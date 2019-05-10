{-# language GADTs, ScopedTypeVariables, RankNTypes #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language DataKinds, PolyKinds, UnboxedTuples, UndecidableInstances #-}
{-# language TypeApplications #-}
module Adapton
  ( runA, runAIO
    -- * Thunks
  , Thunk, thunk, force
    -- * Refs
  , Ref, ref, getRef, setRef
    -- * AVars
  , AVar, avar, getAVar, setAVar
  )
where

import Control.Concurrent.Supply (Supply, newSupply, freshId)
import Control.Monad ((<=<), when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Fix (MonadFix, mfix)
import Control.Monad.Primitive (PrimMonad, PrimBase, PrimState, RealWorld, liftPrim)
import Control.Monad.Reader (ReaderT, runReaderT, asks)
import Control.Monad.ST (ST, runST)
import Data.Set (Set)
import Data.Foldable (traverse_)
import Data.Functor.Classes (Eq1(..), Ord1(..))
import Data.Hashable (Hashable(..), hash)
import Data.HashTable.ST.Basic (HashTable)
import Data.Primitive.MutVar (MutVar, newMutVar, readMutVar, writeMutVar, modifyMutVar)

import qualified Data.HashTable.ST.Basic as HashTable
import qualified Data.Set as Set

data SomeThunk m where
  SomeThunk :: Thunk m a -> SomeThunk m
instance Eq (SomeThunk m) where
  SomeThunk a == SomeThunk b = liftEq undefined a b
instance Ord (SomeThunk m)  where
  compare (SomeThunk a) (SomeThunk b) = liftCompare undefined a b

-- | `U a`
data Thunk m a
  = Thunk
  { _id :: Int
  , _thunk :: A m a
  , _result :: MutVar (PrimState m) a
  , _sub :: MutVar (PrimState m) (Set (SomeThunk m))
  , _super :: MutVar (PrimState m) (Set (SomeThunk m))
  , _clean :: MutVar (PrimState m) Bool
  }

instance Hashable (Thunk m a) where
  hash = _id
  hashWithSalt a = hashWithSalt a . _id

data Env m
  = Env
  { _supply :: MutVar (PrimState m) Supply
  , _current :: MutVar (PrimState m) (Maybe (SomeThunk m))
  }

instance Eq (Thunk m a) where; a == b = _id a == _id b
instance Eq1 (Thunk m) where; liftEq _ a b = _id a == _id b
instance Ord (Thunk m a) where
  compare a b = compare (_id a) (_id b)
instance Ord1 (Thunk m) where
  liftCompare _ a b = compare (_id a) (_id b)

newtype A m a = A { unA :: ReaderT (Env m) m a }
  deriving (Functor, Applicative, Monad, PrimMonad, MonadFix)

fresh :: PrimMonad m => MutVar (PrimState m) Supply -> m Int
fresh ref = do
  a <- readMutVar ref
  let (n, a') = freshId a
  n <$ writeMutVar ref a'

thunk ::
  forall m a.
  PrimBase m =>
  A m a ->
  A m (Thunk m a)
thunk a = do
  supplyRef <- A $ asks _supply
  n <- A . liftPrim @m $ fresh supplyRef
  resultRef <- A . liftPrim @m $ newMutVar undefined
  subRef <- A . liftPrim @m $ newMutVar mempty
  superRef <- A . liftPrim @m $ newMutVar mempty
  cleanRef <- A . liftPrim @m $ newMutVar False
  pure $
    Thunk
    { _id = n
    , _thunk = a
    , _result = resultRef
    , _sub = subRef
    , _super = superRef
    , _clean = cleanRef
    }

addDcgEdge :: forall m a b. PrimBase m => Thunk m a -> Thunk m b -> A m ()
addDcgEdge super sub = do
  liftPrim @m . modifyMutVar (_sub super) $ Set.insert (SomeThunk sub)
  liftPrim @m . modifyMutVar (_super sub) $ Set.insert (SomeThunk super)

delDcgEdge :: forall m a b. PrimBase m => Thunk m a -> Thunk m b -> A m ()
delDcgEdge super sub = do
  liftPrim @m . modifyMutVar (_sub super) $ Set.delete (SomeThunk sub)
  liftPrim @m . modifyMutVar (_super sub) $ Set.delete (SomeThunk super)

compute :: forall m a. PrimBase m => Thunk m a -> A m a
compute a = do
  b <- liftPrim @m $ readMutVar (_clean a)
  if b
    then liftPrim @m $ readMutVar (_result a)
    else do
      traverse_ (\(SomeThunk b) -> delDcgEdge a b) =<< liftPrim @m (readMutVar $ _sub a)
      liftPrim @m $ writeMutVar (_clean a) True
      liftPrim @m . writeMutVar (_result a) =<< _thunk a
      compute a

dirty :: forall m a. PrimBase m => Thunk m a -> A m ()
dirty a = do
  b <- liftPrim @m . readMutVar $ _clean a
  when b $ do
    liftPrim @m $ writeMutVar (_clean a) False
    traverse_ (\(SomeThunk x) -> dirty x) =<< liftPrim @m (readMutVar $ _super a)

-- | `M a`
newtype Ref m a = Ref { unRef :: Thunk m a }
instance Eq (Ref m a) where; Ref a == Ref b = a == b
instance Hashable (Ref m a) where; hash = hash . unRef; hashWithSalt a = hashWithSalt a . unRef

ref :: forall m a. PrimBase m => a -> A m (Ref m a)
ref val = do
  supplyRef <- A $ asks _supply
  n <- liftPrim @m $ fresh supplyRef
  resultRef <- liftPrim @m $ newMutVar val
  subRef <- liftPrim @m $ newMutVar mempty
  superRef <- liftPrim @m $ newMutVar mempty
  cleanRef <- liftPrim @m $ newMutVar True
  let
    a =
      Thunk
      { _id = n
      , _thunk = liftPrim @m $ readMutVar resultRef
      , _result = resultRef
      , _sub = subRef
      , _super = superRef
      , _clean = cleanRef
      }
  pure $ Ref a

setRef :: forall m a. PrimBase m => Ref m a -> a -> A m ()
setRef (Ref a) val = do
  liftPrim @m $ writeMutVar (_result a) val
  dirty a

getRef :: PrimBase m => Ref m a -> A m a
getRef (Ref a) = force a

force :: forall m a. PrimBase m => Thunk m a -> A m a
force a = do
  current <- A $ asks _current
  prev <- liftPrim @m $ readMutVar current
  liftPrim @m $ writeMutVar current $ Just (SomeThunk a)
  result <- compute a
  liftPrim @m $ writeMutVar current prev
  result <$ traverse_ (\(SomeThunk x) -> addDcgEdge x a) prev

memoL ::
  forall m a b.
  ( Eq a, Hashable a
  , PrimBase m
  ) =>
  (a -> A m b) ->
  A m (a -> A m (Thunk m b))
memoL f = do
  table :: HashTable (PrimState m) a (Thunk s b) <- liftPrim HashTable.new
  s <- A $ asks _supply
  pure $ \x -> do
    res <- liftPrim $ HashTable.lookup table x
    case res of
      Nothing -> do
        a :: Thunk m b <- thunk (f x)
        a <$ liftPrim (HashTable.insert table x a)
      Just a -> pure a

memo :: forall s m a b. (Eq a, Hashable a, PrimBase m) => (a -> A m b) -> A m (a -> A m b)
memo f = (force <=<) <$> memoL f

memoFix ::
  (Eq a, Hashable a, PrimBase m, MonadFix m) =>
  ((a -> A m b) -> a -> A m b) ->
  A m (a -> A m b)
memoFix f = mfix (memo . f)

newtype AVar m a = AVar { unAVar :: Ref m (Thunk m a) }
instance Eq (AVar m a) where; AVar a == AVar b = a == b
instance Hashable (AVar m a) where; hash = hash . unAVar; hashWithSalt a = hashWithSalt a . unAVar

avar :: PrimBase m => A m a -> A m (AVar m a)
avar a = fmap AVar . ref =<< thunk a

getAVar :: PrimBase m => AVar m a -> A m a
getAVar (AVar (Ref a)) = force =<< force a

setAVar :: PrimBase m => AVar m a -> A m a -> A m ()
setAVar (AVar v) a = setRef v =<< thunk a

setup :: PrimBase m => Supply -> m (Env m)
setup sup = do
  supRef <- newMutVar sup
  curRef <- newMutVar Nothing
  pure $ Env supRef curRef

runA :: PrimBase m => Supply -> A m a -> m a
runA sup a = setup sup >>= runReaderT (unA a)

runAIO :: A IO a -> IO a
runAIO a = do
  sup <- newSupply
  setup sup >>= runReaderT (unA a)
