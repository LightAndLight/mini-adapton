{-# language GADTs, ScopedTypeVariables, RankNTypes #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language RoleAnnotations #-}
{-# language RecursiveDo #-}
module Adapton where

import Control.Concurrent.Supply (Supply, newSupply, freshId)
import Control.Monad ((<=<), when)
import Control.Monad.Fix (MonadFix)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (ReaderT, runReaderT, asks)
import Data.Set (Set)
import Data.Foldable (traverse_)
import Data.Functor.Classes (Eq1(..), Ord1(..))
import Data.Hashable (Hashable(..), hash)
import Data.HashTable.IO (BasicHashTable)
import Data.IORef (IORef, newIORef, readIORef, writeIORef, modifyIORef)

import qualified Data.HashTable.IO as HashTable
import qualified Data.Set as Set

data SomeAThunk s where
  SomeAThunk :: AThunk s a -> SomeAThunk s
instance Eq (SomeAThunk s) where
  SomeAThunk a == SomeAThunk b = liftEq undefined a b
instance Ord (SomeAThunk s)  where
  compare (SomeAThunk a) (SomeAThunk b) = liftCompare undefined a b

data AThunk s a
  = AThunk
  { _id :: Int
  , _thunk :: A s a
  , _result :: IORef a
  , _sub :: IORef (Set (SomeAThunk s))
  , _super :: IORef (Set (SomeAThunk s))
  , _clean :: IORef Bool
  }
type role AThunk nominal nominal

instance Hashable (AThunk s a) where
  hash = _id
  hashWithSalt a = hashWithSalt a . _id

data Env s
  = Env
  { _supply :: IORef Supply
  , _current :: IORef (Maybe (SomeAThunk s))
  }

instance Eq (AThunk s a) where; a == b = _id a == _id b
instance Eq1 (AThunk s) where; liftEq _ a b = _id a == _id b
instance Ord (AThunk s a) where
  compare a b = compare (_id a) (_id b)
instance Ord1 (AThunk s) where
  liftCompare _ a b = compare (_id a) (_id b)

newtype A s a = A { unA :: ReaderT (Env s) IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFix)
type role A nominal nominal

fresh :: IORef Supply -> IO Int
fresh ref = do
  a <- readIORef ref
  let (n, a') = freshId a
  n <$ writeIORef ref a'

mkAThunk :: A s a -> A s (AThunk s a)
mkAThunk a = do
  supplyRef <- A $ asks _supply
  n <- A . liftIO $ fresh supplyRef
  resultRef <- A . liftIO $ newIORef undefined
  subRef <- A . liftIO $ newIORef mempty
  superRef <- A . liftIO $ newIORef mempty
  cleanRef <- A . liftIO $ newIORef False
  pure $
    AThunk
    { _id = n
    , _thunk = a
    , _result = resultRef
    , _sub = subRef
    , _super = superRef
    , _clean = cleanRef
    }

addDcgEdge :: AThunk s a -> AThunk s b -> A s ()
addDcgEdge super sub = do
  liftIO . modifyIORef (_sub super) $ Set.insert (SomeAThunk sub)
  liftIO . modifyIORef (_super sub) $ Set.insert (SomeAThunk super)

delDcgEdge :: AThunk s a -> AThunk s b -> A s ()
delDcgEdge super sub = do
  liftIO . modifyIORef (_sub super) $ Set.delete (SomeAThunk sub)
  liftIO . modifyIORef (_super sub) $ Set.delete (SomeAThunk super)

compute :: AThunk s a -> A s a
compute a = do
  b <- liftIO $ readIORef (_clean a)
  if b
    then liftIO $ readIORef (_result a)
    else do
      traverse_ (\(SomeAThunk b) -> delDcgEdge a b) =<< liftIO (readIORef $ _sub a)
      liftIO $ writeIORef (_clean a) True
      liftIO . writeIORef (_result a) =<< _thunk a
      compute a

dirty :: AThunk s a -> A s ()
dirty a = do
  b <- liftIO . readIORef $ _clean a
  when b $ do
    liftIO $ writeIORef (_clean a) False
    traverse_ (\(SomeAThunk x) -> dirty x) =<< liftIO (readIORef $ _super a)

newtype Ref s a = Ref { unRef :: AThunk s a }
instance Eq (Ref s a) where; Ref a == Ref b = a == b
instance Hashable (Ref s a) where; hash = hash . unRef; hashWithSalt a = hashWithSalt a . unRef

ref :: a -> A s (Ref s a)
ref val = do
  supplyRef <- A $ asks _supply
  n <- liftIO $ fresh supplyRef
  resultRef <- liftIO $ newIORef val
  subRef <- liftIO $ newIORef mempty
  superRef <- liftIO $ newIORef mempty
  cleanRef <- liftIO $ newIORef True
  let
    a =
      AThunk
      { _id = n
      , _thunk = liftIO $ readIORef resultRef
      , _result = resultRef
      , _sub = subRef
      , _super = superRef
      , _clean = cleanRef
      }
  pure $ Ref a

setRef :: Ref s a -> a -> A s ()
setRef (Ref a) val = do
  liftIO $ writeIORef (_result a) val
  dirty a

force :: AThunk s a -> A s a
force a = do
  current <- A $ asks _current
  prev <- liftIO $ readIORef current
  liftIO $ writeIORef current $ Just (SomeAThunk a)
  result <- compute a
  liftIO $ writeIORef current prev
  result <$ traverse_ (\(SomeAThunk x) -> addDcgEdge x a) prev

memoL ::
  forall s a b.
  (Eq a, Hashable a) =>
  (a -> A s b) ->
  A s (a -> A s (AThunk s b))
memoL f = do
  table :: BasicHashTable a (AThunk s b) <- liftIO HashTable.new
  s <- A $ asks _supply
  pure $ \x -> do
    res <- liftIO $ HashTable.lookup table x
    case res of
      Nothing -> do
        a :: AThunk s b <- mkAThunk (f x)
        a <$ liftIO (HashTable.insert table x a)
      Just a -> pure a

memo :: forall s a b. (Eq a, Hashable a) => (a -> A s b) -> A s (a -> A s b)
memo f = (force <=<) <$> memoL f

memoFix :: (Eq a, Hashable a) => ((a -> A s b) -> a -> A s b) -> A s (a -> A s b)
memoFix f = do
  rec f' <- memo (f f')
  pure f'

newtype AVar s a = AVar { unAVar :: Ref s (AThunk s a) }
instance Eq (AVar s a) where; AVar a == AVar b = a == b
instance Hashable (AVar s a) where; hash = hash . unAVar; hashWithSalt a = hashWithSalt a . unAVar

avar :: A s a -> A s (AVar s a)
avar a = fmap AVar . ref =<< mkAThunk a

avarGet :: AVar s a -> A s a
avarGet (AVar (Ref a)) = force =<< force a

avarSet :: AVar s a -> A s a -> A s ()
avarSet (AVar v) a = setRef v =<< mkAThunk a

setup :: Supply -> IO (Env s)
setup sup = do
  supRef <- newIORef sup
  curRef <- newIORef Nothing
  pure $ Env supRef curRef

runA :: (forall s. A s a) -> IO a
runA a = do
  sup <- newSupply
  setup sup >>= runReaderT (unA a)


prog1 :: IO ()
prog1 =
  runA $ do
    v1 <- avar $ pure 2
    v2 <- avar $ (+4) <$> avarGet v1
    b <- avar $ (+) <$> avarGet v1 <*> avarGet v2
    liftIO . print =<< avarGet b
    avarSet v1 $ pure 10
    liftIO . print =<< avarGet b

data Tree f a
  = Tip a
  | Bin (f (Tree f a)) (f (Tree f a))

right :: Tree f a -> f (Tree f a)
right (Bin _ a) = a
right Tip{} = undefined

prog2 :: IO ()
prog2 = runA go
  where
    go :: forall s. A s ()
    go = do
      maxTree :: AVar s (Tree (AVar s) Int) -> A s Int <-
        memoFix $ \recur a -> do
          a' <- avarGet a
          liftIO . putStrLn $ "computing maxTree"
          case a' of
            Tip x -> pure x
            Bin x y -> max <$> recur x <*> recur y

      maxTreePath :: AVar s (Tree (AVar s) Int) -> A s [Bool] <-
        memoFix $ \recur a -> do
          liftIO . putStrLn $ "computing maxTreePath"
          a' <- avarGet a
          case a' of
            Tip x -> pure []
            Bin x y -> do
              x' <- maxTree x
              y' <- maxTree y
              if x' > y'
                then (False :) <$> recur x
                else (True :) <$> recur y

      t1 <- avar $ Bin <$> avar (pure $ Tip (1::Int)) <*> avar (pure $ Tip 2)
      t2 <- avar $ Bin <$> avar (pure $ Tip 3) <*> avar (pure $ Tip 4)
      tree <- avar $ pure (Bin t1 t2)

      liftIO . print =<< maxTree tree
      liftIO . print =<< maxTreePath tree

      avarSet t2 $ pure (Tip 5)
      liftIO . print =<< maxTree tree
      liftIO . print =<< maxTreePath tree

      liftIO . print =<< maxTree =<< fmap right (avarGet tree)
      liftIO . print =<< maxTreePath =<< fmap right (avarGet tree)
