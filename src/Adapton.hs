{-# language GADTs, RecursiveDo, ScopedTypeVariables, RankNTypes #-}
module Adapton where

import Control.Concurrent.Supply (Supply, freshId)
import Control.Monad (when)
import Data.Set (Set)
import Data.Foldable (traverse_)
import Data.Functor.Classes (Eq1(..), Ord1(..))
import Data.Hashable (Hashable, hash)
import Data.HashTable.IO (BasicHashTable)
import Data.IORef (IORef, newIORef, readIORef, writeIORef, modifyIORef)

import GHC.Exts (Any)
import Unsafe.Coerce (unsafeCoerce)

import qualified Data.HashTable.IO as HashTable
import qualified Data.Set as Set

data SomeAdapton where
  SomeAdapton :: Adapton a -> SomeAdapton
instance Eq SomeAdapton where
  SomeAdapton a == SomeAdapton b = liftEq undefined a b
instance Ord SomeAdapton where
  compare (SomeAdapton a) (SomeAdapton b) = liftCompare undefined a b

data Adapton a
  = Adapton
  { _id :: Int
  , _thunk :: IO a
  , _result :: IORef a
  , _sub :: IORef (Set SomeAdapton)
  , _super :: IORef (Set SomeAdapton)
  , _clean :: IORef Bool
  }

instance Eq (Adapton a) where; a == b = _id a == _id b
instance Eq1 Adapton where; liftEq _ a b = _id a == _id b
instance Ord (Adapton a) where
  compare a b = compare (_id a) (_id b)
instance Ord1 Adapton where
  liftCompare _ a b = compare (_id a) (_id b)

fresh :: IORef Supply -> IO Int
fresh ref = do
  a <- readIORef ref
  let (n, a') = freshId a
  n <$ writeIORef ref a'

mkAdapton :: IORef Supply -> IO a -> IO (Adapton a)
mkAdapton supplyRef a = do
  n <- fresh supplyRef
  resultRef <- newIORef undefined
  subRef <- newIORef mempty
  superRef <- newIORef mempty
  cleanRef <- newIORef False
  pure $
    Adapton
    { _id = n
    , _thunk = a
    , _result = resultRef
    , _sub = subRef
    , _super = superRef
    , _clean = cleanRef
    }

addDcgEdge :: Adapton a -> Adapton b -> IO ()
addDcgEdge super sub = do
  modifyIORef (_sub super) $ Set.insert (SomeAdapton sub)
  modifyIORef (_super sub) $ Set.insert (SomeAdapton super)

delDcgEdge :: Adapton a -> Adapton b -> IO ()
delDcgEdge super sub = do
  modifyIORef (_sub super) $ Set.delete (SomeAdapton sub)
  modifyIORef (_super sub) $ Set.delete (SomeAdapton super)

compute :: Adapton a -> IO a
compute a = do
  b <- readIORef (_clean a)
  if b
    then readIORef (_result a)
    else do
      traverse_ (\(SomeAdapton b) -> delDcgEdge a b) =<< readIORef (_sub a)
      writeIORef (_clean a) True
      writeIORef (_result a) =<< _thunk a
      compute a

dirty :: Adapton a -> IO ()
dirty a = do
  b <- readIORef $ _clean a
  when b $ do
    writeIORef (_clean a) False
    traverse_ (\(SomeAdapton x) -> dirty x) =<< readIORef (_super a)

newtype Ref a = Ref { unRef :: Adapton a }

ref :: IORef Supply -> a -> IO (Ref a)
ref supplyRef val = do
  n <- fresh supplyRef
  resultRef <- newIORef val
  subRef <- newIORef mempty
  superRef <- newIORef mempty
  cleanRef <- newIORef True
  let
    a =
      Adapton
      { _id = n
      , _thunk = readIORef resultRef
      , _result = resultRef
      , _sub = subRef
      , _super = superRef
      , _clean = cleanRef
      }
  pure $ Ref a

setRef :: Ref a -> a -> IO ()
setRef (Ref a) val = do
  writeIORef (_result a) val
  dirty a

force :: IORef (Maybe SomeAdapton) -> Adapton a -> IO a
force current a = do
  prev <- readIORef current
  writeIORef current $ Just (SomeAdapton a)
  result <- compute a
  writeIORef current prev
  result <$ traverse_ (\(SomeAdapton x) -> addDcgEdge x a) prev

memoizeLM ::
  forall a b.
  Hashable a =>
  BasicHashTable Int Any ->
  IORef Supply ->
  (a -> IO b) ->
  a -> IO (Adapton b)
memoizeLM table s f x = do
  let h = hash x
  res <- HashTable.lookup table h
  case res of
    Nothing -> do
      a :: Adapton b <- mkAdapton s (f x)
      a <$ HashTable.insert table h (unsafeCoerce a :: Any)
    Just a -> pure (unsafeCoerce a :: Adapton b)

mapAdapton ::
  Hashable a =>
  BasicHashTable Int Any ->
  IORef Supply ->
  IORef (Maybe SomeAdapton) ->
  (a -> IO b) ->
  Adapton a ->
  IO (Adapton b)
mapAdapton ht sup cur f a = force cur a >>= memoizeLM ht sup f

memoizeM ::
  forall s a b.
  Hashable a =>
  BasicHashTable Int Any ->
  IORef Supply ->
  IORef (Maybe SomeAdapton) ->
  (a -> IO b) ->
  a -> IO b
memoizeM table s cur f x = force cur =<< memoizeLM table s f x

newtype AVar s a = AVar { unAVar :: Ref (Adapton a) }

avar :: IORef Supply -> IO a -> IO (AVar s a)
avar sup a = fmap AVar . ref sup =<< mkAdapton sup a

avarGet :: IORef (Maybe SomeAdapton) -> AVar s a -> IO a
avarGet cur (AVar (Ref a)) = force cur =<< force cur a

avarSet :: IORef Supply -> AVar s a -> IO a -> IO ()
avarSet sup (AVar v) a = setRef v =<< mkAdapton sup a

setup :: Supply -> IO (IORef Supply, IORef (Maybe SomeAdapton), BasicHashTable Int Any)
setup sup = do
  supRef <- newIORef sup
  ht <- HashTable.new
  curRef <- newIORef Nothing
  pure (supRef, curRef, ht)