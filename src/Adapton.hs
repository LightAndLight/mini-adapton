{-# language GADTs, RecursiveDo #-}
module Adapton where

import Control.Concurrent.Supply (Supply, freshId)
import Control.Monad (when)
import Control.Monad.ST (ST)
import Data.Set (Set)
import Data.Foldable (traverse_)
import Data.Functor.Classes (Eq1(..), Ord1(..))
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef)

import qualified Data.Set as Set

data SomeAdapton s where
  SomeAdapton :: Adapton s a -> SomeAdapton s
instance Eq (SomeAdapton s) where
  SomeAdapton a == SomeAdapton b = liftEq undefined a b
instance Ord (SomeAdapton s) where
  compare (SomeAdapton a) (SomeAdapton b) = liftCompare undefined a b

data Adapton s a
  = Adapton
  { _id :: Int
  , _thunk :: ST s a
  , _result :: STRef s a
  , _sub :: STRef s (Set (SomeAdapton s))
  , _super :: STRef s (Set (SomeAdapton s))
  , _clean :: STRef s Bool
  }

instance Eq (Adapton s a) where; a == b = _id a == _id b
instance Eq1 (Adapton s) where; liftEq _ a b = _id a == _id b
instance Ord (Adapton s a) where
  compare a b = compare (_id a) (_id b)
instance Ord1 (Adapton s) where
  liftCompare _ a b = compare (_id a) (_id b)

fresh :: STRef s Supply -> ST s Int
fresh ref = do
  a <- readSTRef ref
  let (n, a') = freshId a
  n <$ writeSTRef ref a'

mkAdapton :: STRef s Supply -> ST s a -> ST s (Adapton s a)
mkAdapton supplyRef a = do
  n <- fresh supplyRef
  resultRef <- newSTRef undefined
  subRef <- newSTRef mempty
  superRef <- newSTRef mempty
  cleanRef <- newSTRef False
  pure $
    Adapton
    { _id = n
    , _thunk = a
    , _result = resultRef
    , _sub = subRef
    , _super = superRef
    , _clean = cleanRef
    }

addDcgEdge :: Adapton s a -> Adapton s b -> ST s ()
addDcgEdge super sub = do
  modifySTRef (_sub super) $ Set.insert (SomeAdapton sub)
  modifySTRef (_super sub) $ Set.insert (SomeAdapton super)

delDcgEdge :: Adapton s a -> Adapton s b -> ST s ()
delDcgEdge super sub = do
  modifySTRef (_sub super) $ Set.delete (SomeAdapton sub)
  modifySTRef (_super sub) $ Set.delete (SomeAdapton super)

compute :: Adapton s a -> ST s a
compute a = do
  b <- readSTRef (_clean a)
  if b
    then readSTRef (_result a)
    else do
      traverse_ (\(SomeAdapton b) -> delDcgEdge a b) =<< readSTRef (_sub a)
      writeSTRef (_clean a) True
      writeSTRef (_result a) =<< _thunk a
      compute a

dirty :: Adapton s a -> ST s ()
dirty a = do
  b <- readSTRef $ _clean a
  when b $ do
    writeSTRef (_clean a) False
    traverse_ (\(SomeAdapton x) -> dirty x) =<< readSTRef (_super a)

newtype Ref s a = Ref { unRef :: Adapton s a }

ref :: STRef s Supply -> a -> ST s (Ref s a)
ref supplyRef val = do
  n <- fresh supplyRef
  resultRef <- newSTRef val
  subRef <- newSTRef mempty
  superRef <- newSTRef mempty
  cleanRef <- newSTRef True
  let
    a =
      Adapton
      { _id = n
      , _thunk = readSTRef resultRef
      , _result = resultRef
      , _sub = subRef
      , _super = superRef
      , _clean = cleanRef
      }
  pure $ Ref a

setRef :: Ref s a -> a -> ST s ()
setRef (Ref a) val = do
  writeSTRef (_result a) val
  dirty a

force :: STRef s (Maybe (SomeAdapton s)) -> Adapton s a -> ST s a
force current a = do
  prev <- readSTRef current
  writeSTRef current $ Just (SomeAdapton a)
  result <- compute a
  writeSTRef current prev
  result <$ traverse_ (\(SomeAdapton x) -> addDcgEdge x a) prev