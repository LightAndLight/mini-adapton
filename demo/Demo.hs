{-# language ScopedTypeVariables #-}
module Main where

import Control.Monad.Primitive (liftPrim)

import Adapton

prog1 :: IO ()
prog1 =
  runAIO $ do
    v1 <- avar $ pure 2
    v2 <- avar $ (+4) <$> getAVar v1
    b <- avar $ (+) <$> getAVar v1 <*> getAVar v2
    liftPrim . print =<< getAVar b
    setAVar v1 $ pure 10
    liftPrim . print =<< getAVar b

data Tree f a
  = Tip a
  | Bin (f (Tree f a)) (f (Tree f a))

right :: Tree f a -> f (Tree f a)
right (Bin _ a) = a
right Tip{} = undefined

prog2 :: IO ()
prog2 = runAIO go
  where
    go :: A IO ()
    go = do
      maxTree :: AVar IO (Tree (AVar IO) Int) -> A IO Int <-
        memoFix $ \recur a -> do
          a' <- getAVar a
          liftPrim . putStrLn $ "computing maxTree"
          case a' of
            Tip x -> pure x
            Bin x y -> max <$> recur x <*> recur y

      maxTreePath :: AVar IO (Tree (AVar IO) Int) -> A IO [Bool] <-
        memoFix $ \recur a -> do
          liftPrim . putStrLn $ "computing maxTreePath"
          a' <- getAVar a
          case a' of
            Tip x -> pure []
            Bin x y -> do
              x' <- maxTree x
              y' <- maxTree y
              if x' > y'
                then (False :) <$> recur x
                else (True :) <$> recur y

      lucky <- avar $ pure (7::Int)
      t1 <- avar $ Bin <$> avar (pure $ Tip (1::Int)) <*> avar (pure $ Tip 2)
      t2 <- avar $ Bin <$> avar (pure $ Tip 3) <*> avar (pure $ Tip 4)
      tree <- avar $ pure (Bin t1 t2)

      liftPrim . print =<< maxTree tree
      liftPrim . print =<< maxTreePath tree

      setAVar t2 $ pure (Tip 5)
      liftPrim . print =<< maxTree tree
      liftPrim . print =<< maxTreePath tree

      liftPrim . print =<< maxTree =<< fmap right (getAVar tree)
      liftPrim . print =<< maxTreePath =<< fmap right (getAVar tree)

      setAVar t2 $ Bin <$> avar (pure $ Tip 20) <*> avar (Tip . (3*) <$> getAVar lucky)
      liftPrim . print =<< maxTree tree
      liftPrim . print =<< maxTreePath tree

      setAVar lucky $ pure 3
      liftPrim . print =<< maxTree tree
      liftPrim . print =<< maxTreePath tree

main :: IO ()
main = prog2
