> {-# LANGUAGE FlexibleContexts #-}

> module MRI_code.Effects where
>
> import Control.Monad.State hiding (evalState)
> import Control.Monad.Identity
> import MRI_code.Advice hiding (fib2)
> import Data.Map (Map, empty, member, (!), insert)

MEMO EXAMPLE

> memo :: MonadState (Map Int Int) m => Open (Int -> m Int) 
> memo super x =  do  m <- get
>                     if member x m  then return (m ! x)
>                                    else do  y <- super x
>                                             m' <- get
>                                             put (insert x y m')
>                                             return y
>
> fib2 :: Monad m => Open (Int -> m Int)
> fib2 this n = case n of  0 -> return 0
>                          1 -> return 1
>                          _ -> do  y <- this (n-1)
>                                   x <- this (n-2) 
>                                   return (x+y)

> slowfib2 :: Int -> Int
> slowfib2 = runIdentity . new fib2


> evalState :: State s a -> s -> a
> evalState m s = fst $ runState m s
>
> fastfib :: Int -> Int
> fastfib n = evalState (new (memo <@> fib2) n) empty
