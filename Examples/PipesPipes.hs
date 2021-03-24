{- Pipes examples using Gabriel Gonzalez's Pipes library:

    http://hackage.haskell.org/package/pipes
 -}

module Examples.PipesPipes where

import Control.Monad.Identity
import Control.Monad
import Control.Monad.Trans

import Pipes

fromList :: Monad m => [a] -> Producer a m ()
fromList = mapM_ yield

take' :: Int -> Pipe a a IO ()
take' n =
  do
    replicateM_ n $ do
      x <- await
      yield x
    lift $ putStrLn "You shall not pass!"

takePure :: Monad m => Int -> Pipe a a m ()
takePure n =
  do
    replicateM_ n $ do
      x <- await
      yield x


printer :: (Show a) => Consumer a IO r
printer =
  forever $ do
    x <- await
    lift (print x)

--pipeline :: Pipe () C IO ()
pipeline = printer <-< take' 3 <-< fromList [1..]

produceFrom :: (Monad m) => Int -> Producer Int m a
produceFrom i =
  do
    yield i
    produceFrom $! (i+1)

produceFromTo :: (Monad m) => Int -> Int -> Producer Int m ()
produceFromTo i j =
  do
    if i == j then return ()
      else do yield i
              (produceFromTo $! i+1) j


count :: Monad m => Pipe i Int m a
count =
  forever $ do
    _ <- await
    yield 1

    
logger :: Monad m => Pipe Int Int m a
logger =
  forever $ do
    x <- await
    yield (intLog 2 x)
    
intLog :: Int -> Int -> Int
intLog b x = if x < b then 0
             else divide (x `div` b^l) l
               where
                 l = 2 * intLog (b*b) x
                 divide x l = if x < b then l
                              else divide (x `div` b) (l+1)


sumTo :: Monad m => Int -> Pipe Int Int m ()
sumTo = sumTo' 0
  where
    sumTo' a limit =
      if a >= limit then yield a
      else
        do
          x <- await
          sumTo' (x+a) limit
  

expoPipe :: Monad m => Int -> Pipe Int Int m a
expoPipe 0 = forever $ do {x <- await; yield $! x+1}
expoPipe n = expoPipe (n-1) <-< expoPipe (n-1)

blackhole :: Monad m => Consumer a m b
blackhole = forever await

test0 n = blackhole <-< produceFromTo 1 n
test1 = printer <-< sumTo 100000000 <-< count <-< produceFrom 0
test2 = printer <-< sumTo 100000000 <-< count <-< count <-< produceFrom 0
test3 = printer <-< sumTo 100000000 <-< count <-< count <-< count <-< produceFrom 0
test4 = printer <-< sumTo 1000000000 <-< logger <-< produceFrom 0
test5 = printer <-< take' 100 <-< expoPipe 10 <-< produceFrom 0
test6 n = blackhole <-< take' 1000 <-< expoPipe n <-< produceFrom 0
test7 n = blackhole <-< takePure 1000 <-< expoPipe n <-< produceFrom 0

main :: IO ()
main = runEffect (test0 (10^8))

simple :: Int -> Identity ()
simple n = runEffect (test0 n)

nested :: Int -> Identity ()
nested n = runEffect (test7 n)
