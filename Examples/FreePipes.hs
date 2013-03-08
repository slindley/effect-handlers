{- An implementation of part of Gabriel Gonzalez's Pipes library using
free monad handlers. The original library is here:

    http://hackage.haskell.org/package/pipes
 -}

{-# LANGUAGE TypeFamilies, GADTs, NoMonomorphismRestriction, RankNTypes,
    MultiParamTypeClasses, FlexibleInstances, OverlappingInstances,
    FlexibleContexts, UndecidableInstances,
    QuasiQuotes
  #-}

module Examples.FreePipes where

import Control.Monad

import FreeHandlers
import DesugarHandlers

[operation|Await s :: s|]
[operation|Yield s :: s -> ()|]

type Pipe i o h a   = ([handles|h {Await i}|], [handles|h {Yield o}|]) => Comp h a
type Consumer i h a = [handles|h {Await i}|] => Comp h a
type Producer o h a = [handles|h {Yield o}|] => Comp h a

newtype Prod s r = Prod (() -> Cons s r -> r)
newtype Cons s r = Cons (s  -> Prod s r -> r)

[handler|
  forward h.Down s a :: Prod s (Comp h a) -> a
    handles {Await s} where
      Await    k (Prod prod) -> prod () (Cons k)
      Return x   _           -> return x
|]
[handler|
  forward h.Up s a :: Cons s (Comp h a) -> a
    handles {Yield s} where
      Yield s  k (Cons cons) -> cons s (Prod k)
      Return x   _           -> return x
|]

(<+<) :: Consumer s (Down h s a) a -> Producer s (Up h s a) a -> Comp h a
d <+< u = down (Prod (\() cons -> up cons u)) d

(>+>) = flip (<+<)

fromList :: [a] -> Producer a h ()
fromList = mapM_ yield

take' :: [handles|h {PutString}|] => Int -> Pipe a a h ()
take' n =
  do
    replicateM_ n $ do
      x <- await
      yield x
    putString "You shall not pass!"

takePure :: Int -> Pipe a a h ()
takePure n =
  do
    replicateM_ n $ do
      x <- await
      yield x


[operation|PutString :: String -> ()|]
[handler|
  PrintHandler a :: IO a handles {PutString} where
    Return x      -> return x
    PutString s k -> do {putStrLn s; k ()}
|]

printer :: [handles|h {PutString}|] => Consumer Int h r
printer =
  forever $ do
    x <- await
    putString (show x)

pipeline :: [handles|h {PutString}|] => Comp h ()
pipeline = printer <+< take' 3 <+< fromList [(1::Int)..]

produceFrom :: Int -> Producer Int h a
produceFrom i =
  do
    yield i
    produceFrom $! i+1

produceFromTo :: Int -> Int -> Producer Int h ()
produceFromTo i j =
  do
    if i == j then return ()
      else do yield i
              (produceFromTo $! i+1) j


    
count :: Pipe i Int h a
count =
  forever $ do
    _ <- await
    yield 1

sumTo :: Int -> Pipe Int Int h ()
sumTo = sumTo' 0
  where
    sumTo' a limit =
      if a >= limit then yield a
      else
        do
          x <- await
          sumTo' (x+a) limit

logger :: Pipe Int Int h a
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

expoPipe :: Int -> Pipe Int Int h a
expoPipe 0 = forever $ do {x <- await; yield $! x+1}
expoPipe n = expoPipe (n-1) <+< expoPipe (n-1)

blackhole :: Consumer a h b
blackhole = forever await


test0 n = blackhole <+< produceFromTo 1 n
test1 = printer <+< sumTo 100000000 <+< count <+< produceFrom 0
test2 = printer <+< sumTo 100000000 <+< count <+< count <+< produceFrom 0
test3 = printer <+< sumTo 100000000 <+< count <+< count <+< count <+< produceFrom 0
test4 = printer <+< sumTo 1000000000 <+< logger <+< produceFrom 0
test5 = printer <+< take' 100 <+< expoPipe 10 <+< produceFrom 0
test6 n = blackhole <+< take' 1000 <+< expoPipe n <+< produceFrom 0
test7 n = blackhole <+< takePure 1000 <+< expoPipe n <+< produceFrom 0

simple = test0
nested = test7
