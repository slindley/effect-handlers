{-# LANGUAGE TypeFamilies, GADTs, NoMonomorphismRestriction, RankNTypes,
    MultiParamTypeClasses, FlexibleInstances, OverlappingInstances,
    FlexibleContexts, TypeOperators, UndecidableInstances,
    QuasiQuotes, ScopedTypeVariables
  #-}

import Control.Monad

import PolyHandlers
import DesugarPolyHandlers

[operation|Await s :: s|]
[operation|Yield s :: s -> ()|]

type Pipe i o h a   = ((h `Handles` Await) i, (h `Handles` Yield) o) => Comp h a
type Consumer i h a = (h `Handles` Await) i => Comp h a
type Producer o h a = (h `Handles` Yield) o => Comp h a

data Prod s r = Prod (() -> Cons s r -> r)
data Cons s r = Cons (s  -> Prod s r -> r)

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

take' :: ((h `Handles` PutString) ()) => Int -> Pipe a a h ()
take' n =
  do
    replicateM_ n $ do
      x <- await
      yield x
    putString "You shall not pass!"

[operation|PutString :: String -> ()|]
instance (IOHandler a `Handles` PutString) () where
  clause (PutString s) k h =
    do
      putStrLn s
      k () h

printer :: (h `Handles` PutString) () => Consumer Int h r
printer =
  forever $ do
    x <- await
    putString (show x)

pipeline :: (h `Handles` PutString) () => Comp h ()
pipeline = printer <+< take' 3 <+< fromList [(1::Int)..]

produceFrom :: Int -> Producer Int h a
produceFrom i =
  do
    yield i
    produceFrom $! i+1

    
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

test1 = printer <+< sumTo 100000000 <+< count <+< produceFrom 0
test2 = printer <+< sumTo 100000000 <+< count <+< count <+< produceFrom 0
test3 = printer <+< sumTo 100000000 <+< count <+< count <+< count <+< produceFrom 0
test4 = printer <+< sumTo 1000000000 <+< logger <+< produceFrom 0
main = handleIO test1
