{- An implementation of part of Gabriel Gonzalez's Pipes library using
shallow handlers. The original library is here:

    http://hackage.haskell.org/package/pipes
 -}


{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction, RankNTypes,
    MultiParamTypeClasses, FlexibleInstances, OverlappingInstances,
    FlexibleContexts, TypeOperators, UndecidableInstances,
    QuasiQuotes, GADTs
  #-}

module Examples.ShallowPipes where

import Control.Monad

import ShallowFreeHandlers
import DesugarHandlers

[operation|Await s :: s|]
[operation|Yield s :: s -> ()|]

-- data Await = Await
-- type instance Return Await = Int
-- await = doOp Await

-- newtype Yield = Yield Int
-- type instance Return Yield = ()
-- yield s = doOp (Yield s)

-- Comp (Up h a) a           becomes  Prod (Cons r -> r)
-- Int -> Comp (Down h a) a  becomes  Cons (Int -> Prod r -> r)
 
[shallowHandler|
  forward h.Down s a :: Comp (Up h s a) a -> a
    handles {Await s} where
      Return x      _      -> return x
      Await     k   prod   -> up k prod |]

[shallowHandler|
  forward h.Up  s a :: (s -> Comp (Down h s a) a) -> a
    handles {Yield s} where
      Return x     _       -> return x
      Yield s   k  cons    -> down (k ()) (cons s) |]


-- newtype Down h a = Down (Comp (Up h a) a)
-- type instance Result (Down h a) = Comp h a
-- type instance Inner  (Down h a) = a
-- instance (Down h a `Handles` Await) () where
--   clause Await k (Down f) = up k f
-- down f comp = handle comp (\x _ -> return x) (Down f)

-- instance (h `Handles` op) () => (Down h a `Handles` op) () where
--   clause op k (Down f) = doOp op >>= (\x -> down f (k x))

-- newtype Up h a = Up (Int -> Comp (Down h a) a)
-- type instance Result (Up h a) = Comp h a
-- type instance Inner  (Up h a) = a
-- instance (Up h a `Handles` Yield) () where
--   clause (Yield s) k (Up f) = down (k ()) (f s)
-- up f comp = handle comp (\x _ -> return x) (Up f)

-- instance (h `Handles` op) () => (Up h a `Handles` op) () where
--   clause op k (Up f) = doOp op >>= (\x -> up f (k x))

type Pipe i o h a     = ([handles|h {Await i}|], [handles|h {Yield o}|]) => Comp h a
type Consumer i h a = [handles|h {Await i}|] => Comp h a
type Producer o h a = [handles|h {Yield o}|] => Comp h a

(<+<) :: Consumer s (Down h s a) a -> Producer s (Up h s a) a -> Comp h a
d <+< u = down u d


-- [operation|exists s.Await :: s|]
-- [operation|exists s.Yield :: s -> ()|]

-- data Prod s r = Prod (() -> Cons s r -> r)
-- data Cons s r = Cons (s  -> Prod s r -> r)

-- [handler|
--   forward h.Down s a :: Prod s (Comp h a) -> a
--     monohandles {Await s} where
--       Await    k (Prod prod) -> prod () (Cons k)
--       Return x   _           -> return x
-- |]
-- [handler|
--   forward h.Up s a :: Cons s (Comp h a) -> a
--     monohandles {Yield s} where
--       Yield s  k (Cons cons) -> cons s (Prod k)
--       Return x   _           -> return x
-- |]

-- (<+<) :: Consumer s (Down h s a) a -> Producer s (Up h s a) a -> Comp h a
-- d <+< u = down (Prod (\() cons -> up cons u)) d


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
[shallowHandler|
  PrintHandler a :: IO a handles {PutString} where
    Return x      -> return x
    PutString s k -> do {putStrLn s; printHandler (k ())}
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
