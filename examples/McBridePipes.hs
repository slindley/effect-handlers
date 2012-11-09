{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction, RankNTypes,
    MultiParamTypeClasses, FlexibleInstances, OverlappingInstances,
    FlexibleContexts, TypeOperators, UndecidableInstances,
    QuasiQuotes
  #-}

import Control.Monad

import OpenHandlersMcBride

data Await = Await
type instance Return Await = Int
await = doOp Await

newtype Yield = Yield Int
type instance Return Yield = ()
yield s = doOp (Yield s)

-- Comp (Up h a) a           becomes  Prod (Cons r -> r)
-- Int -> Comp (Down h a) a  becomes  Cons (Int -> Prod r -> r)

newtype Down h a = Down (Comp (Up h a) a)
type instance Result (Down h a) = Comp h a
type instance Inner  (Down h a) = a
instance (Down h a `Handles` Await) where
  clause Await k (Down f) = up k f
down f comp = handle comp (\x _ -> return x) (Down f)

instance (h `Handles` op) => Down h a `Handles` op where
  clause op k (Down f) = doOp op >>= (\x -> down f (k x))

newtype Up h a = Up (Int -> Comp (Down h a) a)
type instance Result (Up h a) = Comp h a
type instance Inner  (Up h a) = a
instance (Up h a `Handles` Yield) where
  clause (Yield s) k (Up f) = down (k ()) (f s)
up f comp = handle comp (\x _ -> return x) (Up f)

instance (h `Handles` op) => Up h a `Handles` op where
  clause op k (Up f) = doOp op >>= (\x -> up f (k x))

type Pipe h a     = (h `Handles` Await, h `Handles` Yield) => Comp h a
type Consumer h a = (h `Handles` Await) => Comp h a
type Producer h a = (h `Handles` Yield) => Comp h a

(<+<) :: Consumer (Down h a) a -> Producer (Up h a) a -> Comp h a
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

(>+>) = flip (<+<)

fromList :: [Int] -> Producer h ()
fromList = mapM_ yield

take' :: (h `Handles` PutString) => Int -> Pipe h ()
take' n =
  do
    replicateM_ n $ do
      x <- await
      yield x
    putString "You shall not pass!"

--[operation|PutString :: String -> ()|]
newtype PutString = PutString String
type instance Return PutString = ()
putString s = doOp (PutString s)

instance IOHandler a `Handles` PutString where
  clause (PutString s) k h =
    do
      putStrLn s
      iOHandler (k ())
iOHandler comp = handle comp (\x _ -> return x) IOHandler 

printer :: (h `Handles` PutString) => Consumer h r
printer =
  forever $ do
    x <- await
    putString (show x)

pipeline :: (h `Handles` PutString) => Comp h ()
pipeline = printer <+< take' 3 <+< fromList [1..]

produceFrom :: Int -> Producer h a
produceFrom i =
  do
    yield i
    produceFrom $! i+1

    
count :: Pipe h a
count =
  forever $ do
    _ <- await
    yield 1

sumTo :: Int -> Pipe h ()
sumTo = sumTo' 0
  where
    sumTo' a limit =
      if a >= limit then yield a
      else
        do
          x <- await
          sumTo' (x+a) limit

logger :: Pipe h a
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
