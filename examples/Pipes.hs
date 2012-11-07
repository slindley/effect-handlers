{-# LANGUAGE GADTs, TypeFamilies, NoMonomorphismRestriction, RankNTypes,
    MultiParamTypeClasses, FlexibleInstances, OverlappingInstances,
    FlexibleContexts, TypeOperators, ScopedTypeVariables, BangPatterns, UndecidableInstances,
    TemplateHaskell, QuasiQuotes
  #-}

import Control.Monad

import Handlers
import DesugarHandlers

[operation|exists s.Await :: s|]
[operation|exists s.Yield :: s -> ()|]

type Pipe i o h a   = ((h `MonoHandles` Await) i, (h `MonoHandles` Yield) o) => Comp h a
type Consumer i h a = (h `MonoHandles` Await) i => Comp h a
type Producer o h a = (h `MonoHandles` Yield) o => Comp h a

data Prod h s a = Prod (() -> Cons h s a -> Comp h a)
data Cons h s a = Cons (s  -> Prod h s a -> Comp h a)

data Down h s a = Down (Prod h s a)
type instance Result (Down h s a) = Comp h a
instance (Down h s a `MonoHandles` Await) s where
  monoClause Await k (Down (Prod prod)) = prod () (Cons (\s p -> k s (Down p)))

instance (h `Handles` op) => Down h s a `Handles` op where
  clause     op k h = doOp     op >>= (\x -> k x h)
instance (h `MonoHandles` op) t => (Down h s a `MonoHandles` op) t where
  monoClause op k h = monoDoOp op >>= (\x -> k x h)
instance (h `PolyHandles` op)   => Down h s a `PolyHandles` op where
  polyClause op k h = polyDoOp op >>= (\x -> k x h)
down prod d = handle d (\x _ -> return x) (Down prod)

data Up h s a = Up (Cons h s a)
type instance Result (Up h s a) = Comp h a
instance (Up h s a `MonoHandles` Yield) s where
  monoClause (Yield s) k (Up (Cons cons)) = cons s (Prod (\() c -> k () (Up c)))

instance (h `Handles` op) => Up h s a `Handles` op where
  clause     op k h = doOp     op >>= (\x -> k x h)
instance (h `MonoHandles` op) t => (Up h s a `MonoHandles` op) t where
  monoClause op k h = monoDoOp op >>= (\x -> k x h)
instance (h `PolyHandles` op)   => Up h s a `PolyHandles` op where
  polyClause op k h = polyDoOp op >>= (\x -> k x h)
up cons u = handle u (\x _ -> return x) (Up cons)
  
--(<+<) :: Comp (Down h s a) a -> Comp (Up h s a) a -> a
(<+<) :: Consumer s (Down h s a) a -> Producer s (Up h s a) a -> Comp h a
d <+< u = down (Prod (\() cons -> up cons u)) d

(>+>) = flip (<+<)

fromList :: [a] -> Producer a h ()
fromList = mapM_ yield

take' :: (h `Handles` PutString) => Int -> Pipe a a h ()
take' n =
  do
    replicateM_ n $ do
      x <- await
      yield x
    putString "You shall not pass!"

[operation|PutString :: String -> ()|]
instance IOHandler a `Handles` PutString where
  clause (PutString s) k h =
    do
      putStrLn s
      k () h

printer :: (h `Handles` PutString) => Consumer Int h r
printer =
  forever $ do
    x <- await
    putString (show x)

pipeline :: (h `Handles` PutString) => Comp h ()
pipeline = printer <+< take' 3 <+< fromList [(1::Int)..]

