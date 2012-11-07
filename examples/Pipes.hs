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

data RunUp h s a = Finished a | Yielding s (Comp h (RunUp h s a))
-- [handler|
--   forward h.Down s a :: Comp h (RunUp h s a) -> a
--     handles {Await s} where
--       Return x   _ -> return x
--       Await    k c ->
--        do
--        res <- c
--        case res of
--           Finished x   -> return x
--           Yielding s c -> k s c
-- |]
data Down h s a = Down (Comp h (RunUp h s a))
type instance Result (Down h s a) = Comp h a
instance (Down h s a `MonoHandles` Await) s where
  monoClause (Await) k (Down c) =
    do
      res <- c
      case res of
        Finished x   -> return x
        Yielding s c -> k s (Down c)
down c comp = handle comp (\x _ -> return x) (Down c)

instance (h `Handles` op) => Down h s a `Handles` op where
  clause op k h = doOp op >>= (\x -> k x h)
instance (h `MonoHandles` op) t => (Down h s a `MonoHandles` op) t where
  monoClause op k h = monoDoOp op >>= (\x -> k x h)
instance (h `PolyHandles` op) => Down h s a `PolyHandles` op where
  polyClause op k h = polyDoOp op >>= (\x -> k x h)


-- [handler|
--   forward h.Up s a :: RunUp h s a
--     handles {Yield s} where
--       Return x   -> return (Finished x)
--       Yield  s k -> return (Yielding s (k ()))
-- |]
data Up h s a = Up
type instance Result (Up h s a) = Comp h (RunUp h s a)
instance (Up h s a `MonoHandles` Yield) s where
  monoClause (Yield s) k h = return (Yielding s (k () h))
up comp = handle comp (\x _ -> return (Finished x)) Up

instance (h `Handles` op) => Up h s a `Handles` op where
  clause op k h = doOp op >>= (\x -> k x h)
instance (h `MonoHandles` op) t => (Up h s a `MonoHandles` op) t where
  monoClause op k h = monoDoOp op >>= (\x -> k x h)
instance (h `PolyHandles` op) => Up h s a `PolyHandles` op where
  polyClause op k h = polyDoOp op >>= (\x -> k x h)

-- Wrong type!
--(<+<) :: Consumer s h a -> Producer s h a -> Comp h a
  
--(<+<) :: Comp (Down h s a) a -> Comp (Up h s a) a -> Comp h a
(<+<) :: Consumer s (Down h s a) a -> Producer s (Up h s a) a -> Comp h a
d <+< u = down (up u) d

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

printer :: (Show a, h `Handles` PutString) => Consumer a h r
printer =
  forever $ do
    x <- await
    putString (show x)

pipeline :: (h `Handles` PutString) => Comp h ()
pipeline = printer <+< take' 3 <+< fromList [1..]

