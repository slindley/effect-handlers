{- This code illustrates how the continuation monad can be used to
   implement standard handlers over a free-monad via a Church
   encoding. -}

{-# LANGUAGE TypeFamilies,
    GADTs,
    RankNTypes,
    MultiParamTypeClasses,
    FlexibleContexts,
    TypeOperators
 #-}

module Cont where

import Control.Monad.Cont
import DesugarHandlers

-- We start with a free monad for state
data DataState a =
    RetDS a
  | GetDS ()  (Int -> DataState a)
  | PutDS Int (()  -> DataState a)

instance Monad DataState where
  return = RetDS
  RetDS v >>= f = f v
  GetDS () k >>= f = GetDS () (\x -> k x >>= f)
  PutDS s  k >>= f = PutDS s  (\x -> k x >>= f)

getDS :: () -> DataState Int
getDS () = GetDS () return

putDS :: Int -> DataState ()
putDS s  = PutDS s return


-- Now we turn it into a continuation monad:
--   forall r.ContState r a is the Church encoding of DataState
--   (Cont r a ~= (a -> r) -> r)
type ContState r a = Cont ((() -> (Int -> r) -> r) ->   -- get :: () -> Int
                           (Int -> (() -> r) -> r) ->   -- put :: Int -> ()
                           r) a

getCont :: () -> ContState r Int
getCont () = cont (\k get put -> get () (\s -> k s get put))

putCont :: Int -> ContState r ()
putCont s = cont (\k get put -> put s (\() -> k () get put))

-- A handler for DataState takes a return clause and a clause for each
-- operation (get and put).
handleDataState :: DataState a -> (a -> r) -> (() -> (Int -> r) -> r) -> (Int -> (() -> r) -> r) -> r
handleDataState (RetDS v)    ret get put = ret v
handleDataState (GetDS () k) ret get put = get () (\x -> handleDataState (k x) ret get put) 
handleDataState (PutDS s  k) ret get put = put s  (\x -> handleDataState (k x) ret get put)


-- A handler for a continuation computation is just a function that
-- instantiates the return type with a concrete type.
handleCont :: Cont r a -> (a -> r) -> r
handleCont = runCont

-- In particular, a handler for a state computation instantiates the
-- return type to accept get and put clauses.
--
-- Note that in order to be a continuation monad we must thread these
-- clauses through the return clause. This is essential for
-- composability - we need it in order to define bind.
--
-- Typically an actual top-level return clause will ignore the put and
-- get arguments.
handleContState :: ContState r a ->
                   (a -> (() -> (Int -> r) -> r) -> (Int -> (() -> r) -> r) -> r) ->  -- return
                   (() -> (Int -> r) -> r) ->                                         -- get
                   (Int -> (() -> r) -> r) ->                                         -- put
                   r
handleContState = handleCont

-- The definitions of equivalent free and continuation-based handlers
-- are now very similar.

simpleStateFree :: Int -> DataState a -> a
simpleStateFree s comp = handleDataState
                         comp
                         (\x    s -> x)       -- return clause
                         (\() k s -> k s s)   -- get clause
                         (\s  k _ -> k () s)  -- put clause
                         s                    -- handler parameter
                      
simpleStateCont :: Int -> ContState (Int -> a) a -> a
simpleStateCont s comp = handleContState
                         comp
                         (\x    get put s -> x)       -- return clause
                         (\() k         s -> k s  s)  -- get clause
                         (\s  k         _ -> k () s)  -- put clause
                         s                            -- handler parameter

-- If we use type-classes to define operation clauses then the result
-- type of the continuation monad becomes much simpler. We need a
-- single handler argument to track the type == name of a handler and
-- any parameters to the handler. All of the concrete operation
-- clauses are inferred by the type class mechanism.
type family Return (op :: *) :: *
type family Result (h :: *) :: *
class (h `Handles` op) where
  clause :: op -> (Return op -> h -> Result h) -> h -> Result h
type Comp h a = Cont (h -> Result h) a 

handle :: Comp h a -> (a -> h -> Result h) -> h -> Result h
handle = handleCont

doOp :: (h `Handles` op) => op -> Comp h (Return op)
doOp op = cont (\k h -> clause op k h)

data Get where
  Get :: Get
type instance Return Get = Int
get :: (h `Handles` Get) => Comp h Int
get = doOp Get

data Put where
  Put :: !Int -> Put
type instance Return Put = ()
put :: (h `Handles` Put) => Int -> Comp h ()
put s = doOp (Put s)

type SComp a = (h `Handles` Get, h `Handles` Put) => Comp h a

newtype SimpleState a = SimpleState Int
type instance Result (SimpleState  a) = a
instance (SimpleState a `Handles` Get) where
  clause Get k (SimpleState s) = k s (SimpleState s)  -- get clause
instance (SimpleState a `Handles` Put) where
  clause (Put s) k _ = k () (SimpleState s)           -- put clause

simpleState :: Int -> SComp a -> a
simpleState s comp = handle
                     comp
                     (\x (SimpleState s) -> x)  -- return
                     (SimpleState s)            -- handler parameter
