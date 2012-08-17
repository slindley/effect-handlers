-- A demonstration of how to simulate McBride handlers using standard
-- effect handlers.

{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction,
             FlexibleContexts, TypeOperators, ScopedTypeVariables,
             GADTs, DataKinds, RankNTypes
 #-}

import Handlers

data Get s = Get
instance Op (Get s) where
  type Param  (Get s) = ()
  type Return (Get s) = s
get = applyOp Get

data Put s = Put
instance Op (Put s) where
  type Param  (Put s) = s
  type Return (Put s) = ()
put = applyOp Put

getClause :: Monad m => OpClause (Get s) (m (s -> m a))
getClause = Get |-> (\() k -> return (\v -> do { f <- k v; f v}))

-- note that because we have access to the continuation we can
-- interpret Put using a type that looks like the type of a reader
-- monad

putClause :: Monad m => OpClause (Put s) (m (s -> a))
putClause = Put |-> (\p k -> do { f <- k (); return (\_ -> f p)})

-- handle state in the standard way
handleState :: Monad m => s -> Comp (Get s, (Put s, ())) a -> m a
handleState = handleStateWith Empty

-- The handleStateWith function generalises handleState to support
-- horizontal composition, either for throwing other effects or for
-- composing with compatible effects such as random choice.
handleStateWith :: (Get s `NotIn` e, Put s `NotIn` e, Monad m) =>
                     OpHandler e (m (s -> m a)) -> s -> Comp (Get s, (Put s, e)) a -> m a
handleStateWith h s comp =
  do
    f <-
      (handle comp
       (getClause :<: putClause :<: h,
        \s -> return (\_ -> return s)))
    f s

-- We simulate a McBride handler of type: Comp e a -> b using a
-- standard effect handler of type: Comp e a -> Mode -> Comp e b,
-- where the mode is used to switch between handling operations
-- immediately and forwarding them to an outer handler.
    
data Mode = Handle | Forward

dynamicMcBrideState' :: Int -> Comp (Get Int, (Put Int, ())) a -> Mode -> Comp (Get Int, (Put Int, ())) a
dynamicMcBrideState' (s :: Int) comp =
  handle comp
  (((Get :: Get Int) |-> (\() k -> \mode ->
    case mode of
      Handle ->
        dynamicMcBrideState' s (k s Forward) Handle
      Forward ->
        do {(s :: Int) <- get (); k s Forward})) :<:
   (Put |-> (\s k -> \mode ->
    case mode of
      Handle ->
        dynamicMcBrideState' s (k () Forward) Handle
      Forward ->
        do {put s; k () Forward})) :<: Empty,
   \x mode -> return x)

-- In handle mode, the result must be a returned value, which we
-- can extract.
dynamicMcBrideState :: Int -> Comp (Get Int, (Put Int, ())) a -> a
dynamicMcBrideState s comp =
  case dynamicMcBrideState' s comp Handle of
    Ret v -> v
    _     -> undefined

-- In general in a non-recursive simply-typed setting we can simulate
-- a McBride handler of type:
--
-- Comp e a -> b
--
-- using a function of type:
--
-- Comp e a -> Maybe b
--
-- The general transformation is local - i.e. McBride handlers are
-- macro-expressible in terms of standard effect handlers.
--
-- If we add recursion then we can get rid of the Maybe - the
-- impossible case returns a non-terminating function of type b.
    

-- Using dependent types we can statically guarantee that handle mode
-- yields a returned value.
data ModeProxy :: Mode -> * where
  H :: ModeProxy Handle
  F :: ModeProxy Forward

-- In handle mode the result is a value. In forward mode it is a
-- computation.
data ModeResult e a :: Mode -> * where
  Handled   :: a ->        ModeResult e a Handle
  Forwarded :: Comp e a -> ModeResult e a Forward
unHandled   (Handled v)   = v
unForwarded (Forwarded c) = c

-- GHC doesn't really cope with unboxed polymorphism.
newtype Poly e a = Poly {unPoly :: forall (mode :: Mode).ModeProxy mode -> ModeResult e a mode} 

mcbrideState :: Int -> Comp (Get Int, (Put Int, ())) a -> a
mcbrideState s comp =
  unHandled (unPoly (mcbrideState' s comp) H)

mcbrideState' :: Int -> Comp (Get Int, (Put Int, ())) a -> Poly (Get Int, (Put Int, ())) a
mcbrideState' s comp =
  handle comp
  ((Get |-> (\() k ->
              Poly (\mode -> 
                     case mode of
                       H ->
                         unPoly (mcbrideState' s (unForwarded (unPoly (k s) F))) H
                       F ->
                         Forwarded $ do {(s :: Int) <- get (); unForwarded $ unPoly (k s) F}))) :<:
   (Put |-> (\s k ->
              Poly (\mode ->
                     case mode of
                       H ->
                         unPoly (mcbrideState' s (unForwarded (unPoly (k ()) F))) H
                       F ->
                         Forwarded $ do {put s; unForwarded $ unPoly (k ()) F}))) :<: Empty,
   \x -> Poly (\mode ->
                case mode of
                  H -> Handled   $ x
                  F -> Forwarded $ return x))

count :: Comp (Get Int, (Put Int, ())) ()
count =
    do {n <- get ();
        if n == (0 :: Int) then return ()
        else do {put (n-1); count}}

-- The simulation is rather inefficient. The n-th operation
-- application is forwarded by n-1 handlers.
