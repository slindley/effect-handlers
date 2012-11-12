{- Fully general open handlers making essential use of DataKinds -}

{-# LANGUAGE TypeFamilies,
    MultiParamTypeClasses,
    GADTs,
    TypeOperators,
    RankNTypes,
    FunctionalDependencies,
    TypeSynonymInstances,
    FlexibleInstances,
    FlexibleContexts,
    ScopedTypeVariables,
    DataKinds,
    PolyKinds
  #-}

module PolyHandlers where

import DesugarHandlers

type family Return (opApp :: *) :: *
type family Result (h :: *) :: *
class ((h :: *) `Handles` (op :: j -> k -> *)) (e :: j) | h op -> e where
  clause :: op e u -> (Return (op e u) -> h -> Result h) -> h -> Result h
newtype Comp h a = Comp {handle :: (a -> h -> Result h) -> h -> Result h}
doOp :: (h `Handles` op) e => op e u -> Comp h (Return (op e u))
doOp op = Comp (\k h -> clause op k h)
-- doOp op = Comp (\k -> clause op k)
-- doOp op = Comp (clause op)
-- doOp    = Comp . clause
-- We are careful not to use this equivalent implementation because it
-- leads to an enormous slow-down. Pointless programming in GHC is
-- dangerous!
--
-- doOp = Comp . clause

instance Monad (Comp h) where
  return v     = Comp (\k h -> k v h)
  Comp c >>= f = Comp (\k h -> c (\x h' -> handle (f x) k h') h)

instance Functor (Comp h) where
  fmap f c = c >>= \x -> return (f x)


-- pure handlers
data PureHandler a = PureHandler
type instance Result (PureHandler a) = a

handlePure :: Comp (PureHandler a) a -> a
handlePure comp = handle comp (\x _ -> x) PureHandler

data IOHandler a = IOHandler
type instance Result (IOHandler a) = IO a

handleIO :: Comp (IOHandler a) a -> IO a
handleIO comp = handle comp (\x _ -> return x) IOHandler 

data Get (s :: *) (t :: ()) where
  Get :: Get s '()
type instance Return (Get s '()) = s
get :: ((h `Handles` Get) s) => Comp h s
get = doOp Get

data Put (s :: *) (t :: ()) where
  Put :: s -> Put s '()
type instance Return (Put s '()) = ()
put :: ((h `Handles` Put) s) => s -> Comp h ()
put s = doOp (Put s)

-- [handles| h {Get s, Put s}|]

--type SComp s a = ((h `Handles` Get) s, (h `Handles` Put) s) => Comp h a
--type SComp s a = (Handles h Get s, Handles h Put s) => Comp h a
type SComp s a = ([handles|h {Get s}|], [handles|h {Put s}|]) => Comp h a

-- unfortunately this doesn't work...  We have a choice of parsing a
-- type or a declaration. A single constraint is a type,
-- but a collection of constraints is a predicate.

-- type SComp s a = ([handles|h {Get s, Put s}|]) => Comp h a

newtype StateHandler (s :: *) (a :: *) = StateHandler s
type instance Result (StateHandler s a) = a
instance ((StateHandler s a `Handles` Get) s) where
  clause Get k (StateHandler s) = k s (StateHandler s)
instance ((StateHandler s a `Handles` Put) s) where
  clause (Put s) k _ = k () (StateHandler s)

countTest :: () -> SComp Int ()
countTest () =
    do {n <- get;
        if n == 0 then return ()
        else do {put (n-1); countTest ()}}
