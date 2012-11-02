{- Parameterised open handlers as a continuation monad -}

{-# LANGUAGE TypeFamilies,
    MultiParamTypeClasses,
    TypeOperators,
    NoMonomorphismRestriction  
  #-}

module Handlers where

type family Return op :: *
type family Result h :: *
class h `Handles` op where
  clause :: op -> (Return op -> h -> Result h) -> h -> Result h
-- The type Comp h a is isomorphic to Cont (h -> Result h) -> h. We
-- don't actually use Cont as the extra abstraction leads to a
-- significant performance penalty.
newtype Comp h a = Comp {handle :: (a -> h -> Result h) -> h -> Result h}
doOp :: (h `Handles` op) => op -> Comp h (Return op)
doOp op = Comp (\k h -> clause op k h)
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

-- polymorphic operations
class h `PolyHandles` op where polyClause :: op a -> (Return (op a) -> h -> Result h) -> h -> Result h
polyDoOp :: (h `PolyHandles` op) => op a -> Comp h (Return (op a))
polyDoOp op = Comp (\k h -> polyClause op k h)

-- pure handlers
data PureHandler a = PureHandler
type instance Result (PureHandler a) = a

handlePure :: Comp (PureHandler a) a -> a
handlePure comp = handle comp (\x _ -> x) PureHandler

data IOHandler a = IOHandler
type instance Result (IOHandler a) = IO a

handleIO :: Comp (IOHandler a) a -> IO a
handleIO comp = handle comp (\x _ -> return x) IOHandler 

data Get s = Get
type instance Return (Get s) = s
get = doOp Get

newtype Put s = Put s
type instance Return (Put s) = ()
put s = doOp (Put s)

newtype StateHandler s a = StateHandler s
type instance Result (StateHandler s a) = a
instance (StateHandler s a `Handles` Get s) where
  clause Get k (StateHandler s) = k s (StateHandler s)
instance (StateHandler s a `Handles` Put s) where
  clause (Put s) k _ = k () (StateHandler s)

countTest =
    do {n <- get;
        if n == (0 :: Int) then return ()
        else do {put (n-1); countTest}}
