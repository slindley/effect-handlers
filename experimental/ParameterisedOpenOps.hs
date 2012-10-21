{- Parameterised open handlers with parameterised operations -}

{-# LANGUAGE TypeFamilies,
    MultiParamTypeClasses, FlexibleInstances,
    TypeOperators, ScopedTypeVariables,
    NoMonomorphismRestriction #-}

module ParameterisedOpenOps where

-- Operations live in the Op type class.
--   Return is the return type of the operation.
--   Any parameters should be attached to instances of Op.
class Op op where
  type Return op :: *

class Handler h where
  type Result h :: *
  type Inner h :: *
  ret :: h -> Inner h -> Result h

class (Op op, Handler h) => Handles h op where
  clause :: h -> op -> (h -> Return op -> Result h) -> Result h

data Comp h a = Comp {unComp :: h -> (h -> a -> Result h) -> Result h}

instance Monad (Comp h) where
  return v     = Comp (\h k -> k h v)
  Comp c >>= f = Comp (\h k -> c h (\h' x -> unComp (f x) h' k))

instance Functor (Comp h) where
  fmap f c = c >>= return . f

doOp :: (h `Handles` op) => op -> Comp h (Return op)
doOp op = Comp (\h k -> clause h op k)

handle :: (Handler h) => Comp h (Inner h) -> h -> Result h
handle (Comp c) h = c h ret

data Get s = Get
instance Op (Get s) where
  type Return (Get s) = s
get = doOp Get

data Put s = Put s
instance Op (Put s) where
  type Return (Put s) = ()
put s = doOp (Put s)

data StateHandler s a = StateHandler s
instance Handler (StateHandler s a) where
  type Result (StateHandler s a) = a
  type Inner (StateHandler s a)  = a
  ret _ x = x

instance (StateHandler s a `Handles` Put s) where
  clause _ (Put s) k = k (StateHandler s) ()

instance (StateHandler s a `Handles` Get s) where
  clause (StateHandler s) Get k = k (StateHandler s) s

count =
    do {n <- get;
        if n == (0 :: Int) then return ()
        else do {put (n-1); count}}
