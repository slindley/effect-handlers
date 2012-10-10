{- Parameterised open handlers -}

{-# LANGUAGE TypeFamilies,
    MultiParamTypeClasses, FlexibleInstances,
    TypeOperators, ScopedTypeVariables,
    NoMonomorphismRestriction #-}

module ParameterisedOpenHandlers where

-- Operations live in the Op type class.
--   Param is the parameter type of the operation.
--   Return is the return type of the operation.
class Op op where
  type Param op :: *
  type Return op :: *

class Handler h where
  type Result h :: *
  type Inner h :: *
  ret :: h -> Inner h -> Result h

class (Op op, Handler h) => Handles h op where
  clause :: op -> h -> Param op -> (h -> Return op -> Result h) -> Result h

data Comp h a = Comp {unComp :: h -> (h -> a -> Result h) -> Result h}

instance Monad (Comp h) where
  return v     = Comp (\h k -> k h v)
  Comp c >>= f = Comp (\h k -> c h (\h' x -> unComp (f x) h' k))

instance Functor (Comp e) where
  fmap f c = c >>= return . f

applyOp :: (h `Handles` op) => op -> Param op -> Comp h (Return op)
applyOp m p = Comp (\h k -> clause m h p k)

handle :: (Handler h) => Comp h (Inner h) -> h -> Result h
handle (Comp c) h = c h ret

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

data StateHandler s a = StateHandler s
instance Handler (StateHandler s a) where
  type Result (StateHandler s a) = a
  type Inner (StateHandler s a)  = a
  ret _ x = x

instance (StateHandler s a `Handles` Put s) where
  clause _ _ s k = k (StateHandler s) ()

instance (StateHandler s a `Handles` Get s) where
  clause _ (StateHandler s) () k = k (StateHandler s) s

count =
    do {n <- get ();
        if n == (0 :: Int) then return ()
        else do {put (n-1); count}}
