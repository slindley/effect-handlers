{- Parameterised open handlers with parameterised operations
   (simplified)

   This version has two type families for specifying the return type
   of operations and the result type of handlers. Only one type class
   is declared. Its instances define handler clauses.

   Parameters should be stored in operations and handlers. Thus the
   handler and op arguments to the clause function can be used to
   actually pass parameters, and not just to work around weaknesses in
   type inference. Note that this also means an arbitrary number of
   parameters can be easily attached to an operation or handler

   The return clause is passed in as an argument to the handle
   function.
-}

{-# LANGUAGE TypeFamilies,
    MultiParamTypeClasses,
    TypeOperators,
    NoMonomorphismRestriction #-}

module OpenHandlers where

type family Return op :: *
type family Result h :: *

type Cont h a = h -> a -> Result h

class Handles h op where
  clause :: h -> op -> Cont h (Return op) -> Result h

newtype Comp h a = Comp {unComp :: h -> Cont h a -> Result h}

instance Monad (Comp h) where
  return v     = Comp (\h k -> k h v)
  Comp c >>= f = Comp (\h k -> c h (\h' x -> unComp (f x) h' k))

instance Functor (Comp h) where
  fmap f c = c >>= return . f

doOp :: (h `Handles` op) => op -> Comp h (Return op)
doOp op = Comp (\h k -> clause h op k)

handle :: Comp h a -> h -> Cont h a -> Result h
handle (Comp c) h = c h

data Get s = Get
type instance Return (Get s) = s
get = doOp Get

newtype Put s = Put s
type instance Return (Put s) = ()
put s = doOp (Put s)

newtype StateHandler s a = StateHandler s
type instance Result (StateHandler s a) = a
instance (StateHandler s a `Handles` Get s) where
  clause (StateHandler s) Get k = k (StateHandler s) s
instance (StateHandler s a `Handles` Put s) where
  clause _ (Put s) k = k (StateHandler s) ()

count =
    do {n <- get;
        if n == (0 :: Int) then return ()
        else do {put (n-1); count}}
