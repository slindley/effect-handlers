{- Parameterised open McBride handlers -}

{-# LANGUAGE TypeFamilies,
    MultiParamTypeClasses,
    TypeOperators,
    NoMonomorphismRestriction #-}

module OpenHandlers where

type family Return op :: *
type family Result h :: *

class Handles h op where
  clause :: h -> op -> (Return op -> Comp h (Result h)) -> Result h

newtype Comp h a = Comp {handle :: h -> (h -> a -> Result h) -> Result h}

instance Monad (Comp h) where
  return v     = Comp (\h k -> k h v)
  Comp c >>= f = Comp (\h k -> c h (\h' x -> handle (f x) h' k))

instance Functor (Comp h) where
  fmap f c = c >>= return . f

doOp :: (h `Handles` op) => op -> Comp h (Return op)
doOp op = Comp (\h k -> clause h op (\x -> return (k h x)))

forward :: (h `Handles` op) => h' -> op -> (h' -> Return op -> Comp h a) -> Comp h a
forward h op k = doOp op >>= k h

-- polymorphic operations
class (h `PolyHandles` op) where
  polyClause :: h -> op a -> (h -> Return (op a) -> Comp h (Result h)) -> Result h

polyDoOp :: (h `PolyHandles` op) => op a -> Comp h (Return (op a))
polyDoOp op = Comp (\h k -> polyClause h op (\h x -> return (k h x)))

-- pure handlers
data PureHandler a = PureHandler
type instance Result (PureHandler a) = a

handlePure :: Comp (PureHandler a) a -> a
handlePure c = handle c PureHandler (const id)

data Get s = Get
type instance Return (Get s) = s
get = doOp Get

newtype Put s = Put s
type instance Return (Put s) = ()
put s = doOp (Put s)

newtype StateHandler s a = StateHandler s
type instance Result (StateHandler s a) = a
instance (StateHandler s a `Handles` Put s) where
  clause h (Put s) k = handleState s (k ())
instance (StateHandler s a `Handles` Get s) where
  clause (StateHandler s) Get k = handleState s (k s)
handleState s comp = handle comp (StateHandler s) (const id)


countTest =
    do {n <- get;
        if n == (0 :: Int) then return ()
        else do {put (n-1); countTest}}
