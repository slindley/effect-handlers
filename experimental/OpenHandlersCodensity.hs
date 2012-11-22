{- Parameterised open handlers with parameterised operations
   using the codensity monad composed with a free monad.
-}

{-# LANGUAGE TypeFamilies,
    MultiParamTypeClasses,
    TypeOperators, GADTs, RankNTypes,
    NoMonomorphismRestriction #-}

module OpenHandlersCodensity where

type family Return op :: *
type family Result h :: *

class Handles h op where
  clause :: op -> (Return op -> h -> Result h) -> h -> Result h

newtype Comp h a = Comp {unComp :: forall r . (a -> RawComp h r) -> RawComp h r}
data RawComp h a where
  Ret :: a -> RawComp h a
  Do  :: (h `Handles` op) => op -> (Return op -> RawComp h a) -> RawComp h a

instance Monad (RawComp h) where
  return        = Ret
  Ret v >>= f   = f v
  Do op k >>= f = Do op (\x -> k x >>= f)
instance Functor (RawComp h) where
  fmap f c = c >>= return . f
  
instance Monad (Comp c) where
  return v     = Comp (\k -> k v)
  Comp c >>= f = Comp (\k -> c (\x -> unComp (f x) k))
instance Functor (Comp h) where
  fmap f c = c >>= \x -> return (f x)

doOp :: (h `Handles` op) => op -> Comp h (Return op)
doOp op = Comp (\k -> Do op k)

handle :: Comp h a -> (a -> h -> Result h) -> h -> Result h
handle (Comp c) = handle' (c return)
  where
    handle' :: RawComp h a -> (a -> h -> Result h) -> h -> Result h
    handle' (Ret v) r h = r v h
    handle' (Do op k) r h = clause op (\v h' -> handle' (k v) r h') h

forward :: (Handles h op) => op -> (Return op -> h' -> Comp h a) -> h' -> Comp h a
forward op k h = doOp op >>= (\x -> k x h)
  
data PureHandler a = PureHandler
type instance Result (PureHandler a) = a

handlePure :: Comp (PureHandler a) a -> a
handlePure c = handle c (\x _ -> x) PureHandler

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
