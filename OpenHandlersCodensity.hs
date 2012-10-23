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
  clause :: h -> op -> (h -> Return op -> Result h) -> Result h

newtype Comp e a = Comp {unComp :: forall r . (a -> RawComp e r) -> RawComp e r}
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
  Comp c >>= f = Comp (\k' -> c (\x -> unComp (f x) k'))
instance Functor (Comp h) where
  fmap f c = c >>= return . f

doOp :: (h `Handles` op) => op -> Comp h (Return op)
doOp op = Comp (\k -> Do op k)

handle :: Comp h a -> h -> (h -> a -> Result h) -> Result h
handle (Comp c) = handle' (c return)
  where
    handle' :: RawComp h a -> h -> (h -> a -> Result h) -> Result h
    handle' (Ret v) h r = r h v
    handle' (Do op k) h r = clause h op (\h' v -> handle' (k v) h' r)

forward :: (Handles h op) => h' -> op -> (h' -> Return op -> Comp h a) -> Comp h a
forward h op k = doOp op >>= k h
  
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
instance (StateHandler s a `Handles` Get s) where
  clause (StateHandler s) Get k = k (StateHandler s) s
instance (StateHandler s a `Handles` Put s) where
  clause _ (Put s) k = k (StateHandler s) ()

countTest =
    do {n <- get;
        if n == (0 :: Int) then return ()
        else do {put (n-1); countTest}}
