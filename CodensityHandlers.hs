{- Handlers using a free monad and the codensity monad -}

{-# LANGUAGE TypeFamilies,
    MultiParamTypeClasses,
    GADTs,
    TypeOperators,
    RankNTypes,
    FunctionalDependencies,
    PolyKinds
  #-}

module CodensityHandlers where

type family Return (opApp :: *) :: *
type family Result (h :: *) :: *
class ((h :: *) `Handles` (op :: j -> k -> *)) (e :: j) | h op -> e where
  clause :: op e u -> (Return (op e u) -> h -> Result h) -> h -> Result h

newtype Comp h a = Comp {unComp :: forall r . (a -> RawComp h r) -> RawComp h r}
data RawComp h a where
  Ret :: a -> RawComp h a
  Do  :: (h `Handles` op) e => op e u -> (Return (op e u) -> RawComp h a) -> RawComp h a
instance Monad (RawComp h) where
  return        = Ret
  Ret v   >>= f = f v
  Do op k >>= f = Do op (\x -> k x >>= f)

instance Monad (Comp c) where
  return v     = Comp (\k -> k v)
  Comp c >>= f = Comp (\k -> c (\x -> unComp (f x) k))
instance Functor (Comp h) where
  fmap f c = c >>= \x -> return (f x)

doOp :: (h `Handles` op) e => op e u -> Comp h (Return (op e u))
doOp op = Comp (\k -> Do op k)

handle :: Comp h a -> (a -> h -> Result h) -> h -> Result h
handle (Comp c) = handle' (c return)
  where
    handle' :: RawComp h a -> (a -> h -> Result h) -> h -> Result h
    handle' (Ret v) r h = r v h
    handle' (Do op k) r h = clause op (\v h' -> handle' (k v) r h') h
