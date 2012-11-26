{- shallow codensity handlers -}

{-# LANGUAGE TypeFamilies, RankNTypes,
    MultiParamTypeClasses, FlexibleContexts,
    TypeOperators, GADTs
  #-}

module ShallowCodensityHandlers where

type family Return op :: *
type family Result h :: *
type family Inner h :: *     

-- To achieve adequate performance it seems essential to have the
-- continuation return a RawComp and expose handle'.
class Handles h op where
  clause :: op -> (Return op -> RawComp h (Inner h)) -> h -> Result h

newtype Comp h a = Comp {unComp :: forall r.(a -> RawComp h r) -> RawComp h r}
data RawComp h a where
  Ret :: a -> RawComp h a
  Do  :: (h `Handles` op) => op -> (Return op -> RawComp h a) -> RawComp h a
instance Monad (RawComp h) where
  return        = Ret
  Ret v   >>= f = f v
  Do op k >>= f = Do op (\x -> k x >>= f)
instance Functor (RawComp h) where
  fmap f c = c >>= \x -> return (f x)

instance Monad (Comp h) where
  return v     = Comp (\k -> k v)
  Comp c >>= f = Comp (\k -> c (\x -> unComp (f x) k))
instance Functor (Comp h) where
  fmap f c = c >>= \x -> return (f x)

lift :: RawComp h a -> Comp h a
lift rawComp = Comp (\k -> rawComp >>= k)

lower :: Comp h a -> RawComp h a
lower comp = unComp comp return

doOp :: (h `Handles` op) => op -> Comp h (Return op)
doOp op = Comp (\k -> Do op k)

handle :: Comp h (Inner h) -> (Inner h -> h -> Result h) -> h -> Result h
handle comp = handle' (lower comp)

handle' :: RawComp h (Inner h) -> (Inner h -> h -> Result h) -> h -> Result h
handle' (Ret v)   r h = r v h
handle' (Do op k) r h = clause op k h

-- pure handlers
data PureHandler a = PureHandler
type instance Result (PureHandler a) = a
type instance Inner (PureHandler a) = a

handlePure :: Comp (PureHandler a) a -> a
handlePure comp = handle comp (\x _ -> x) PureHandler

data IOHandler a = IOHandler
type instance Result (IOHandler a) = IO a
type instance Inner (IOHandler a) = a

handleIO :: Comp (IOHandler a) a -> IO a
handleIO comp = handle comp (\x _ -> return x) IOHandler 

