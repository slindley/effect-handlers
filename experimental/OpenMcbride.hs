{- Open handlers using a free monad
   functors for handler result types -}

{-# LANGUAGE TypeFamilies,
    MultiParamTypeClasses, FlexibleInstances, OverlappingInstances,
    TypeOperators, ScopedTypeVariables, RankNTypes,
    NoMonomorphismRestriction, GADTs #-}

module OpenMcBride where

-- Operations live in the Op type class.
--   Param is the parameter type of the operation.
--   Return is the return type of the operation.
class Op op where
  type Param op :: *
  type Return op :: *

class Handler h where
  type Result h :: * -> *
  ret :: h -> a -> Result h a

class (Op op, Handler h) => Handles h op where
  clause :: op -> h -> Param op -> (Return op -> Comp h a) -> Result h a

data Comp h a where
  Ret :: a -> Comp h a
  App :: (h `Handles` op) => op -> Param op -> (Return op -> Comp h a) -> Comp h a 

instance Monad (Comp h) where
  return = Ret
  (Ret v) >>= k      = k v
  (App m p k') >>= k = App m p (\v -> k' v >>= k)

instance Functor (Comp h) where
  fmap f c = c >>= return . f

applyOp :: (h `Handles` op) => op -> Param op -> Comp h (Return op)
applyOp m p = App m p return

handle :: (Handler h) => Comp h a -> h -> Result h a
handle (Ret v)     h = ret h v
handle (App m p k) h = clause m h p k


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

newtype Id a = Id {unId :: a}

data StateHandler s = StateHandler 
instance Handler (StateHandler s) where
  type Result (StateHandler s) = Id
  ret _ x = Id x

instance (StateHandler s `Handles` Put s) where
  clause m h s k = handle (k ()) h

-- handleState s comp = handle comp StateHandler

-- instance (StateHandler s `Handles` Get s) where
--   clause _ _ _ k = (\s -> k s s)
