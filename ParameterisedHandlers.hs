-- Parameterised effect handlers

-- This is an implementation of a variant of effect handlers in which
-- handlers are parameterised. The continuation in the body of an
-- operation clause accepts a value of the parameter type, allowing
-- the parameter to be varied when handling operations in the
-- continuation.
--
-- Parameterised effect handlers are very similar in use to recursive
-- effect handlers. It is straightforward to simulate a parameterised
-- effect handler with a recursive effect handler and vice-versa.
--
-- Clearly standard effect handlers can be simulated with
-- parameterised effect handlers by setting the parameter to be unit.
--
-- Parameterised effect handlers can be simulated with standard effect
-- handlers by internalising the parameter.

{-# LANGUAGE GADTs, TypeFamilies,
    MultiParamTypeClasses,FlexibleInstances,
    OverlappingInstances, FlexibleContexts,
    NoMonomorphismRestriction, TypeOperators #-}

module ParameterisedHandlers where

import TypeNeq ((:=/=:))

-- Operations live in the Op type class.
--   Param is the parameter type of the operation.
--   Return is the return type of the operation.
class Op op where
  type Param op :: *
  type Return op :: *

-- Each instance of Op should be a singleton type whose inhabitant
-- acts as a proxy for the type.

-- An effect e is a heterogeneous list, that is tuple, of operation
-- types.

-- a type class for effect non-membership
class Op op => op `NotIn` e where  
instance Op op => op `NotIn` ()
instance (op :=/=: op', op `NotIn` e) => op `NotIn` (op', e)

-- a witness to the proof that op is in e
data Witness op e where
  Here  :: Witness op (op, e)
  There :: Witness op e -> Witness op (op', e)

-- We could implement this kind of hack to make error messages
-- slightly more illuminating.
--
-- class Error x
-- data OpNotFound op e
-- data OpFound op e
--
-- instance (Error (OpFound op (op, e)), Op op) => op `NotIn` (op, e)
-- instance (Error (OpNotFound op e), op `NotIn` e, Op op) => op `In` e where
--   makeWitness = undefined

-- a type class for effect membership
-- that can construct membership witnesses
class Op op => op `In` e where
  makeWitness :: Witness op e
instance (Op op, op `NotIn` e) => op `In` (op, e) where
  makeWitness = Here
instance (op :=/=: op', op `In` e) => op `In` (op', e) where
  makeWitness = There makeWitness

-- Computations of type a
--   Ret v:      return value v
--   Op w m p k: operation with witness w, name m, parameter p, continuation k
data Comp e a :: * where
  Ret :: a -> Comp e a
  App :: Witness op e -> op -> Param op ->
          (Return op -> Comp e a) -> Comp e a

instance Monad (Comp e) where
  return = Ret
  (Ret v)        >>= k = k v
  (App w m p k') >>= k = App w m p (\v -> k' v >>= k)

instance Functor (Comp e) where
  fmap f c = c >>= return . f

-- direct style operation application
applyOp :: (op `In` e) => op -> Param op -> Comp e (Return op)
applyOp m p = App makeWitness m p return

-- the first component of OpClause is redundant
-- but it eases type inference and makes the connection
-- with the operational semantics blindingly obvious
type OpClause op a p = (op, OpAbs op a p)
type RetClause a b = a -> b

type OpAbs op a p = Param op -> (p -> Return op -> a) -> a

(|->) :: Op op => op -> OpAbs op a p -> OpClause op a p
(|->) = (,)
infix 2 |-> 

infixr 1 :<:
-- An op handler represents a collection of operation clauses.
data OpHandler e a p where
  Empty :: OpHandler () a p
  (:<:) :: (op `NotIn` e) => OpClause op a p -> OpHandler e a p -> OpHandler (op, e) a p

type Handler a e b p = (OpHandler e b p, RetClause a b)

-- handleOp w p k h
--
--   handle the operation at the position in op handler h denoted by
--   the witness w with parameter p and continuation k
handleOp :: Witness op e -> OpHandler e a p -> OpAbs op a p
handleOp Here      ((_, f) :<: _) = f
handleOp (There w) (_ :<: h)      = handleOp w h

handle :: p -> Comp e a -> Handler a e b p -> b
handle p (Ret v)       (h, r) = r v
handle p (App w _ v k) (h, r) = handleOp w h v k'
  where k' p v = handle p (k v) (h, r)

-- an operation clause that throws op
throw :: (op `In` e) => op -> p -> OpClause op (Comp e a) p
throw m p = (m, \v k -> App makeWitness m v (k p))

infixr 1 -:<:
-- m -:<: h
--
--   extends h by throwing the effect e to be handled by an outer
--   handler
--
-- (op is a singleton type and m is its instance)
(-:<:) :: (op `NotIn` e, op `In` e') =>
            (op, p) -> OpHandler e (Comp e' a) p -> OpHandler (op, e) (Comp e' a) p
(m, p) -:<: h = throw m p :<: h
