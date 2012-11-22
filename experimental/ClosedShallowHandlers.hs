----- McBride handlers -----

-- This is an implementation of a variant of handlers in which
-- continuation applications inside an operation clause are *not*
-- wrapped in the handler to which the operation clause belongs.

-- For common use-cases, such as iteratees, they require the handler
-- to be explicitly invoked recursively. Standard effect handlers, in
-- contrast, build in a particular kind of recursion in that
-- continuation applications inside an operation clause are
-- automatically wrapped in the handler.
--
-- Conor McBride's Frank implements McBride handlers:
--
--   http://hackage.haskell.org/package/Frank
--
-- McBride handlers are convenient for threading state through a
-- computation: the state is encoded as a parameter to the handler.
--
-- Standard handlers are often more convenient in the absence of such
-- state, as it is not necessary to explicitly handle continuation
-- applications.
--
-- McBride handlers are to control0/prompt0 as standard effect
-- handlers are to shift0/reset0.
--
-- See Ken Shan's paper 'A static simulation of dynamic delimited control':
--
--   http://www.cs.rutgers.edu/~ccshan/recur/recur-hosc-final.pdf
--
-- and Oleg Kiselyov's 'How to remove a dynamic prompt: static and
-- dynamic delimited continuation operators are equally expressible':
--
--   http://www.cs.indiana.edu/pub/techreports/TR611.pdf
--
-- It might be interesting to define versions of handlers
-- corresponding to the shift/reset and control/prompt continuation
-- operators. It isn't yet clear to me whether or not they would be
-- useful. It would seem to amount to interpretting an algebraic
-- computation as another computation with the same effects - the
-- handler would automatically be wrapped around the body of all of
-- its operation clauses.

{-# LANGUAGE GADTs, TypeFamilies,
    MultiParamTypeClasses, FlexibleInstances,
    OverlappingInstances, FlexibleContexts,
    TypeOperators #-}

module McBrideHandlers where

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
type OpClause op a b = (op, OpAbs op a b)
type RetClause a b = a -> b
 
type OpAbs op a b = Param op -> (Return op -> a) -> b

(|->) :: op -> OpAbs op a b -> OpClause op a b
(|->) = (,)
infix 2 |-> 

infixr 1 :<:
-- An op handler represents a collection of operation clauses.
data OpHandler e a b where
  Empty :: OpHandler () a b
  (:<:) :: (op `NotIn` e) => OpClause op a b -> OpHandler e a b -> OpHandler (op, e) a b

type Handler a e b = (OpHandler e (Comp e a) b, RetClause a b)

-- handleOp w p k h
--
--   handle the operation at the position in op handler h denoted by
----   the witness w with parameter p and continuation k
handleOp :: Witness op e -> OpHandler e a b -> OpAbs op a b
handleOp Here      ((_, f) :<: _) = f
handleOp (There w) (_ :<: h)      = handleOp w h

handle :: Comp e a -> Handler a e b -> b
handle (Ret v)       (h, r) = r v
handle (App w _ p k) (h, r) = handleOp w h p k

-- an operation clause that throws op
throw :: (op `In` e) => op -> OpClause op (Comp e a) (Comp e a)
throw m = (m, App makeWitness m)

infixr 1 -:<:
-- m -:<: h
--
--   extends h by throwing the effect e to be handled by an outer
--   handler
--
-- (op is a singleton type and m is its instance)
(-:<:) :: (op `NotIn` e, op `NotIn` e') =>
            op -> OpHandler e       (Comp (op, e') a) (Comp (op, e') a)
               -> OpHandler (op, e) (Comp (op, e') a) (Comp (op, e') a)
m -:<: h = throw m :<: h
