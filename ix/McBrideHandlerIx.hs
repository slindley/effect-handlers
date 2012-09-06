{-# LANGUAGE GADTs, TypeFamilies,
    MultiParamTypeClasses,FlexibleInstances,
    OverlappingInstances, FlexibleContexts,
    TypeOperators, 
    PolyKinds, DataKinds, RankNTypes, ImpredicativeTypes,
    NoMonomorphismRestriction, KindSignatures,
    UndecidableInstances,
    ScopedTypeVariables
  #-}

module Handlers where

import Control.Exception (catch, IOException)
import System.IO

import TypeNeqIx ((:=/=:))

import FunctorIx
import MonadIx

-- Operations live in the Op type class.
--   Param is the parameter type of the operation.
--   Return is the return type of the operation.
class Op op where
  type Param op :: i -> *
  type Return op :: i -> *

-- Each instance of Op should be a singleton type whose inhabitant
-- acts as a proxy for the type.

-- An effect e is a heterogeneous list, that is tuple, of operation
-- types.

-- a type class for effect non-membership
class op `NotIn` e where  
instance op `NotIn` ()
instance (op :=/=: op', op `NotIn` e) => op `NotIn` (op', e)

-- a witness to the proof that op is in e
data Witness op e where
  Here  :: Witness op (op, e)
  There :: Witness op e -> Witness op (op', e)

-- a type class for effect membership
-- that can construct membership witnesses
class op `In` e where
  makeWitness :: Witness op e
instance (op `NotIn` e) => op `In` (op, e) where
  makeWitness = Here
instance (op :=/=: op', op `In` e) => op `In` (op', e) where
  makeWitness = There makeWitness

-- Computations of type a
--   Ret v:      return value v
--   Op w m p k: operation with witness w, name m, parameter p, continuation k
data Comp e (a :: (i -> *)) :: (i -> *) where
  Ret :: a i -> Comp e a i
  App :: Witness op e -> op -> Param op pre ->
           (Return op :-> Comp e a) -> Comp e a pre

instance MonadIx (Comp e) where
  returnIx = Ret
  extendIx k (Ret v)        = k v 
  extendIx k (App w m p k') = App w m p (\v -> k' v ?>= k)

instance FunctorIx (Comp e) where
  mapIx f c = c ?>= (returnIx . f)

instance ApplicativeP (Comp e) where
  pure      = returnP
  mf |*| ms = mf =>= \f -> ms =>= \s -> returnP (f s)

-- direct style operation application
applyOp :: (op `In` e) => op -> Param op i -> Comp e (Return op) i
applyOp m p = App makeWitness m p returnIx

-- We use the Plain newtype for representing non-dependent result
-- types. This is just an instance of the K combinator.
newtype Plain (a :: *) (i :: k) = Plain {unPlain :: a}

-- operation clause with a dependent result type
infix 2 |-> 
(|->) :: op -> OpAbsRaw op m a b post -> OpClause op m a b post
m |-> c = (m, OpAbs c)

-- operation clause with a non-dependent result type
infix 2 |=>
(|=>) :: op -> OpAbsPlainResult op m a b post -> OpClause op m a (Plain b) post
m |=> c = (m, OpAbs (\p k -> Plain (c p k)))

type OpClause op (m :: (k -> *) -> (k -> *)) a (b :: k -> *) (post :: k) =
  (op, OpAbs op m a b post)

-- GHC can't cope if this polymorphism isn't wrapped in a newtype
newtype OpAbs op (m :: (k -> *) -> (k -> *)) a (b :: k -> *) (post :: k) =
  OpAbs {unOpAbs :: OpAbsRaw op m a b post}

type OpAbsRaw op (m :: (k -> *) -> (k -> *)) a (b :: k -> *) (post :: k) =
  (forall (pre :: k).Param op pre -> (Return op :-> m (a := post)) -> b pre)

type OpAbsPlainResult op (m :: (k -> *) -> (k -> *)) a b (post :: k) =
  (forall (pre :: k).Param op pre -> (Return op :-> m (a := post)) -> b)

type RetClause a b = a -> b

infixr 1 :<:
-- An op handler represents a collection of operation clauses.
data OpHandler e (m :: (k -> *) -> (k -> *)) a (b :: k -> *) (post :: k) where
  Empty :: OpHandler () m a b post
  (:<:) :: (op `NotIn` e) =>
            OpClause op m a b (post :: k) ->
              OpHandler e m a b post -> OpHandler (op, e) m a b post

type Handler a e (b :: k -> *) (pre :: k) (post :: k) =
  (OpHandler e (Comp e) a b post, RetClause ((a := post) post) (b pre))
type PlainHandler a e b (post :: k) =
  (OpHandler e (Comp e) a (Plain b) post, RetClause ((a := post) post) b)


-- handleOp w p k h
--
--   handle the operation at the position in op handler h denoted by
--   the witness w with parameter p and continuation k
handleOp :: Witness op e ->
            OpHandler e m a b post ->
            OpAbs op m a b post
handleOp Here      ((_, f) :<: _) = f
handleOp (There w) (_ :<: h)      = handleOp w h

handle :: Comp e (a := post) pre -> Handler a e b pre post -> b pre
handle (Ret (V x))   (h, r) = r (V x)
handle (App w _ p k) (h, r) = unOpAbs (handleOp w h) p k

-- If pre :=/=: post then the return clause cannot be defined nor
-- invoked.
nonReturningHandle :: (pre :=/=: post) =>
                         Comp e (a := post) pre -> OpHandler e (Comp e) a b post -> b pre
nonReturningHandle m h = handle m (h, undefined)

-- If the result is plain, i.e., non-dependent then this removes the
-- dependent wrapper.
handlePlainResult :: Comp e (a := post) pre -> PlainHandler a e b post -> b
handlePlainResult m (h, r) = unPlain (handle m (h, (\v -> Plain (r v))))

nonReturningHandlePlainResult :: (pre :=/=: post) =>
                                    Comp e (a := post) pre -> OpHandler e (Comp e) a (Plain b) post -> b
nonReturningHandlePlainResult m h = unPlain (nonReturningHandle m h)

-- an operation clause that throws op
throw :: In op e =>
       op -> OpClause op (Comp e) a (Comp e (a := post)) post
throw m = (m, OpAbs (\p k -> App makeWitness m p k))

infixr 1 -:<:
-- m -:<: h
--
--   extends h by throwing the effect e to be handled by an outer
--   handler
--
-- (op is a singleton type and m is its instance)
(-:<:) :: (op `NotIn` e, op `NotIn` e') =>
           op -> OpHandler e       (Comp (op, e')) a (Comp (op, e') (a := post)) post
              -> OpHandler (op, e) (Comp (op, e')) a (Comp (op, e') (a := post)) post
m -:<: h = throw m :<: h

-- Is is possible to prove that a clause is unreachable? Perhaps it
-- is with a suitable encoding of session types...

-- unreachable clause
infixr 1 >:<:
(>:<:) :: (op `NotIn` e) =>
           op -> OpHandler e       m a b post
              -> OpHandler (op, e) m a b post
m >:<: h = (m |-> undefined) :<: h

----- Example: reading a file -----

-- This is taken from Kleisli Arrows of Outrageous Fortune by Conor
-- McBride.

data FileState :: * where
  Open   :: FileState
  Closed :: FileState

data SFileState :: FileState -> * where
  SOpen   :: SFileState 'Open
  SClosed :: SFileState 'Closed

data FOpen = FOpen
instance Op FOpen where
  type Param  FOpen = FilePath := 'Closed
  type Return FOpen = SFileState
fOpen :: (In FOpen e) => String -> Comp e SFileState 'Closed
fOpen p = applyOp FOpen (V p)

data FGetC = FGetC
instance Op FGetC where
  type Param  FGetC = () := 'Open
  type Return FGetC = Maybe Char := 'Open
fGetC :: (In FGetC e) => Comp e (Maybe Char := 'Open) 'Open
fGetC = applyOp FGetC (V ())

data FClose = FClose
instance Op FClose where
  type Param  FClose = () := 'Open
  type Return FClose = () := 'Closed
fClose :: (In FClose e) => Comp e (() := 'Closed) 'Open
fClose = applyOp FClose (V ())

fileContents :: (In FOpen e, In FGetC e, In FClose e) =>
                  String -> Comp e (Maybe String := 'Closed) 'Closed
fileContents p = fOpen p ?>= \b -> case b of
  SClosed -> pure Nothing
  SOpen   -> pure (\s _ -> Just s) |*| readOpenFile |*| fClose

readOpenFile :: (In FGetC e) => Comp e (String := 'Open) 'Open
readOpenFile = fGetC =>= \x -> case x of
  Nothing -> pure ""
  Just c  -> pure (c:) |*| readOpenFile



type FIO = (FOpen, (FClose, (FGetC, ())))
unV (V x) = x
-- This is a specific handler that we want to be able to write
runFH' :: Comp FIO (a := 'Closed) 'Closed -> IO a
runFH' (Ret (V x))          = return x
runFH' (App Here FOpen s k) = catch
  (openFile (unV s) ReadMode >>= openFH (k SOpen))
  (\(_ :: IOException) -> runFH' (k SClosed))
    where
      openFH :: Comp FIO (a := 'Closed) 'Open -> Handle -> IO a
      openFH (App (There Here) FClose _ k) h = hClose h >> runFH' (k (V ()))
      openFH (App (There (There Here)) FGetC _ k) h = catch
        (hGetChar h >>= \c -> openFH (k (V (Just c))) h)
        (\(_ :: IOException) -> openFH (k (V Nothing)) h)

---- Here's an implementation using our generic handlers
runFH :: Comp FIO (a := 'Closed) 'Closed -> IO a
runFH m =
   (handlePlainResult m
   ((FOpen  |=> (\(V s) k ->
                  (catch
                     (openFile s ReadMode >>= openFH (k SOpen))
                     (\(_ :: IOException) -> runFH (k SClosed))))) :<:
     FClose >:<:
     FGetC  >:<: Empty,
    \(V x) -> return x))
 where
   openFH :: Comp FIO (a := 'Closed) 'Open -> Handle -> IO a
   openFH m h =
       (nonReturningHandlePlainResult m
          ( FOpen >:<:
           (FClose |=> (\(V ()) k -> (hClose h >> runFH (k (V ()))))) :<:
           (FGetC  |=> (\(V ()) k ->
                       (catch
                          (hGetChar h >>= \c -> openFH (k (V (Just c))) h)
                          (\(_ :: IOException) -> openFH (k (V Nothing)) h)))) :<: Empty))
