-- dynamic handlers with no effect typing

{-# LANGUAGE GADTs, KindSignatures,
    TypeOperators, ScopedTypeVariables #-}

module DynamicHandlers where

import System.IO.Unsafe
import Unsafe.Coerce
import Data.IORef

newtype Op p r = Op {unOp :: Int}

opSource :: IORef Int
opSource = unsafePerformIO (newIORef 0)

newOp :: () -> Op p r
newOp () = unsafePerformIO freshOp
    where
      freshOp = do {n <- readIORef opSource; writeIORef opSource (n+1); return $ Op n}

-- Computations of type a
--   Ret v:      return value v
--   Do op p k: operation op, parameter p, continuation k
data Comp a :: * where
  Ret :: a -> Comp a
  Do  :: Op p r -> p ->
           (r -> Comp a) -> Comp a

instance Monad Comp where
  return = Ret
  (Ret v)      >>= k = k v
  (Do op p k') >>= k = Do op p (\v -> k' v >>= k)

instance Functor Comp where
  fmap f c = c >>= return . f

-- direct style operation application
applyOp :: Op p r -> p -> Comp r
applyOp op p = Do op p return

data OpClause a where
  OpClause :: Op p r -> OpAbs p r a -> OpClause a
type RetClause a b = a -> b

type OpAbs p r a = p -> (r -> a) -> a

(|->) :: Op p r -> OpAbs p r a -> OpClause a
(|->) = OpClause
infix 2 |-> 

data Mode a where
  Open   :: Mode (Comp a)
  Closed :: Mode a

type OpHandler a = [OpClause a]
type Handler a b = (Mode b, OpHandler b, RetClause a b)

-- handleOp m mode cs p k
--
--   look up the operation in the list - if it's not there and the
--   mode is 'Open' then forward to an outer handler
handleOp :: Op p r -> Mode a -> OpHandler a -> OpAbs p r a
handleOp op Open []                                         = Do op
handleOp op _    (OpClause op' f : _) | unOp op == unOp op' = unsafeCoerce f
handleOp op mode (_  : cs)                                  = handleOp op mode cs

handle :: Comp a -> Handler a b -> b
handle (Ret v)     (_, _, r)     = r v
handle (Do op p k) (mode, cs, r) = handleOp op mode cs p k'
  where k' v = handle (k v) (mode, cs, r)

get :: Op () Int
get = newOp ()

put :: Op Int ()
put = newOp ()

closedStateHandler :: Comp a -> Int -> a
closedStateHandler comp =
  handle comp
    (Closed,
     [get |-> (\() k s -> k s s),
      put |-> (\s  k _ -> k () s)],
     (\x _ -> x))

openStateHandler :: Comp a -> Int -> Comp a
openStateHandler comp s =
  do
    f <- (handle comp
          (Open,
           [get |-> (\() k -> return $ \s -> do {f <- k s; f s}),
            put |-> (\s  k -> return $ \_ -> do {f <- k (); f s})],
           (\x -> return $ (\_ -> return x))))
    f s
