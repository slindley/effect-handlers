-- This example demonstrates that Oleg Kiselyov's iteratees are
-- algebraic computations and enumerators are effect handlers. It is a
-- transcription of the code from Section 3 of Oleg's FLOPS 2012
-- paper, Iteratees:
-- 
--   http://okmij.org/ftp/Haskell/Iteratee/describe.pdf

{-# LANGUAGE GADTs, TypeFamilies, NoMonomorphismRestriction,
             FlexibleContexts, TypeOperators, ScopedTypeVariables #-}

import Control.Monad
import Handlers

type LChar = Maybe Char

data GetC = GetC
instance Op GetC where
  type Param GetC  = ()
  type Return GetC = LChar
getC = applyOp GetC ()

type I a = Comp (GetC, ()) a

getline :: (GetC `In` e) => Comp e String
getline = loop ""
  where loop acc =
          do w <- getC
             check acc w
        check acc (Just c) | c /= '\n' = loop (c:acc)
        check acc _                    = return (reverse acc)

-- Oleg's implementation is based on control0-like behaviour.  We get
-- the same effect by moving the parameterisation of eval inside the
-- handler: the return type of the handler is String -> a.
--
-- Could we give a more direct translation of Oleg's code by working
-- out how to represent control0-style handlers in terms of
-- shift0-style handlers?
eval :: String -> I a -> a
eval s comp =
  handle comp
  (GetC |-> (\() k ->
              \s -> 
              case s of
                ""    -> k Nothing ""
                (c:t) -> k (Just c) t)
   :<: Empty,
   \x -> \s -> x)
   s

eval' :: String -> I a -> a
eval' s comp =
  handle comp
  (GetC |-> (\() k ->
              case s of
                ""    -> eval' "" $ return $ k Nothing
                (c:t) -> eval' t  $ return $ k (Just c))
   :<: Empty,
   id)


getlines :: (GetC `In` e) => Comp e [String]
getlines = loop []
  where loop acc = getline >>= check acc
        check acc "" = return (reverse acc)
        check acc l  = loop (l:acc)
        
en_str :: String -> I a -> I a
en_str s comp =
  handle comp
  (GetC |-> (\() k ->
              \s ->
              case s of
                ""    -> comp
                (c:t) -> k (Just c) t) :<: Empty,
   \x -> \s -> return x)
   s

run :: I a -> a
run comp =
  handle comp
  (GetC |-> (\n k -> k Nothing) :<: Empty,
   id)


(<|) :: I a -> I a -> I a
Ret x                 <| _                     = return x
_                     <| Ret x                 = return x
(App Here GetC () k1) <| (App Here GetC () k2) =
  App makeWitness GetC () (\c -> k1 c <| k2 c)

failure :: I a
failure = getC >>= const failure

empty :: a -> I a
empty = return

oneL :: I LChar
oneL = getC

one :: I Char
one = oneL >>= maybe failure return

pSat :: (LChar -> Bool) -> I LChar
pSat pred = oneL >>= \c -> if pred c then return c else failure

pGetline :: I String
pGetline = nl <| liftM2 (:) one pGetline
  where nl =
          do
            pSat (\c -> c == Just '\n' || c == Nothing)
            return ""
            
pGetline' :: I String
pGetline' = oneL >>= check
  where check (Just '\n') = return ""
        check Nothing     = return ""
        check (Just c)    = liftM (c:) pGetline'
