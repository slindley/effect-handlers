-- Iteratees using McBride handlers. This gives a more direct
-- translation of Oleg Kiselyov's code than the version that uses
-- standard effect handlers (Iteratees.hs).

{-# LANGUAGE GADTs, TypeFamilies, NoMonomorphismRestriction,
             FlexibleContexts, TypeOperators, ScopedTypeVariables #-}

import Control.Monad
import McBrideHandlers

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

eval :: String -> I a -> a
eval s comp =
  handle comp
  (GetC |-> (\() k ->
              case s of
                ""    -> eval "" $ k Nothing
                (c:t) -> eval t  $ k (Just c))
   :<: Empty,
   id)

getlines :: (GetC `In` e) => Comp e [String]
getlines = loop []
  where loop acc = getline >>= check acc
        check acc "" = return (reverse acc)
        check acc l  = loop (l:acc)
        
--en_str :: String -> I a -> I a
en_str' s comp =
  handle comp
  (GetC |-> (\() k ->
              case s of
                ""    -> comp
                (c:t) -> en_str t $ k (Just c)) :<: Empty,
   return)


en_str ""    comp = comp
en_str (c:t) comp =
  handle comp
  (GetC |-> (\() k -> en_str t $ k (Just c)) :<: Empty,
   return)


run :: I a -> a
run comp =
  handle comp
  (GetC |-> (\n k -> run $ k Nothing) :<: Empty,
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
