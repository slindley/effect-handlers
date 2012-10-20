-- This example demonstrates that Oleg Kiselyov's iteratees are
-- algebraic computations and enumerators are effect handlers. It is a
-- transcription of the code from Section 3 of Oleg's FLOPS 2012
-- paper, Iteratees:
-- 
--   http://okmij.org/ftp/Haskell/Iteratee/describe.pdf

{-# LANGUAGE GADTs, TypeFamilies, NoMonomorphismRestriction, RankNTypes,
    MultiParamTypeClasses, FlexibleInstances, OverlappingInstances,
    FlexibleContexts, TypeOperators, ScopedTypeVariables #-}

import Control.Monad
import ParameterisedOpenHandlers

type LChar = Maybe Char

data GetC = GetC
instance Op GetC where
  type Param GetC  = ()
  type Return GetC = LChar
getC = applyOp GetC ()

type I a = (h `Handles` GetC) => Comp h a

getline :: (h `Handles` GetC) => Comp h String
getline = loop ""
  where loop acc =
          do w <- getC
             check acc w
        check acc (Just c) | c /= '\n' = loop (c:acc)
        check acc _                    = return (reverse acc)

data EvalHandler a = EvalHandler String
instance Handler (EvalHandler a) where
  type Result (EvalHandler a) = a
  type Inner (EvalHandler a) = a
  ret _ x = x

instance (EvalHandler a `Handles` GetC) where
  clause _ (EvalHandler "")    () k = k (EvalHandler "") Nothing
  clause _ (EvalHandler (c:t)) () k = k (EvalHandler t) (Just c)

getlines :: (h `Handles` GetC) => Comp h [String]
getlines = loop []
  where loop acc = getline >>= check acc
        check acc "" = return (reverse acc)
        check acc l  = loop (l:acc)
        
data EnStrHandler h a = EnStrHandler String
instance Handler (EnStrHandler h a) where
  type Result (EnStrHandler h a) = Comp (EnStrHandler h a) a
  type Inner (EnStrHandler h a) = a
  ret _ x = return x

instance (EnStrHandler h a `Handles` GetC) where
  clause _ (EnStrHandler "")    () k = do {c <- getC; k (EnStrHandler "") c}
  clause _ (EnStrHandler (c:t)) () k = k (EnStrHandler t) (Just c)

instance (h `Handles` op) => (EnStrHandler h a `Handles` op) where
  clause m h p k = Comp (\h' k' ->
                          clause m h' p (\h'' x -> unComp (k h'' x) h' k'))
  
-- RunHandler throws away any outstanding unhandled GetC applications
data RunHandler h a = RunHandler String
instance Handler (RunHandler h a) where
  type Result (RunHandler h a) = Comp h a
  type Inner (RunHandler h a) = a
  ret _ x = return x

instance (RunHandler h a `Handles` GetC) where
  clause _ h () k = k h Nothing

instance (h `Handles` op) => (RunHandler h a `Handles` op) where
  clause m h p k = Comp (\h' k' ->
                          clause m h' p (\h'' x -> unComp (k h x) h' k'))

data FlipHandler h a = (h `Handles` GetC) => FlipHandler (Bool, LChar, FlipHandler h a -> LChar -> Comp h a)
instance (Handler (FlipHandler h a)) where
  type Result (FlipHandler h a) = Comp h a
  type Inner (FlipHandler h a) = a
  ret _ x = return x

instance (FlipHandler h a `Handles` GetC) where
  clause _ (FlipHandler (True,  c, kr)) () kl = do {kr (FlipHandler (False, c, kl)) c}
  clause _ (FlipHandler (False, _, kl)) () kr = do {c <- getC; kl (FlipHandler (True, c, kr)) c}

instance (h `Handles` op) => (FlipHandler h a `Handles` op) where
  clause m h p k = Comp (\h' k' ->
                          clause m h' p (\h'' x -> unComp (k h x) h' k'))

-- synchronise two iteratees
(<|) :: I a -> I a -> I a
l <| r = handle l (FlipHandler (True, Nothing, \h' Nothing -> handle r h'))

-- Roughly, we get the following behaviour from the synchronised
-- traces of (l <| r):
-- 
--     ls1...GetC...ls2...GetC...  ...GetC...lsn
--            ||           ||          ||
--     rs1...GetC...rs2...GetC...  ...GetC...rsn
--
-- becomes:
--
--     ls1,rs1, GetC, ls2,rs2, GetC,...,GetC lsn,rsn

-- fetch characters forever
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
