{-
  Iteratees as shallow handlers.

  This example demonstrates that Oleg Kiselyov's iteratees are
  algebraic computations and enumerators are effect handlers. It is a
  transcription of the code from Section 3 of Oleg's FLOPS 2012
  paper, Iteratees:
   
    http://okmij.org/ftp/Haskell/Iteratee/describe.pdf
-}

{-# LANGUAGE GADTs, TypeFamilies, NoMonomorphismRestriction, RankNTypes,
    MultiParamTypeClasses, FlexibleInstances, OverlappingInstances, UndecidableInstances,
    FlexibleContexts, BangPatterns, QuasiQuotes
 #-}

import Control.Monad

import ShallowFreeHandlers
import DesugarHandlers

import Unsafe.Coerce

type LChar = Maybe Char

[operation|GetC :: LChar|]

type I a = forall h.[handles|h {GetC}|] => Comp h a

getline :: I String
getline = loop ""
  where loop acc =
          do w <- getC
             check acc w
        check acc (Just c) | c /= '\n' = loop (c:acc)
        check acc _                    = return (reverse acc)

[shallowHandler|
  EvalHandler a :: String -> a
    handles {GetC} where
      GetC     k ""    -> evalHandler "" $ k Nothing
      GetC     k (c:t) -> evalHandler t  $ k (Just c)
      Return x   _     -> x
|]

eval :: String -> I a -> a
eval s comp = evalHandler s comp

getlines :: I [String]
getlines = loop []
  where loop acc = getline >>= check acc
        check acc "" = return (reverse acc)
        check acc l  = loop (l:acc)

-- The following enumerator implementation is inefficient because it
-- unnecessarily traverses the unhandled part of the continuation
-- once the input has run out.
--
-- The difficulty with writing an efficient version arises because
-- of limitations in our type-class based implementation of        
-- handlers. Frank, for example, would not have this problem.
[shallowHandler|
  forward h handles {GetC}.
    EnStrHandler a :: String -> a
      handles {GetC} where
        Return x   _     -> return x
        GetC     k ""    -> do {c <- getC; enStrHandler "" (k c)}
        GetC     k (c:t) -> enStrHandler t $ k (Just c)
|]

-- this one is efficient, but is closed
[shallowHandler|
  EnStrHandlerRec a :: String -> Comp (EnStrHandlerRec a) a
    handles {GetC} where
      Return x   _     -> return x
      GetC     k ""    -> do {c <- getC; k c}
      GetC     k (c:t) -> enStrHandlerRec t $ k (Just c)
|]

-- this one is efficient and open, but relies on an unsafe coercion
[shallowHandler|
  forward h handles {GetC}.
    EnStrHandlerUnsafe a :: String -> a
      handles {GetC} where
        Return x   _     -> return x
        GetC     k ""    -> do {c <- getC; unsafeCoerce (k c)}
        GetC     k (c:t) -> enStrHandlerUnsafe t $ k (Just c)
|]

en_str :: String -> I a -> I a
en_str s comp = enStrHandlerUnsafe s comp

-- RunHandler throws away any outstanding unhandled GetC applications
[shallowHandler|
 forward h.RunHandler a :: a
    handles {GetC} where
      GetC     k -> runHandler $ k Nothing
      Return x   -> return x
|]

run :: I a -> Comp h a
run comp = runHandler comp


-- like RunHandler but with no underlying handler
[shallowHandler|
  PureRun a :: a
    handles {GetC} where
      Return x -> x
      GetC   k -> pureRun $ k Nothing
|]

[shallowHandler|
  forward h handles {GetC}.
    LeftI a :: (Comp (RightI h a) a) -> a
      handles {GetC} where
        Return x   r -> return x
        GetC     k r -> undefined $ rightI k r
|]

[shallowHandler|
  forward h handles {GetC}.
    RightI a :: (LChar -> Comp (LeftI h a) a) -> a
      handles {GetC} where
        Return x   l -> return x
        GetC     k l -> do {c <- getC; leftI (k c) (l c)}
|]

(<|) :: I a -> I a -> I a
l <| r = leftI r l

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



countI :: Char -> I Int
countI c = count' 0
  where
    count' :: Int -> I Int
    count' !n =
      do
        mc <- getC
        case mc of
            Nothing -> return n
            Just c' -> count' (if c==c' then n+1 else n)
         
countH :: Char -> String -> Int
countH c s = pureRun (en_str s (countI c))
       
test n = if n == 0 then ""
         else "abc" ++ test (n-1)

main = print (countH 'a' (test 100000000))
