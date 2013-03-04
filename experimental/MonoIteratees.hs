-- This example demonstrates that Oleg Kiselyov's iteratees are
-- algebraic computations and enumerators are effect handlers. It is a
-- transcription of the code from Section 3 of Oleg's FLOPS 2012
-- paper, Iteratees:
-- 
--   http://okmij.org/ftp/Haskell/Iteratee/describe.pdf

{-# LANGUAGE GADTs, TypeFamilies, NoMonomorphismRestriction, RankNTypes,
    MultiParamTypeClasses, FlexibleInstances, OverlappingInstances,
    UndecidableInstances, FlexibleContexts, TypeOperators, ScopedTypeVariables,
    BangPatterns, QuasiQuotes, ConstraintKinds
  #-}

import Control.Monad
import Handlers
import DesugarHandlers

type LChar = Maybe Char

[operation|GetC :: LChar|]

type I a = forall h.(h `Handles` GetC) => Comp h a

getline :: I String
getline = loop ""
  where loop acc =
          do w <- getC
             check acc w
        check acc (Just c) | c /= '\n' = loop (c:acc)
        check acc _                    = return (reverse acc)

[handler|
  EvalHandler a :: String -> a handles {GetC} where
    GetC     k ""    -> k Nothing ""
    GetC     k (c:t) -> k (Just c) t
    Return x   _     -> x
|]

eval :: String -> I a -> a
eval s comp = evalHandler s comp

getlines :: I [String]
getlines = loop []
  where loop acc = getline >>= check acc
        check acc "" = return (reverse acc)
        check acc l  = loop (l:acc)

newtype EnStrHandler0 h a = EnStrHandler0 String
type instance Result (EnStrHandler0 h a) = Comp h a
instance (h `Handles` GetC) => EnStrHandler0 h a `Handles` GetC where
  clause GetC k (EnStrHandler0 "")    = do {c <- getC; k c (EnStrHandler0 "")}
  clause GetC k (EnStrHandler0 (c:t)) = k (Just c) (EnStrHandler0 t)
--en_str0 :: String -> I a -> I a
en_str0 s comp = handle comp (\x _ -> return x) (EnStrHandler0 s)

[operation|Foo :: ()|]
bar = do {x <- getC; foo; return x}

-- we should allow constraints on closed handlers

-- [handler|
--   (h handles {GetC}) =>
--     EnStrHandler0 h a :: String -> Comp h a
--       handles {GetC} where
--         Return x   _     -> return x
--         GetC     k ""    -> do {c <- getC; k c ""}
--         GetC     k (c:t) -> k (Just c) t
-- |]

-- Perhaps forwarding should be syntactic sugar for default patterns.
--
-- Potentially, this could support other kinds of behaviour. For
-- instance, we could count the number of forwarded operations. We
-- could also do things like duplicate the continuation for forwarded
-- computations. It's not entirely clear how that would be useful. We
-- can't inspect forward operations, as they are polymorphic.

-- [handler|
--   (h handles {GetC}) =>
--     EnStrHandler h a :: String -> Comp h a handles {GetC} where
--       Return x   _     -> return x
--       GetC     k ""    -> do {c <- getC; k c ""}
--       GetC     k (c:t) -> k (Just c) t
--       op       k s     -> do {x <- op; k x s}
-- |]



[handler|
  forward h.(h `Handles` GetC) =>
    EnStrHandler a :: String -> a handles {GetC} where
      GetC     k ""    -> do {c <- getC; k c ""}
      GetC     k (c:t) -> k (Just c) t
      Return x   _     -> return x
|]

type J a = forall h c.(h `Handles` GetC, c h) => Comp h a

en_str :: (h `Handles` GetC) => String -> I a -> Comp h a
en_str s comp = enStrHandler s comp

-- data EnStrHandler h a = EnStrHandler String
-- type instance Result (EnStrHandler h a) = Comp h a

-- instance (h `Handles` GetC) => (EnStrHandler h a `Handles` GetC) where
--   clause GetC k (EnStrHandler "")    = do {c <- getC; k c (EnStrHandler "")}
--   clause GetC k (EnStrHandler (c:t)) = k (Just c) (EnStrHandler t)

-- instance (h `Handles` op) => (EnStrHandler h a `Handles` op) where
--     clause op k h = doOp op >>= (\x -> k x h)

-- en_str :: String -> I a -> I a
-- en_str s comp = handle comp (\x _ -> return x) (EnStrHandler s)

-- RunHandler throws away any outstanding unhandled GetC applications
[handler|
  forward h.RunHandler a :: a handles {GetC} where
    GetC     k -> k Nothing
    Return x   -> return x
|]

run :: I a -> Comp h a
run comp = runHandler comp

-- like RunHandler but with no underlying handler
[handler|
  PureRunHandler a :: a handles {GetC} where
    GetC   k -> k Nothing
    Return x -> x
|]
pureRun :: I a -> a
pureRun comp = pureRunHandler comp

data FlipState h a = FlipState Bool LChar (LChar -> FlipState h a -> Comp h a)
[handler|
  forward h.(h `Handles` GetC) =>
    FlipHandler a :: FlipState h a -> a handles {GetC} where
      GetC     kl (FlipState True  c kr) -> do {kr c (FlipState False c kl)}
      GetC     kr (FlipState False _ kl) -> do {c <- getC; kl c (FlipState True c kr)}
      Return x    _                      -> return x
|]

-- data FlipHandler h a = (h `Handles` GetC) => FlipHandler (Bool, LChar, LChar -> FlipHandler h a -> Comp h a)
-- type instance Result (FlipHandler h a) = Comp h a

-- instance (FlipHandler h a `Handles` GetC) where
--   clause GetC kl (FlipHandler (True,  c, kr)) = do {kr c (FlipHandler (False, c, kl))}
--   clause GetC kr (FlipHandler (False, _, kl)) = do {c <- getC; kl c (FlipHandler (True, c, kr))}

-- instance (h `Handles` op) => (FlipHandler h a `Handles` op) where
--   clause op k h = doOp op >>= (\x -> k x h)

-- l <| r = handle l (\x _ -> return x)
--          (FlipHandler True Nothing (\Nothing h' -> handle r (\x _ -> return x) h'))


-- synchronise two iteratees
(<|) :: I a -> I a -> I a
l <| r = flipHandler (FlipState True Nothing (\Nothing s -> flipHandler s r)) l


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

count :: Char -> String -> Int
count c s = count' s 0
  where
    count' :: String -> Int -> Int
    count' []      !n = n
    count' (c':cs) !n = count' cs (if c==c' then n+1 else n)
    
test n = if n == 0 then ""
         else "abc" ++ test (n-1)

main = putStrLn (show $ countH 'a' (test 100000000))
