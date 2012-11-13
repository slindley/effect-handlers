-- This example demonstrates that Oleg Kiselyov's iteratees are
-- algebraic computations and enumerators are effect handlers. It is a
-- transcription of the code from Section 3 of Oleg's FLOPS 2012
-- paper, Iteratees:
-- 
--   http://okmij.org/ftp/Haskell/Iteratee/describe.pdf

{-# LANGUAGE GADTs, TypeFamilies, NoMonomorphismRestriction, RankNTypes, ImpredicativeTypes,
    MultiParamTypeClasses, FlexibleInstances, OverlappingInstances, UndecidableInstances,
    FlexibleContexts, TypeOperators, ScopedTypeVariables, BangPatterns, 
    DataKinds
 #-}

--import Control.Monad
--import Control.Monad.State

import PolyHandlers
import DesugarPolyHandlers

type LChar = Maybe Char

[operation|GetC :: LChar|]
-- data GetC (s :: ()) (t :: ()) where
--   GetC :: GetC () ()
-- type instance Return (GetC () ()) = LChar
-- getC :: ((h `Handles` GetC) ()) => Comp h LChar
-- getC = doOp GetC

type I a = forall h.[handles|h {GetC}|] => Comp h a

[handler|
  forward h handles {GetC}.EnStrHandler a :: String -> a
    handles {GetC} where
      Return x   _     -> return x
      GetC     k ""    -> do {c <- getC; k c ""}
      GetC     k (c:t) -> k (Just c) t
|]

-- data EnStrHandler (h :: *) (a :: *) = EnStrHandler String
-- type instance Result (EnStrHandler h a) = Comp h a

-- instance ((h `Handles` GetC) ()) => ((EnStrHandler h a `Handles` GetC) ()) where
--   clause GetC k (EnStrHandler "")    = do {c <- getC; k c (EnStrHandler "")}
--   clause GetC k (EnStrHandler (c:t)) = k (Just c) (EnStrHandler t)

-- instance ((h `Handles` op) args) => ((EnStrHandler h a `Handles` op) args) where
--     clause op k h = doOp op >>= (\x -> k x h)

en_str :: String -> I a -> I a
en_str s comp = enStrHandler s comp


                     
data PureRunHandler (a :: *) = PureRunHandler
type instance Result (PureRunHandler a) = a
instance ((PureRunHandler a `Handles` GetC) ()) where
  clause GetC k h = k Nothing h
pureRun :: I a -> a
pureRun comp = handle comp (\x _ -> x) PureRunHandler
                     
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

main = putStrLn (show $ countH 'a' (test 100000000))

-- -- count :: Char -> String -> Int
-- -- count c s = evalState (count' 0) s
-- --   where
-- --     count' :: Int -> State String Int
-- --     count' !n = 
-- --       do 
-- --         s <- get
-- --         case s of
-- --           [] -> return n
-- --           (c':cs) -> do {put cs; count' (if c==c' then (n+1) else n)}
        
-- -- test n = if n == 0 then ""
-- --          else "abc" ++ test (n-1)

