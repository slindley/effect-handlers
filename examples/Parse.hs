{-# LANGUAGE TypeFamilies,
    GADTs,
    NoMonomorphismRestriction,
    RankNTypes,
    MultiParamTypeClasses,
    QuasiQuotes,
    FlexibleInstances,
    FlexibleContexts,
    OverlappingInstances,
    UndecidableInstances,
    ConstraintKinds,
    TypeOperators,
    ScopedTypeVariables, 
    DataKinds,
    PolyKinds
 #-}

import Control.Applicative
import Control.Monad (ap)

-- import Control.Monad.ST
-- import Data.STRef

import ShallowFreeHandlers
import DesugarHandlers

instance Applicative (Comp h) where
    pure = return
    (<*>) = ap

[operation|Choice           :: Bool|] 
[operation|forall a.Failure :: a|]
[operation|Token            :: Char|]
--[operation|forall a.NT (nt :: * -> *) :: nt -> a |]
data NT (nt :: * -> *) (a :: *) = NT (nt a)
type instance Return (NT nt a) = a
nT :: (h `Handles` NT) nt => nt a -> Comp h a
nT x = doOp (NT x)

-- the type of parser computations
type PC nt a = ([handles|h {Choice}|], [handles|h {Failure}|], [handles|h {Token}|],
                (h `Handles` NT) nt) => Comp h a

type Grammar nt = forall a.nt a -> PC nt a

data Stack nt a b where
  Empty :: Stack nt a a
  Cons  :: (a -> Comp (Parser nt c b) c) -> Stack nt c b -> Stack nt a b


-- [handler|
--   Parser nt b a :: Grammar nt -> String -> Stack nt a b -> Maybe (b, String)
--     handles {Choice, Failure, Token, NT nt} where
--       Return x   g s      Empty          -> Just (x, s)
--       Return x   g s      (Cons k stack) -> parser g s stack (k x)
--       Choice   k g s      stack          ->
--         case parser g s stack (k True) of
--           Nothing -> parser g s stack (k False)
--           Just s  -> Just s
--       Failure  k g s      stack          -> Nothing
--       Token    k g []     stack          -> Nothing
--       Token    k g (c:cs) stack          ->
--         parser g cs stack (k c)
--       NT x     k g s      stack          ->
--         parser g s (Cons k stack) (g x)
-- |]

data Parser nt a b = Parser (Grammar nt) String (Stack nt a b)
type instance Result (Parser nt a b) = Maybe (b, String)
type instance Inner (Parser nt a b) = a

instance (Parser nt a b `Handles` Choice) () where
  clause Choice k (Parser g s stack) =
    case  parser g s stack (k True) of
      Nothing -> parser g s stack (k False)
      Just s  -> Just s
instance (Parser nt a b `Handles` Failure) () where
  clause Failure k h = Nothing
instance (Parser nt a b `Handles` Token) () where
  clause Token k (Parser g (c:cs) stack) =
    parser g cs stack (k c)
  clause Token k (Parser g [] stack) = Nothing  
instance (Parser nt a b `Handles` NT) nt where
  clause (NT x) k (Parser g s stack) =
    parser g s (Cons k stack) (g x)
parser :: Grammar nt -> String -> Stack nt a b -> Comp (Parser nt a b) a -> Maybe (b, String)
parser g s stack comp = handle comp ret (Parser g s stack)
  where
    ret :: a -> Parser nt a b -> Maybe (b, String)
    ret x (Parser g s Empty)          = Just (x, s)
    ret x (Parser g s (Cons k stack)) = parser g s stack (k x)

parse :: Grammar nt -> String -> PC nt a -> Maybe (a, String)
parse g s c = parser g s Empty c

-- helper functions
tok :: ([handles|h {Token}|], [handles|h {Failure}|]) => Char -> Comp h () -> Comp h ()
tok c k = do c' <- token; if c == c' then k else failure

stop :: Comp h ()
stop = return ()

(|||) :: ([handles|h {Choice}|]) => Comp h a -> Comp h a -> Comp h a
p ||| q = do b <- choice; if b then p else q

data Gram (x :: *) where 
  S :: Gram ()
  X :: Gram ()
gram :: Grammar Gram
gram S = tok 'x' stop ||| nT X
gram X = tok 'y' (nT S)

test1 = parse gram "yyyxabasdfasef"  (nT S)

