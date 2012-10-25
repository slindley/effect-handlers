{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction, RankNTypes,
    MultiParamTypeClasses,
    FlexibleContexts, TypeOperators, ScopedTypeVariables #-}

import Control.Monad
import OpenHandlers


-- data Failure = Failure
-- type instance Return Failure = Void
-- failure = doOp Failure >>= undefined

data DivideByZero a = DivideByZero
type instance Return (DivideByZero a) = a
divideByZero = polyDoOp DivideByZero

data EndOfStream a = EndOfStream
type instance Return (EndOfStream a) = a
endOfStream = polyDoOp EndOfStream

data GetN = GetN
type instance Return GetN = Int
getN = doOp GetN

data GetD = GetD
type instance Return GetD = Int
getD = doOp GetD

divs :: (h `Handles` GetN, h `Handles` GetD) => Comp h [Int]
divs =
  do
    n <- getN
    d <- getD
    fmap ((:) (n `div` d)) divs
    
-- TODO: reinterpret this computation to support various kinds of
-- error conditions / exception handling




