{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction, RankNTypes,
    MultiParamTypeClasses,
    FlexibleContexts, TypeOperators, ScopedTypeVariables #-}

import Control.Monad
import OpenHandlers

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
    
data StreamKind = Numerator | Denominator

data DivReader a = DivReader [Int] [Int]
type instance Result (DivReader a) = a
instance (DivReader a `Handles` GetN) where
  clause (DivReader (n:ns) ds) GetN k = k (DivReader ns ds) n
instance (DivReader a `Handles` GetD) where
  clause (DivReader ns (d:ds)) GetD k = k (DivReader ns ds) d
  
readAndDivide ns ds = handle divs (DivReader ns ds) (const id)


-- TODO: reinterpret this computation to support various kinds of
-- error conditions / exception handling




