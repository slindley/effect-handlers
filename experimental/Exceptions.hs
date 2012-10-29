{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction,
    RankNTypes,
    MultiParamTypeClasses, TemplateHaskell, QuasiQuotes, FlexibleInstances, OverlappingInstances,
    FlexibleContexts, TypeOperators, ScopedTypeVariables #-}

import Control.Monad
import OpenHandlers
import DesugarHandlers

[operation|Divide : Int -> Int -> Int|]
[handler|
  forward h.
    DivideHandler a : Comp h a handles {Divide} where
      clause h (Divide x y) k = k h (x `div` y)
|]
[handler|
  forward h.(h `PolyHandles` DivideByZero, h `Handles` Divide) =>
    CheckZeroHandler a : Comp h a handles {Divide} where
      clause h (Divide x y) k = if y == 0 then
                                   divideByZero
                                else
                                   (x `divide` y) >>= k h
|]
[handler|
  forward h.ReportErrorHandler a : Comp h (Either String a) handles {DivideByZero} where
    polyClause _ DivideByZero k = return $ Left "Cannot divide by zero"
|]

type D a = forall h.(h `Handles` Divide) => Comp h a

divUnchecked :: D a -> a
divUnchecked comp =
  handlePure (handle comp DivideHandler (const return))

divChecked :: D a -> Either String a
divChecked comp =
  handlePure
  (handle
   (handle
    (handle comp CheckZeroHandler (\_ x -> return (Right x)))
    DivideHandler (const return)) 
   ReportErrorHandler (const return))



[operation|forall a.DivideByZero : a|]
[operation|forall a.EndOfStream : a|]
[operation|GetN : Int|]
[operation|GetD : Int|]


divs :: (h `Handles` GetN, h `Handles` GetD) => Comp h [Int]
divs =
  do
    n <- getN
    d <- getD
    fmap ((:) (n `div` d)) divs
    
data StreamKind = Numerator | Denominator

[handler|
  DivReader a : [Int] -> [Int] -> a handles {GetN, GetD} where
    clause (DivReader (n:ns) ds) GetN k = k (DivReader ns ds) n
    clause (DivReader ns (d:ds)) GetD k = k (DivReader ns ds) d
|]
  
readAndDivide ns ds = handle divs (DivReader ns ds) (const id)

-- TODO: reinterpret this computation to support various kinds of
-- error conditions / exception handling




