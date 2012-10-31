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
      clause (Divide x y) h k = k h (x `div` y)
|]
[handler|
  forward h.(h `PolyHandles` DivideByZero, h `Handles` Divide) =>
    CheckZeroHandler a : Comp h a handles {Divide} where
      clause (Divide x y) h k = if y == 0 then
                                   divideByZero
                                else
                                   (x `divide` y) >>= k h
      -- Divide x y k -> ...
      -- Return x     -> return x                                   
|]
[handler|
  forward h.ReportErrorHandler a : Comp h (Either String a) handles {DivideByZero} where
    polyClause DivideByZero _ k = return $ Left "Cannot divide by zero"
|]


type D a = forall h.(h `Handles` Divide) => Comp h a

divUnchecked :: D a -> a
divUnchecked comp =
  handlePure (handle comp DivideHandler (const return))

-- Looks like we could do with more help from the sugar! We should be
-- able to define return clauses and generate corresponding default
-- handling functions. Then we should have a concise way of writing
-- handler composition.

-- Perhaps (const return) should be a default for forwarding handlers
-- and (const id) for non-forwarding handlers.

divChecked :: D a -> Either String a
divChecked comp =
  handlePure
  (handle
   (handle
    (handle comp CheckZeroHandler (\_ x -> return (Right x)))
    DivideHandler (const return)) 
   ReportErrorHandler (const return))

