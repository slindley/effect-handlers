{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction,
    RankNTypes,
    MultiParamTypeClasses, TemplateHaskell, QuasiQuotes, FlexibleInstances, OverlappingInstances,
    FlexibleContexts, TypeOperators, ScopedTypeVariables #-}

import Control.Monad
import OpenHandlers
import DesugarHandlers

[operation|Divide : Int -> Int -> Int|]
[operation|forall a.DivideByZero : a|]
[handler|
  forward h.
    DivideHandler a : Comp h a handles {Divide} where
      clause (Divide x y) h k = k h (x `div` y)
      ret _ x = return x
      -- Divide x y k -> ...
      -- Return x     -> return x                                   
|]    
[handler|
  forward h.(h `PolyHandles` DivideByZero, h `Handles` Divide) =>
    CheckZeroHandler a : Comp h a handles {Divide} where
      clause (Divide x y) h k = if y == 0 then
                                   divideByZero
                                else
                                   (x `divide` y) >>= k h
      ret _ x = return (Right x)
|]
[handler|
  forward h.ReportErrorHandler a : Comp h (Either String a) handles {DivideByZero} where
    polyClause DivideByZero _ k = return $ Left "Cannot divide by zero"
    ret _ x = return x
|]


type D a = forall h.(h `Handles` Divide) => Comp h a

divUnchecked :: D a -> a
divUnchecked comp = (handlePure . divideHandler) comp 

-- Perhaps (const return) should be a default for forwarding handlers
-- and (const id) for non-forwarding handlers?
--
-- For now we'll just insist on including the return clause. Automatic
-- things may be too bug-prone and confusing.

divChecked :: D a -> Either String a
divChecked comp = (handlePure . reportErrorHandler . divideHandler . checkZeroHandler) comp


