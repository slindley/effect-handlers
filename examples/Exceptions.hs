{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction,
    RankNTypes,
    MultiParamTypeClasses, TemplateHaskell, QuasiQuotes, FlexibleInstances, OverlappingInstances,
    FlexibleContexts, TypeOperators, ScopedTypeVariables #-}

import Control.Monad
import Handlers
import DesugarHandlers

[operation|Divide : Int -> Int -> Int|]
[operation|forall a.DivideByZero : a|]
[handler|
  forward h.
    DivideHandler a : Comp h a handles {Divide} where
      clause (Divide x y) k h = k (x `div` y) h
      ret x _ = return x
      -- Divide x y k -> k (x `div` y)
      -- Return x     -> return x                                   
|]    
[handler|
  forward h.(h `PolyHandles` DivideByZero, h `Handles` Divide) =>
    CheckZeroHandler a : Comp h a handles {Divide} where
      clause (Divide x y) k h = if y == 0 then
                                   divideByZero
                                else
                                   (x `divide` y) >>= (\x -> k x h)
      ret x _ = return (Right x)
|]
[handler|
  forward h.ReportErrorHandler a : Comp h (Either String a) polyhandles {DivideByZero} where
    polyClause DivideByZero k _ = return $ Left "Cannot divide by zero"
    ret x _ = return x
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


