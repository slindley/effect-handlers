{-# LANGUAGE TypeFamilies,
    GADTs,
    RankNTypes,
    MultiParamTypeClasses,
    QuasiQuotes,
    FlexibleInstances,
    FlexibleContexts,
    OverlappingInstances,
    UndecidableInstances,
    ConstraintKinds,
    DataKinds, 
    NoMonomorphismRestriction   
 #-}

import Handlers
import TopLevel
import DesugarHandlers
import System.IO
import Control.Monad
import Network
import Control.Concurrent
import Data.Array.IO

[operation| ReadChar :: Maybe  Char |]
[operation| Eof :: Bool |]



readLine = 
  do
  mc <- readChar  
  case mc of 
    Nothing -> return []
    Just '\n' -> return []
    Just c -> do
              l <- readLine
              return (c : l)
              
[handler|
  forward h handles {ReadChar}.
    CountChar0 a :: Int -> (a,Int)
      handles {ReadChar} where
           Return x i -> return (x,i)
           ReadChar k i ->  do 
                            m <- readChar
                            case m of
                              Nothing -> k m i
                              Just _ ->  k m $! i + 1 |]

countChar = countChar0 0
-- Bool represents whether in a word
[handler| 
 forward h handles {ReadChar}.
     CountWord0 a :: Int -> Bool -> (a,Int) 
       handles {ReadChar} where
           Return x i _ -> return (x,i)
           ReadChar k i b -> 
                     do
                     m <- readChar
                     case m of 
                        Nothing  -> (k m $! (if b then i + 1 else i)) $ False
                        Just w -> if  (w == ' ' ||  w == '\t' || w == '\n') then 
                                    (k m $! (if b then i + 1 else i)) $ False
                                   else  k m i True |]

countWord = countWord0 0 False

                     
[handler| 
   CharFromString a :: String -> a
        handles {ReadChar, Eof} where
               Return x _ -> x
               ReadChar k [] -> k Nothing []
               ReadChar k (s : l) -> k (Just s) l      
               Eof k [] -> k True []
               Eof k l  -> k False l 
                      |]


wc = 
   do 
     ((lines, words), chars) <-  countChar (countWord (loop 0))   
     return (chars, words, lines)
   where 
   loop  i =   
     do
     b <- eof
     if b then return i
          else 
          do
          _ <- readLine  
          loop $! (i + 1)           
          
          
[operation| SaveLine :: String -> () |]
[operation| PrintAll :: () |]



[handler| 
  forward h handles {Io}. 
    KeepAll0 a :: [String] -> Int -> a
       handles {SaveLine, PrintAll} where
           Return x _ _ -> return x
           SaveLine s k l i -> k () (s:l) i
           PrintAll k  l i  -> 
                 do
                 io (forM_ (take i l) putStrLn) 
                 k () l i|]

keepAll = keepAll0 []

tailC = 
  do
  l <- readLine  
  saveLine l
  b <- eof
  if b then printAll else tailC
  
data CircularArray  = CircularArray !Int !(IOArray Int String) !Int !Int
  
newCircularArray i = do
  a <- io (newArray (0, i - 1) []) 
  return (CircularArray i a 0 0)
                       
incrIdx length i = 
  let j = i + 1 in
  if (j < length) then j else 0

push (CircularArray length arr first next) elt =                        
  do
    io (writeArray arr next elt)
    let j = incrIdx length next 
    return (CircularArray length arr (if (j == first) then (incrIdx length first) else first) j)
  
printAllCircularArray (CircularArray length arr first next) = 
    loop first
    where
      loop i = if (i == next) 
               then return () 
               else do 
                 io ((readArray arr i) >>= putStrLn)
                 loop (incrIdx length i)
                  
 
 [handler|  
  forward h handles {Io}.
     CircularArray :: CircularArray -> a
      handles {SaveLine, PrintAll} where
         Return x _ -> return x    
         SaveLine s k c -> push c s >>= k ()
         PrintAll k c -> printAllCircularArray c >> k () c |]