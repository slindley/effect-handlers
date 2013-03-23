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

[operation|ReadChar :: Maybe Char|]
[operation|Finished :: Bool|]

readLine :: [handles|h {ReadChar}|] => Comp h String
readLine = 
  do
    mc <- readChar  
    case mc of 
      Nothing   -> return []
      Just '\n' -> return []
      Just c -> do
                  l <- readLine
                  return (c : l)
              
[handler|
  forward h handles {ReadChar}.
    CountChar0 a :: Int -> (a, Int)
      handles {ReadChar} where
        Return x i   -> return (x,i)
        ReadChar k i -> do 
                          m <- readChar
                          case m of
                            Nothing -> k m i
                            Just _  -> k m $! i + 1 |]
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
              Nothing -> (k m $! (if b then i + 1 else i)) $ False
              Just w  -> if (w == ' ' ||  w == '\t' || w == '\n' || w == '\r') then 
                           (k m $! (if b then i + 1 else i)) $ False
                         else
                           k m i True |]
countWord = countWord0 0 False

[handler|
  StringReader a :: String -> a
    handles {ReadChar, Finished} where
      Return x   _       -> x
      ReadChar k []      -> k Nothing []
      ReadChar k (s : l) -> k (Just s) l      
      Finished k []      -> k True []
      Finished k l       -> k False l |]

wc :: ([handles|h {ReadChar}|], [handles|h {Finished}|]) => Comp h (Int, Int, Int)
wc = 
   do 
     ((lines, words), chars) <- countChar (countWord (loop 0))   
     return (chars, words, lines)
   where 
   loop i =   
     do
       b <- finished
       if b then return i
       else 
         do
           _ <- readLine  
           loop $! (i + 1)     
          
          
[operation|SaveLine :: String -> ()|]
[operation|PrintAll :: ()|]

[handler|
  forward h handles {Io}. 
    KeepAll0 a :: [String] -> Int -> a
      handles {SaveLine, PrintAll} where
        Return x      _ _ -> return x
        SaveLine s k  l i -> k () (s:l) i
        PrintAll   k  l i -> 
          do
            io (forM_ (take i l) putStrLn) 
            k () l i |]
keepAll = keepAll0 []

tailC :: ([handles|h {ReadChar}|], [handles|h {Finished}|],
          [handles|h {SaveLine}|], [handles|h {PrintAll}|]) => Comp h ()
tailC =
  do
    l <- readLine  
    saveLine l
    b <- finished
    if b then printAll else tailC
  
data CircularArray = CircularArray !Int !(IOArray Int String) !Int !Int

newCircularArray :: [handles|h {Io}|] => Int -> Comp h CircularArray
newCircularArray i = do
  a <- io (newArray (0, i - 1) []) 
  return (CircularArray i a 0 0)

push :: [handles|h {Io}|] => CircularArray -> String -> Comp h CircularArray
push (CircularArray length arr first next) s =                        
  do
    io (writeArray arr next s)
    let j = incrIdx length next 
    return (CircularArray length arr (if (j == first) then (incrIdx length first) else first) j)

incrIdx :: Int -> Int -> Int
incrIdx length i =
  let j = i + 1 in
  if (j < length) then j else 0

printAllCircularArray :: [handles|h {Io}|] => CircularArray -> Comp h ()
printAllCircularArray (CircularArray length arr first next) = 
    loop first
    where
      loop i = if (i == next) then return () 
               else do 
                      io ((readArray arr i) >>= putStrLn)
                      loop (incrIdx length i)

[handler|  
  forward h handles {Io}.
    CircularArrayH0 a :: CircularArray -> a 
      handles {SaveLine, PrintAll} where
        Return x     _ -> return x    
        SaveLine s k c -> push c s >>= k ()
        PrintAll   k c -> printAllCircularArray c >> k () c |]
circularArrayH i p = do
  c <- newCircularArray i
  circularArrayH0 c p

[handler| 
  forward h handles {Io}.
    StdinReader a :: a
      handles {ReadChar, Finished} where
        Return x -> return x
        ReadChar k -> 
          do
            b <- io (hIsEOF stdin)
            if b then k Nothing else io getChar >>= (k . Just)
        Finished k -> io (hIsEOF stdin) >>= k|]

tailStdin :: Int -> IO ()
tailStdin i = handleIO (stdinReader (circularArrayH (i+1) tailC))

wcStdin :: IO ()
wcStdin = do            
  (c, w, l) <- handleIO (stdinReader wc)
  putStrLn $ (show l) ++ " " ++ (show w) ++ " " ++ (show c)
              
main = wcStdin