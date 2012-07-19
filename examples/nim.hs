-- The subtraction game (a variant of the game of nim).
--
-- A game begins with n sticks on the table. I take the first turn. I
-- take between one and three sticks, then it is your turn, and you
-- take between one and three sticks. We alternate turns until we run
-- out of sticks. The winner is the player who takes the last stick.

{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction,
             FlexibleContexts, TypeOperators #-}

import Data.List
import Handlers

-- Operations:
--
--   ichoose n = m, if I choose m out of the remaining n sticks
--   uchoose n = m, if you choose m out of the remaining n sticks

data IChoose = IChoose
instance Op IChoose where
  type Param IChoose = Int
  type Return IChoose = Int
iChoose = applyOp IChoose

data UChoose = UChoose
instance Op UChoose where
  type Param UChoose = Int
  type Return UChoose = Int
uChoose = applyOp UChoose

data Player = Me | You
  deriving (Show, Eq)

-- a game parameterised by the number of starting sticks
game :: (IChoose `In` e, UChoose `In` e) => Int -> Comp e Player
game = myTurn

myTurn n =
  if n == 0 then return You
  else
    do
      take <- iChoose n
      yourTurn (n-take)
      
yourTurn n =
  if n == 0 then return Me
  else
    do
      take <- uChoose n
      myTurn (n-take)

-- Note that this implementation does not check that each player takes
-- between one and three sticks on each turn. We will add such a check
-- later.

-- a perfect strategy given n remaining sticks (represented as an
-- operation clause)
perfect :: Monad m => Int -> (Int -> m a) -> m a
perfect n k = k (max (n `mod` 4) 1)

-- perfect vs perfect
pp :: Monad m => Int -> m Player
pp n =
  handle (game n)
  (IChoose |-> perfect :<: UChoose |-> perfect :<: Empty,
   return)

-- *Main> pp 3
-- Me
-- *Main> pp 29
-- Me
-- *Main> pp 32
-- You

-- list of valid moves given n sticks remaining
validMoves :: Int -> [Int]
validMoves n = filter (<= n) [1,2,3]

-- a brute force strategy
--
-- Enumerate all the moves. If one of them leads to a win for player,
-- then choose it. Otherwise just take 1 stick.
bruteForce :: Monad m => Player -> Int -> (Int -> m Player) -> m Player
bruteForce player n k =
  do
    winners <- mapM k (validMoves n)
    case (elemIndex player winners) of
      Nothing -> k 1
      Just i  -> k (i+1)

-- brute force vs perfect
bp :: Monad m => Int -> m Player
bp n =
  handle (game n)
  (IChoose |-> bruteForce Me :<: UChoose |-> perfect :<: Empty,
   return)

-- bruteForce behaves just the same as the perfect strategy, except it
-- is much slower

-- *Main> bp 3
-- Me
-- *Main> bp 31
-- Me
-- *Main> bp 32
-- You

-- Instead of simply evaluating the winner according to some strategy,
-- we can also compute other data. For instance, we can compute a tree
-- representing the possible moves of each player.

-- a tree encoding possible moves
data MoveTree = ITake [(Int, MoveTree)] | UTake [(Int, MoveTree)] | Winner Player
  deriving Show

-- reify a move as part of a move tree
reifyMove :: Monad m => Player -> Int -> (Int -> m MoveTree) -> m MoveTree
reifyMove player n k =
  do
    let play =
          case player of
            Me  -> ITake
            You -> UTake
    l <- mapM k (validMoves n)
    return $ play (zip [1..] l)
    
-- generate the complete move tree for a game starting with n sticks
mm :: Monad m => Int -> m MoveTree
mm n =
  handle (game n)
  (IChoose |-> reifyMove Me :<: UChoose |-> reifyMove You :<: Empty,
   \x -> return $ Winner x)

-- *Main> mm 3
-- ITake [(1,UTake [(1,ITake [(1,Winner Me)]),(2,Winner You)]),(2,UTake [(1,Winner You)]),(3,Winner Me)]

-- generate the move tree for a game in which you play a perfect
-- strategy
mp :: Monad m => Int -> m MoveTree
mp n =
  handle
  (handle (game n)
   (IChoose |-> reifyMove Me :<:
    UChoose |-> (\n k ->
                  do
                    take <- uChoose n 
                    tree <- k take
                    return $ UTake [(take, tree)]) :<: Empty,
    \x -> return $ Winner x))
  (UChoose |-> perfect :<: Empty,
   return)

-- *Main> mp 3
-- ITake [(1,UTake [(2,Winner You)]),(2,UTake [(1,Winner You)]),(3,Winner Me)]

-- an uninhabited type
data Void

-- cheat (p, m) is invoked when player p cheats by attempting to take
-- m sticks (for m < 1 or 3 < m)
data Cheat = Cheat
instance Op Cheat where
  type Param Cheat = (Player, Int) 
  type Return Cheat = Void
cheat (p, m) = (applyOp Cheat (p, m)) >>= undefined

-- a checked choice
--
-- If the player chooses a valid number of sticks, then the game
-- continues. If not, then the cheat operation is invoked.
checkChoice :: (IChoose `In` e, UChoose `In` e, Cheat `In` e) =>
               Player -> Int -> (Int -> Comp e a) -> Comp e a
checkChoice player n k = 
  do
    let ch =
          case player of
            Me  -> iChoose
            You -> uChoose
    take <- ch n
    if take < 0 || 3 < take then cheat (player, take)
    else k take

-- a game that checks for cheating
checkedGame :: (IChoose `In` e, UChoose `In` e, Cheat `In` e) => Int -> Comp e Player
checkedGame n =
  handle
  (game n)
  (IChoose |-> checkChoice Me :<: UChoose |-> checkChoice You :<: Empty,
   return)

-- a cheating strategy: take all of the sticks, no matter how many
-- remain
cheater n k = k n

-- I cheat against your perfect strategy
-- (I always win)
cp n =
  handle (game n)
  (IChoose |-> cheater :<: UChoose |-> perfect :<: Empty,
   return)

-- *Main> cp 32
-- Me

-- a game in which cheating leads to the game being abandoned, and the
-- cheater is reported along with how many sticks they attempted to
-- take
cheaterEndingGame :: (IChoose `In` e, UChoose `In` e) => Int -> Comp e Player
cheaterEndingGame n =
  handle (checkedGame n)
  (IChoose -:<: UChoose -:<:
   Cheat |-> (\(p, n) _ -> error ("Cheater: " ++ show p ++ ", took: " ++ show n)) :<: Empty,
   return)

-- a game in which if I cheat then you win immediately, and if you
-- cheat then I win immediately
cheaterLosingGame :: (IChoose `In` e, UChoose `In` e) => Int -> Comp e Player
cheaterLosingGame n =
  handle (checkedGame n)
  (IChoose -:<: UChoose -:<:
   Cheat |-> (\(p, n) _ -> 
               case p of
                 Me -> return You
                 You -> return Me) :<: Empty,
   return)

-- I cheat against your perfect strategy
--
-- (If n < 4 then I win, otherwise the game is abandoned because I
-- cheat.)
cpEnding n =
  handle (cheaterEndingGame n)
  (IChoose |-> cheater :<: UChoose |-> perfect :<: Empty,
   return)

-- *Main> cpEnding 3
-- Me
-- *Main> cpEnding 5
-- *** Exception: Cheater: Me, took: 5

-- I cheat against your perfect strategy
--
-- (If n < 4 then I win, otherwise you win because I cheat.)
cpLosing n =
  handle (cheaterLosingGame n)
  (IChoose |-> cheater :<: UChoose |-> perfect :<: Empty,
   return)

-- *Main> cpLosing 3
-- Me
-- *Main> cpLosing 5
-- You
