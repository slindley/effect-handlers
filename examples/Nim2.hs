-- The subtraction game (a variant of the game of nim).
--
-- A game begins with n sticks on the table. I go first. I take
-- between one and three sticks, then it is your turn, and you take
-- between one and three sticks. We alternate turns until we run out
-- of sticks. The winner is the player who takes the last stick.

{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction,
             FlexibleContexts, TypeOperators #-}

import Data.List
import Handlers

-- Operations:
--
--   choose (player, n) = m, if player chooses m out of the remaining n sticks

data Player = Me | You
  deriving (Show, Eq)

-- The 'Move' operation represents a move by a player in the game. The
-- parameter is a pair of the player and the number of sticks
-- remaining. The return value is the number of sticks the player
-- chooses to take.
data Move = Move
instance Op Move where
  type Param Move = (Player, Int)
  type Return Move = Int
move :: (Move `In` e) => (Player, Int) -> Comp e Int
move = applyOp Move

-- a game parameterised by the number of starting sticks
game :: (Move `In` e) => Int -> Comp e Player
game = myTurn

myTurn n =
  if n == 0 then return You
  else
    do
      take <- move (Me, n)
      yourTurn (n-take)
      
yourTurn n =
  if n == 0 then return Me
  else
    do
      take <- move (You, n)
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
  (Move |-> (\(_, n) -> perfect n) :<: Empty,
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
-- then move it. Otherwise just take 1 stick.
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
  (Move |-> (\(player, n) ->
                case player of
                  Me  -> bruteForce Me n
                  You -> perfect n) :<: Empty,
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
data MoveTree = Take (Player, [(Int, MoveTree)]) | Winner Player
  deriving Show

-- reify a move as part of a move tree
reifyMove :: Monad m => Player -> Int -> (Int -> m MoveTree) -> m MoveTree
reifyMove player n k =
  do
    l <- mapM k (validMoves n)
    return $ Take (player, zip [1..] l)
    
-- generate the complete move tree for a game starting with n sticks
mm :: Monad m => Int -> m MoveTree
mm n =
  handle (game n)
  (Move |-> (\(player, n) -> reifyMove player n) :<: Empty,
   \x -> return $ Winner x)

-- *Main> mm 3
-- Take (Me, [(1, Take (You, [(1, Take (Me, [(1,Winner Me)])),
--                            (2, Winner You)])),
--            (2, Take (You, [(1,Winner You)])),
--            (3, Winner Me)])

-- generate the move tree for a game in which you play a perfect
-- strategy
mp :: Monad m => Int -> m MoveTree
mp n =
  handle
  (handle (game n)
   (Move |-> (\(player, n) k ->
                 case player of
                   Me -> reifyMove Me n k
                   You ->
                     do
                       take <- move (You, n)
                       tree <- k take
                       return $ Take (You, [(take, tree)])) :<: Empty,
    \x -> return $ Winner x))
  (Move |-> (\(You, n) -> perfect n) :<: Empty,
   return)

-- *Main> mp 3
-- Take (Me, [(1, Take (You, [(2, Winner You)])),
--            (2, Take (You, [(1, Winner You)])),
--            (3, Winner Me)])
   
-- an uninhabited type
data Void

-- cheat (p, m) is invoked when player p cheats by attempting to take
-- m sticks (for m < 1 or 3 < m)
data Cheat = Cheat
instance Op Cheat where
  type Param Cheat = (Player, Int) 
  type Return Cheat = Void
cheat :: (Cheat `In` e) => (Player, Int) -> Comp e a
cheat (p, m) = (applyOp Cheat (p, m)) >>= undefined

-- a checked choice
--
-- If the player chooses a valid number of sticks, then the game
-- continues. If not, then the cheat operation is invoked.
checkChoice :: (Move `In` e, Cheat `In` e) =>
               Player -> Int -> (Int -> Comp e a) -> Comp e a
checkChoice player n k =
  do
    take <- move (player, n)
    if take < 0 || 3 < take then cheat (player, take)
    else k take

-- a game that checks for cheating
checkedGame :: (Move `In` e, Cheat `In` e) => Int -> Comp e Player
checkedGame n =
  handle
  (game n)
  (Move |-> (\(player, n) -> checkChoice player n) :<: Empty,
   return)

-- a cheating strategy: take all of the sticks, no matter how many
-- remain
cheater n k = k n

-- I cheat against your perfect strategy
-- (I always win)
cp n =
  handle (game n)
  (Move |-> (\(player, n) -> 
                case player of
                  Me -> cheater n 
                  You -> perfect n) :<: Empty,
   return)

-- *Main> cp 32
-- Me

-- a game in which cheating leads to the game being abandoned, and the
-- cheater is reported along with how many sticks they attempted to
-- take
cheaterEndingGame :: (Move `In` e) => Int -> Comp e Player
cheaterEndingGame n =
  handle (checkedGame n)
  (Move -:<:
   Cheat |-> (\(p, n) _ -> error ("Cheater: " ++ show p ++ ", took: " ++ show n)) :<: Empty,
   return)

-- a game in which if I cheat then you win immediately, and if you
-- cheat then I win immediately
cheaterLosingGame :: (Move `In` e) => Int -> Comp e Player
cheaterLosingGame n =
  handle (checkedGame n)
  (Move -:<:
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
  (Move |-> (\(player, n) ->
                case player of
                  Me -> cheater n  
                  You -> perfect n) :<: Empty,
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
  (Move |-> (\(player, n) ->
                case player of
                  Me -> cheater n
                  You -> perfect n) :<: Empty,
   return)

-- *Main> cpLosing 3
-- Me
-- *Main> cpLosing 5
-- You
