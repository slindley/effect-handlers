fun id x = x
infixr |->
val filter = List.filter
val map = List.map
fun elemIndex x xs =
    let val rec elemIndex' =
	    fn i => fn x => fn xs =>
				   case xs of []      => NONE
					    | (y::xs) =>
					      if x=y then SOME i
					      else elemIndex' (i+1) x xs
    in
  	elemIndex' 0 x xs
    end
fun index xs =
    let val rec index' =
	 fn i => fn xs =>
		    case xs of []      => []
			     | (x::xs) => (i, x) :: index' (i+1) xs
    in
	index' 0 xs
    end

datatype player = Me | You

val (Move : (player * int, int) Op) = newOp ()
val move = applyOp Move

fun myTurn n =
    if n = 0 then You
    else yourTurn (n - move (Me, n))
and yourTurn n =
    if n = 0 then Me
    else myTurn (n - move (You, n))

val game = myTurn

fun perfect n k = k (Int.max (Int.mod (n, 4), 1))

fun pp n =
  Handle (fn () => game n)
  ([Move |-> (fn (_, n) => perfect n)], id)

fun validMoves n = filter (fn x => x <= n) [1,2,3]

fun bruteForce player n k =
    case (elemIndex player (map k (validMoves n))) of
	NONE   => k 1
      | SOME i => k (i+1)

fun bp n =
  Handle (fn () => game n)
  ([Move |-> (fn (player, n) =>
		 case player of
		     Me  => bruteForce Me n
		   | You => perfect n)],
   id)

datatype moveTree = Take of player * (int * moveTree) list | Winner of player

fun reifyMove player n k =
    Take (player, index (map k (validMoves n)))

fun mm n =
    Handle (fn () => game n)
    ([Move |-> (fn (player, n) =>
		   reifyMove player n)],
     fn x => Winner x)

val (YouMove : (int, int) Op) = newOp ()
val youMove = applyOp YouMove

fun mp n =
    Handle
    (fn () =>
	Handle (fn () => game n)
	       ([Move |-> (fn (player, n) =>
			   fn k =>
			      case player of
				  Me  => reifyMove Me n k
				| You =>
				  let val take = youMove n in
				      Take (You, [(take, k take)])
				  end)],
		Winner))
    ([YouMove |-> perfect],
     id)

datatype void = Void of void

fun undefined (Void x) = undefined x

val (Cheat : (player * int, void) Op) = newOp ()
fun cheat (player, n) = undefined (applyOp Cheat (player, n))

fun checkChoice player n k =
    let val take = move (player, n) in
	if (take < 0) orelse (3 < take) then cheat (player, take)
	else k take
    end

fun checkedGame n =
    Handle (fn () => game n)
    ([Move |-> (fn (player, n) => checkChoice player n)],
     id)

fun cheater n k = k n

fun cp n =
    Handle (fn () => game n)
    ([Move |-> (fn (player, n) =>
		   case player of
		       Me  => cheater n
		     | You => perfect n)],
     id)

datatype ('a, 'b) EndState = CleanWinner of 'a | Cheater of 'b

fun cheaterEndingGame n =
    Handle (fn () => checkedGame n)
    ([Cheat |-> (fn (player, n) => fn _ =>
				      Cheater (player, n))],
     CleanWinner)

fun cheaterLosingGame n =
    Handle (fn () => checkedGame n)
    ([Cheat |-> (fn (player, n) => fn _ => 
		    case player of
			Me  => You
		      | You => Me)],
     id)


fun cpEnding n =
    Handle (fn () => cheaterEndingGame n)
    ([Move |-> (fn (player, n) =>
		   case player of
		       Me  => cheater n
		     | You => perfect n)],
     id)

fun cpLosing n =
    Handle (fn () => cheaterLosingGame n)
    ([Move |-> (fn (player, n) =>
		   case player of
		       Me => cheater n
		     | You => perfect n)],
     id)
