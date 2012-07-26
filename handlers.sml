(*
 Effect handlers for SML

 By Ohad Kammar, Sam Lindley and Nicolas Oury

 See the draft paper:

   http://homepages.inf.ed.ac.uk/slindley/papers/handlers.pdf

 for further details.
*)

signature EFF =
sig
  type 'a clause
  type ('p, 'r) Op

  type 'a opHandler = 'a clause list
  type ('a, 'b) retHandler = 'a -> 'b 
  type ('a, 'b) handler = 'b opHandler * ('a, 'b) retHandler

  val newOp : unit -> ('p,'r) Op
  val applyOp : ('p, 'r) Op -> 'p -> 'r

  val |-> : ('p,'r) Op * ('p -> ('r -> 'a) -> 'a) -> 'a clause

  val Handle               : (unit -> 'a) -> ('a, 'b) handler -> 'b
  val handleFinally        : (unit -> 'a) -> ('a, 'b) handler -> ('b -> 'c) -> 'c

  (* the following probably shouldn't be part of the interface *)
  val handleEffect         : 'a opHandler ->                             (unit -> 'a) -> 'a
  val withReturn           : 'b opHandler -> ('a -> 'b) ->               (unit -> 'a) -> 'b
  val withReturnAndFinally : 'b opHandler -> ('a -> 'b) -> ('b -> 'c) -> (unit -> 'a) -> 'c
end

structure Eff :> EFF =
struct
  open SMLofNJ.Cont

  type unitThunk = unit -> unit
  type unitThunks = unitThunk list
                
  exception Effect of unitThunks

  type 'a clause = unitThunks -> (unit -> 'a) cont ref -> unit
  type 'a opHandler = 'a clause list
  type ('a, 'b) retHandler = 'a -> 'b 
  type ('a, 'b) handler = 'b opHandler * ('a, 'b) retHandler

  type ('p,'r) effect = {param:'p option ref, k:'r cont option ref}

  type ('p, 'r) Op = ('p -> 'r) * ('p, 'r) effect

  val (stack : unitThunks ref) = ref []

  fun push thunk = stack := (thunk :: !stack)
  fun pop () = let val (thunk :: rest) = !stack in
                   stack := rest;
                   thunk
               end

  fun popAndRun () = pop()()
  fun pushMany thunks = List.app push thunks

  (* implementation details *)
  (* val makeComposable : unitThunks -> 'r cont -> (unit -> 'a) cont ref -> ('r -> 'a) *)
  (* val rawEffect : unit -> ('p,'r) effect *)
  (* val throwEffect : ('p,'r) effect -> 'p -> 'r *)

  fun makeComposable thunks k kr r =
      callcc (fn k' =>
                 (push (fn () => kr := k');
                  pushMany thunks;
                  throw k r)) ()

  fun rawEffect () = {param = ref NONE, k = ref NONE}
  fun throwEffect {param=pr, k=kr} p =
      callcc (fn k' =>
                 (pr := SOME p;
                  kr := SOME k';
                  raise Effect []))

  fun newOp () = let val e = rawEffect() in (throwEffect e, e) end

  fun applyOp (f, _) = f
  
  infixr |->
  
  fun (_, {param=pr, k=krr}) |-> f = fn thunks => fn kra =>
      case !pr of
          NONE   => ()
        | SOME p =>
          let val SOME kr = !krr in
              pr := NONE;
              krr := NONE;
              throw (!kra) (fn () => f p (makeComposable thunks kr kra))
          end

  fun handleEffect hs comp =
      callcc (fn k =>
                 throw (isolate
                            (let val kr = ref k
                                 val () = push (fn () => kr := k)
                                 val result =
                                     comp ()
                                     handle Effect thunks =>
                                            let val thunk = pop() in
                                                thunk(); (* restore return point into kr from the stack *)
                                                List.app (fn h => h thunks kr) hs;
                                                (throw (!kr) (fn () =>
                                                                 raise Effect (thunk :: thunks)))
                                            end
                             in
                                 popAndRun();
                                 throw (!kr) (fn () => result)
                             end))) ()
  fun withReturn hs f thunk =
      handleEffect hs (f o thunk)
  fun withReturnAndFinally hs f g thunk =
      g (withReturn hs f thunk)

  fun Handle thunk (hs, r) = withReturn hs r thunk
  fun handleFinally thunk (hs, r) f = withReturnAndFinally hs r f thunk
end
