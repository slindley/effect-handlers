(*
  Effect handlers for OCaml

  This implementation lies somewhere between the SML and Racket
  implementations. It takes advantage of Oleg Kiselyov's delimited
  continuations library for OCaml:

  http://okmij.org/ftp/continuations/implementations.html#delimcc-paper

  Currently we use some harmless Obj.magic. One might get rid of it
  using a more involved representation.
*)

module type EFF =
sig
  type 'a clause
  type ('p, 'r) op = 'p -> 'r

  type ('a, 'b) return_clause = 'a -> 'b
  type ('a, 'b) handler = 'b clause list * ('a, 'b) return_clause

  val new_op : unit -> ('p,'r) op

  val (|->) : ('p,'r) op -> ('p -> ('r -> 'a) -> 'a) -> 'a clause

  val shallow : ('p,'r) op -> ('p -> ('r -> 'a) -> 'a) -> 'a clause
  val local : ('p,'r) op -> ('p -> 'r) -> 'a clause
  val escape : ('p,'r) op -> ('p -> 'a) -> 'a clause

  val handle : (unit -> 'a) -> ('a, 'b) handler -> 'b

(*  val stack_size : unit -> int *)
end

module Eff : EFF =
struct
  open Delimcc

  let control0 p f = take_subcont p (fun sk () ->
    f (fun c -> push_subcont sk (fun () -> c)))

  type ('p, 'r) op = 'p -> 'r

  (* An effector interpets a handler as a function that given an
     operation and an argument dispatches to the appropriate operation
     clause with the current delimited continuation. *)
  type effector = {effector : 'p 'r.('p, 'r) op -> 'p -> 'r}

  type 'a clause = {clause : 'p 'r.(unit -> 'a) prompt -> effector -> ('p, 'r) op -> ('p -> 'r) option}
  type ('a, 'b) return_clause = 'a -> 'b
  type ('a, 'b) handler = 'b clause list * ('a, 'b) return_clause

  (* the stack of effectors represents the stack of handlers *)
  let effector_stack = ref []

  (* let stack_size () = List.length !effector_stack *)

  let push e = effector_stack := (e :: !effector_stack)
  let pop () =
    match !effector_stack with
      | []    -> failwith "unhandled operation"
      | e::es -> effector_stack := es
  let peek () =
    match !effector_stack with
      | []    -> None
      | e::es -> Some e

  let new_op_with_default default =
    let rec me p =
      (* the effector at the top of the stack handles this
         operation *)
      match peek() with
        | None          -> default p
        | Some effector -> effector.effector me p
    in
      me

  let new_op () = new_op_with_default (fun _ -> failwith "unhandled operation")
        
  (* Obj.magic is used to coerce quantified types to their concrete
     representations. Correctness is guaranteed by pointer equality on
     OCaml functions. If op and op' are equal then p and k must have
     types compatible with body. *)
  let (|->) op body =
    {clause = fun prompt effector op' ->
      if op == Obj.magic op' then
        Some (fun p ->
          shift0 prompt
            (fun k () -> 
              body (Obj.magic p)
                (fun x ->
                  push effector;
                  let result = Obj.magic k x () in
                    pop (); result)))
      else
        None}

  (* Shallow clauses are implemented with control0 instead of shift0.
     They correspond with Conor McBride's version of handlers in
     Frank. The key difference between shallow clauses and standard
     clauses is that the continuation is not automatically re-handled
     by a shallow clause. This functionality can be used to implement
     parameterised handlers. It can also be used to give
     implementations of prompt and prompt0 as handlers.

     Our current implementation of shallow clauses seems to have a
     severe memory leak.

     Parameterised handlers are easier to implement more
     efficiently and offer some of the benefits of shallow
     handlers. *)
  let shallow op body =
    {clause = fun prompt _effector op' ->
      if op == Obj.magic op' then
        Some (fun p ->
          control0 prompt
            (fun k () -> 
              body (Obj.magic p)
                (fun x -> Obj.magic k x ())))
      else
        None}

  (* A local clause can be used as an optimisation for direct-style
     operations that do not need to manipulate the continuation. *)
  let local op body =
    {clause = fun prompt _effector op' ->
      if op == Obj.magic op' then
        Some
          (fun p -> Obj.magic (body (Obj.magic p)))
      else
        None}

  (* An escape clause can be used as an optimisation for aborting
     operations (such as exceptions) that discard the continuation. *)
  let escape op body =
    {clause = fun prompt _effector op' ->
      if op == Obj.magic op' then
        Some
          (fun p ->
            abort prompt (fun () -> body (Obj.magic p)))
      else
        None}

  let effector_of_op_clauses prompt op_clauses =
    (* Morally an effector is just a recursive function. We use a
       record to get proper polymorphism, and value recursion to
       define the recursive function. *)
    let rec effector =
      {effector =
          let rec me op_clauses =
            fun op p ->
              match op_clauses with
                | [] ->
                  (* reinvoke an unhandled operation - to be handled
                     by an outer handler *)
                  pop ();
                  let result = op p in
                    (* push this effector back on the stack in order
                       to correctly handle any operations in the
                       continuation *)
                    push effector;
                    result
                | op_clause::op_clauses ->
                  begin
                    match op_clause.clause prompt effector op with
                      | None   -> me op_clauses op p
                      | Some f -> f p
                  end
          in
            (* eta expansion circumvents the value restriction *)
            fun op -> me op_clauses op}
    in
      effector

  let handle m (op_clauses, return_clause) =
    let prompt = new_prompt () in
    let effector = effector_of_op_clauses prompt op_clauses in
      push effector;
      let thunk =
        push_prompt prompt
          (fun () ->
            let result = m () in
              fun () -> return_clause result)
      in
        pop (); thunk ()
end 
   
open Eff

let get : (unit, int) op = new_op ()
let put : (int, unit) op = new_op ()

let handle_state s m =
  handle m
    ([get |-> (fun () k s -> k s s);
      put |-> (fun s  k _ -> k () s)],
     fun x s -> x) s

let handle_state_local s m =
  let r = ref s in
    handle m
      ([local get (fun () -> !r);
        local put (fun s  -> r := s)],
       fun x -> x)

let choice : (unit, bool) op = new_op ()

let nondeterminism m =
  handle m
    ([choice |-> (fun () k -> k true @ k false)],
     fun x -> [x])

let fail : (unit, 'a) op = new_op ()

let failure m =
  handle m
    ([fail |-> (fun () k -> None)],
     fun x -> Some x)

let fast_failure m =
  handle m
    ([escape fail (fun () -> None)],
     fun x -> Some x)

let rec shallow_state s m =
  handle m
    ([local   get (fun ()  -> s);
      shallow put (fun s k -> shallow_state s k)],
     fun x -> x)

let stop = new_op ()

let rec stupid n =
handle (fun () -> if n = 0 then stop () else n-1) 
  ([escape stop (fun () -> ())],
   (fun n -> stupid n))

let rec count : unit -> unit = fun () ->
  let n = get() in
    if n = 0 then ()
    else (put (n-1); count())

let rec repeat n =
  if n = 0 then ()
  else (let x = shallow_state 42 get in repeat (n-1))

(* let _ = shallow_state 10000 count *)
let _ = handle_state 1000000 count



