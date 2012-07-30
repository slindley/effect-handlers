(*
  Parameterised effect handlers for OCaml.
*)

module type EFF =
sig
  type ('a, 'h) clause
  type ('p, 'r) op = 'p -> 'r

  type ('a, 'b) return_clause = 'a -> 'b
  type ('a, 'b, 'h) handler = ('h -> ('b, 'h) clause list) * ('a, 'b) return_clause

  type ('a, 'b) plain_handler = ('b, unit) clause list * ('a, 'b) return_clause

  val new_op : unit -> ('p,'r) op

  val (|->) : ('p,'r) op -> ('p -> ('h -> 'r -> 'a) -> 'a) -> ('a, 'h) clause

  val plain : ('p,'r) op -> ('p -> ('r -> 'a) -> 'a) -> ('a, 'h) clause
  val mcbride : ('p,'r) op -> ('p -> ('r -> 'a) -> 'a) -> ('a, 'h) clause
  val local : ('p,'r) op -> ('p -> 'r) -> ('a, 'h) clause
  val escape : ('p,'r) op -> ('p -> 'a) -> ('a, 'h) clause

  val handle : (unit -> 'a) -> ('a, 'b, 'h) handler -> 'h -> 'b
  val handle_plain : (unit -> 'a) -> ('a, 'b) plain_handler -> 'b

  val stack_size : unit -> int
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
  type effector = {active : 'p 'r.('p, 'r) op -> 'p -> 'r;
                   template : 'h 'p 'r.'h -> ('p, 'r) op -> 'p -> 'r}

  type ('a, 'h) clause = {clause : 'p 'r.('h -> 'a) prompt -> effector -> ('p, 'r) op -> ('p -> 'r) option}
  type ('a, 'b) return_clause = 'a -> 'b
  type ('a, 'b, 'h) handler = ('h -> ('b, 'h) clause list) * ('a, 'b) return_clause

  type ('a, 'b) plain_handler = ('b, unit) clause list * ('a, 'b) return_clause

  (* the stack of effectors represents the stack of handlers *)
  let effector_stack = ref []

  let stack_size () = List.length !effector_stack

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
        | Some effector -> effector.active me p
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
            (fun k h -> 
              body
                (Obj.magic p)
                (fun h x ->
                   push {effector with active = Obj.magic (effector.template h)};
                   let result = Obj.magic k x h in
                     pop (); result)))
      else
        None}

  let plain op body =
    {clause = fun prompt effector op' ->
       if op == Obj.magic op' then
         Some (fun p ->
          shift0 prompt
            (fun k h -> 
               body
                 (Obj.magic p)
                 (fun x ->
                    push {effector with active = Obj.magic (effector.template h)};
                    let result = Obj.magic k x h in
                      pop (); result)))
       else
         None}

  (* McBride clauses are implemented with control0 instead of shift0.
     They correspond with Conor McBride's version of handlers in
     Frank. The key difference between McBride clauses and standard
     clauses is that the continuation is not automatically re-handled
     by a McBride clause. This functionality can be used to implement
     parameterised handlers. It can also be used to give
     implementations of prompt and prompt0 as handlers.

     Our current implementation of McBride clauses seems to have a
     severe memory leak.

     Perhaps parameterised handlers are easier to implement more
     efficiently and offer most of the benefits of McBride
     handlers. *)
  let mcbride op body =
    {clause = fun prompt effector op' ->
      if op == Obj.magic op' then
        Some (fun p ->
          control0 prompt
            (fun k h ->
              body (Obj.magic p)
                (fun x -> Obj.magic k x h)))
      else
        None}

  (* A local clause can be used as an optimisation for direct-style
     operations that do not need to manipulate the continuation. *)
  let local op body =
    {clause = fun prompt effector op' ->
      if op == Obj.magic op' then
        Some
          (fun p -> Obj.magic (body (Obj.magic p)))
      else
        None}

  (* An escape clause can be used as an optimisation for aborting
     operations (such as exceptions) that discard the continuation. *)
  let escape op body =
    {clause = fun prompt effector op' ->
      if op == Obj.magic op' then
        Some
          (fun p ->
            abort prompt (fun h -> body (Obj.magic p)))
      else
        None}

  let effector_of_op_clauses h prompt op_clauses =
    (* Morally an effector is just a recursive function. We use a
       record to get proper polymorphism, and value recursion to
       define the recursive function. *)
    let rec effector =
      let rec me h op_clauses =
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
                  push {effector with active = Obj.magic (effector.template h)};
                  result
            | op_clause::op_clauses ->
                begin
                  match op_clause.clause prompt effector op with
                    | None   -> me h op_clauses op p
                    | Some f -> f p
                end
      in
        (* eta expansion circumvents the value restriction *)
        {active = (fun op -> me h (op_clauses h) op);
         template = (fun h -> me h (Obj.magic (op_clauses) h))}
    in 
      effector

  let handle m (op_clauses, return_clause) h =
    let prompt = new_prompt () in
    let effector = effector_of_op_clauses h prompt op_clauses in
      push effector;
      let thunk =
        push_prompt prompt
          (fun () ->
            let result = m () in
              fun _ -> return_clause result)
      in
        pop (); thunk h

  let handle_plain m (op_clauses, return_clause) =
    handle m ((fun () -> op_clauses), return_clause) ()
end 
   
open Eff

let get : (unit, int) op = new_op ()
let put : (int, unit) op = new_op ()

let parameterised_state s m =
  handle m
    ((fun s ->
        [local get (fun () -> s);
         put |-> (fun s  k -> k s ())]),
     (fun x -> x))
    s

let rec mcbride_state s m =
  handle m
    ((fun () ->
        [local   get (fun ()  -> s);
         mcbride put (fun s k -> mcbride_state s k)]),
     (fun x -> x)) ()

let handle_state s m =
  handle_plain m
    ([plain get (fun () k s -> k s s);
      plain put (fun s  k _ -> k () s)],
     fun x s -> x) s

let handle_state_local s m =
  let r = ref s in
    handle_plain m
      ([local get (fun () -> !r);
        local put (fun s  -> r := s)],
       fun x -> x)

(* let choice : (unit, bool) op = new_op () *)

(* let nondeterminism m = *)
(*   handle m *)
(*     ([choice |-> (fun () k -> k true @ k false)], *)
(*      fun x -> [x]) *)

let fail : (unit, 'a) op = new_op ()

let failure m =
  handle_plain m
    ([plain fail (fun () k -> None)],
     fun x -> Some x)

let fast_failure m =
  handle_plain m
    ([escape fail (fun () -> None)],
     fun x -> Some x)

let stop = new_op ()
let rec stupid n =
  handle_plain (fun () -> if n = 0 then stop () else n-1)
    ([escape stop (fun () -> ())],
     (fun n -> stupid n))

let rec count : unit -> unit =
  fun () ->
    let n = get() in
      if n = 0 then ()
      else (put (n-1); count())

(* let rec repeat n = *)
(*   if n = 0 then () *)
(*   else (let x = mcbride_state 42 get in repeat (n-1)) *)

(* (\* let _ = mcbride_state 10000 count *\) *)
