(*
  McBride handlers in OCaml using Oleg's implementation of
  control0 and prompt0 in terms of shift and reset.

  This implementation of control0 has the same memory leak problems as
  the more direct one.
*)

module Control0 =
struct
  type ('a, 'r) cont = H of ('a -> 'r) * (('a -> 'r) -> 'r) | HV of 'r
  type ('a, 'r) prop_prompt = (('a, 'r) cont) Delimcc.prompt

  type 'r stop_prompt = 'r Delimcc.prompt

  let hr_stop : 'r stop_prompt -> ('a, 'r) cont -> 'r =
    fun prompt ->
      function
        | (H (f, x)) -> Delimcc.push_prompt prompt (fun () -> x f)
        | (HV x)     -> x
  let hs_stop = hr_stop
    
  let hr_prop : ('a, 'r) prop_prompt -> ('a, 'r) cont -> 'r =
    fun _prompt ->
      function
        | (H (f, x)) -> x f
        | (HV x)     -> x
            
  let rec hs_prop : ('a, 'r) prop_prompt -> ('a, 'r) cont -> 'r =
    fun prompt ->
      function
        | (H (f, x)) -> Delimcc.shift prompt (fun g -> H ((fun y -> hs_prop prompt (g (f y))), x))
        | (HV x)     -> x

  let prompt0 : ('a, 'r) prop_prompt -> (unit -> 'r) -> 'r =
    fun prompt e ->
      hr_prop prompt (Delimcc.push_prompt prompt (fun () -> HV (e ())))
  let control0 : ('a, 'r) prop_prompt -> (('a -> 'r) -> 'r) -> 'a =
    fun prompt c ->
      Delimcc.shift prompt (fun k -> H ((fun x -> hs_prop prompt (k x)), c))
end

module type EFF =
sig
  type 'a clause
  type ('p, 'r) op = 'p -> 'r

  type ('a, 'b) return_clause = 'a -> 'b
  type ('a, 'b) handler = 'b clause list * ('a, 'b) return_clause

  val new_op : unit -> ('p,'r) op

  val (|->) : ('p,'r) op -> ('p -> ('r -> 'a) -> 'a) -> 'a clause

  val handle : (unit -> 'a) -> ('a, 'b) handler -> 'b

  val stack_size : unit -> int
end

module Eff : EFF =
struct
  open Delimcc
  open Control0

  let control0' p f = take_subcont p (fun sk () ->
                                        f (fun c -> push_subcont sk (fun () -> c)))

  type ('p, 'r) op = 'p -> 'r

  (* An effector interpets a handler as a function that given an
     operation and an argument dispatches to the appropriate operation
     clause with the current delimited continuation. *)
  type effector = {effector : 'p 'r.('p, 'r) op -> 'p -> 'r}

  type 'a clause = {clause : 'p 'r.('r, unit -> 'a) prop_prompt -> effector -> ('p, 'r) op -> ('p -> 'r) option}
  type ('a, 'b) return_clause = 'a -> 'b
  type ('a, 'b) handler = 'b clause list * ('a, 'b) return_clause

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
        | Some effector -> effector.effector me p
    in
      me

  let new_op () = new_op_with_default (fun _ -> failwith "unhandled operation")

  let (|->) op body =
    {clause = fun prompt effector op' ->
      if op == Obj.magic op' then
        Some (fun p ->
          control0 prompt
            (fun k () -> 
              body (Obj.magic p)
                (fun x -> Obj.magic k x ())))
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
                  let result = op p in
                    (* push this effector back on the stack in order
                       to correctly handle any operations in the
                       continuation *)
                    push effector;
                    result
                | op_clause::op_clauses ->
                    begin
                      match op_clause.clause (Obj.magic prompt) effector op with
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
        prompt0 prompt
          (fun () ->
             let result = m () in
              fun () -> return_clause result)
      in
        pop (); thunk ()
end 
   
open Eff

let get : (unit, int) op = new_op ()
let put : (int, unit) op = new_op ()

let rec mcbride_state s m =
  handle m
    ([get |-> (fun () k -> mcbride_state s (fun () -> k s));
      put |-> (fun s  k -> mcbride_state s (fun () -> k ()))],
     fun x -> x)

let rec count : unit -> unit = fun () ->
  let n = get() in
    if n = 0 then ()
    else (put (n-1); count())

(* mcbride_state 1000 count eats up memory *)
