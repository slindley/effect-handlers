(*
  Effect handlers for OCaml

  This implementation lies somewhere between the SML and Racket
  implementations. It takes advantage of Oleg Kiselyov's delimited
  continuations library for OCaml:

  http://okmij.org/ftp/continuations/implementations.html#delimcc-paper

  Currently we use some harmless Obj.magic. One might get rid of it
  using existentials or using GADTs in OCaml 4.
*)

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
  (* open the delimited continuation library *)
  open Delimcc

  type ('p, 'r) op = 'p -> 'r

  type effector = {effector : 'p 'r.('p, 'r) op -> 'p -> 'r}

  type 'a clause = {clause : 'p 'r.'a prompt -> effector -> ('p, 'r) op -> ('p -> 'r) option}
  type ('a, 'b) return_clause = 'a -> 'b
  type ('a, 'b) handler = 'b clause list * ('a, 'b) return_clause

  let effector_stack = ref []

  let stack_size () = List.length (!effector_stack)

  let push e = effector_stack := (e :: !effector_stack)
  let pop () =
    match !effector_stack with
      | []    -> failwith "unhandled operation"
      | e::es -> effector_stack := es; e

  let new_op () =
    let rec me p =
      (pop ()).effector me p
    in
      me
        
  let (|->) op body =
    {clause = fun prompt effector op' ->
      if op == Obj.magic op' then
        Some (fun p ->
          shift0 prompt
            (fun k ->
              body (Obj.magic p)
                (fun x -> push effector; Obj.magic k x)))
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
      push_prompt prompt
        (fun () ->
          let result =  m () in
          let _ = pop () in
            return_clause result)
end 

open Eff

let get : (unit, int) op = new_op ()
let put : (int, unit) op = new_op ()

let state_handler s m =
  handle m
    ([get |-> (fun () k s -> k s s);
      put |-> (fun s  k _ -> k () s)],
     fun x s -> x) s

let choice : (unit, bool) op = new_op ()

let nondeterminism m =
  handle m
    ([choice |-> (fun p k -> k true @ k false)], fun x -> [x])

