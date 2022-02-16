open Core
open Hashcons

module T = struct
  type frame = Id.t * Id.t [@@deriving hash, equal]

  type op = Push | Co_pop [@@deriving hash, equal]

  type stack = Cons of { prev : t; op : op; frame : frame } | Empty

  and t = stack Hashcons.hash_consed
end
(* When symbolic executing, we create counter on the fly.
   However, when relativize, we lose the info on the counter.

   Two solution to solve this:
   1. Keep the stack-tree, which is the collection of all the possible stacks.
   Thus, any concrete stacks can be treated as _paths_ on the tree.
   We can retrieve the nodes as needed.
   The pro is the counter is simple. The con is to maintain the tree.
   2. Use hashcons. We use hash-cons instead of the counter.
   The pro is the hashcons is a standard way. The con is slightly heavier than the counter.
*)

module X = struct
  open T

  type t = T.stack

  let equal t1 t2 =
    match (t1, t2) with
    | Empty, Empty -> true
    | Cons cell1, Cons cell2 ->
        T.equal_op cell1.op cell2.op
        && T.equal_frame cell1.frame cell2.frame
        && phys_equal cell1.prev cell2.prev
    | _, _ -> false

  let hash = function
    | Empty -> Hashtbl.hash Empty
    | Cons { op; frame; prev } ->
        (prev.tag * 19) + (T.hash_frame frame * 7) + T.hash_op op
end

module H = Hashcons.Make (X)
include T

type t = T.t

let ht = H.create 100

let empty = H.hashcons ht Empty

let cons op prev frame = H.hashcons ht (Cons { op; prev; frame })

let push rstk frame = cons Push rstk frame

let pop (rstk : t) frame : t option =
  match rstk.node with
  | Empty ->
      (* TODO: what if starting from a then-block *)
      Some (cons Co_pop rstk frame)
  | Cons { op = Push; prev; frame = frame_prev } ->
      let f1, _ = frame in
      let f2, _ = frame_prev in
      if Id.equal f1 f2 then
        Some prev
      else (* failwith "unmathch pop from stk" *)
        None
  | Cons { op = Co_pop; _ } -> Some (cons Co_pop rstk frame)

let paired_callsite rstk this_f =
  match rstk.node with
  | Empty -> None
  | Cons { op = Push; frame; _ } ->
      let cs, fid = frame in
      if Id.equal fid this_f then
        Some cs
      else
        failwith "inequal f when stack is not empty"
  | Cons { op = Co_pop; _ } -> None

let rec concretize_top rstk =
  match rstk.node with
  | Empty -> []
  | Cons { op = Co_pop; prev; frame } -> frame :: concretize_top prev
  | _ -> failwith "non-empty stack when concretize"

let relativize (target_stk : Concrete_stack.t) (call_stk : Concrete_stack.t) : t
    =
  let rec discard_common ts cs =
    match (ts, cs) with
    | fm1 :: ts', fm2 :: cs' ->
        if equal_frame fm1 fm2 then
          discard_common ts' cs'
        else
          (ts, cs)
    | _, _ -> (ts, cs)
  in
  (* Reverse the call stack to make it stack top ~ list head ~ source first *)
  let call_rev = List.rev call_stk in
  let target_stk', call_stk' = discard_common target_stk call_rev in
  (* (target_stk', List.rev call_stk') *)
  let rstk' =
    List.fold (List.rev target_stk') ~init:empty ~f:(fun acc fm ->
        Option.value_exn (pop acc fm))
  in
  let rstk = List.fold (List.rev call_stk') ~init:rstk' ~f:push in
  rstk

let str_of_frame (Id.Ident x1, Id.Ident x2) = "(" ^ x1 ^ "," ^ x2 ^ ")"

let str_of_op = function Push -> "<-" | Co_pop -> "!"

let str_of_t h = string_of_int h.hkey

let construct_stks r_stk =
  let rec loop r_stk co_stk stk =
    match r_stk.node with
    | Empty -> (co_stk, stk)
    | Cons { op = Co_pop; prev; frame } -> loop prev (frame :: co_stk) stk
    | Cons { op = Push; prev; frame } -> loop prev co_stk (frame :: stk)
  in
  loop r_stk [] []

let rec pp oc rstk =
  match rstk.node with
  | Empty -> ()
  | Cons { op = Co_pop; prev; frame } ->
      Fmt.pf oc "-%s;%a" (str_of_frame frame) pp prev
  | Cons { op = Push; prev; frame } ->
      Fmt.pf oc "+%s;%a" (str_of_frame frame) pp prev

(*
let str_of_id h = str_of_id (lift_to_stack h)

   let rec lift_to_hstack = function
     | Empty -> empty
     | Cons { prev; op; frame } -> cons op (lift_to_hstack prev) frame

   let rec lift_to_stack h =
     match h.node with
     | Empty -> Empty
     | Cons { prev; op; frame } -> Cons { op; frame; prev = lift_to_stack prev }

   let stack_of_sexp s =
     let node = t_of_sexp s in
     let hnode = lift_to_hstack node in
     hnode

   let sexp_of_stack (h : stack) =
     let node = lift_to_stack h in
     sexp_of_t node

   let rec compare_stack (h1 : stack) (h2 : stack) =
     match (h1.node, h2.node) with
     | Empty, Empty -> 0
     | Cons cell1, Cons cell2 ->
         Std.chain_compare
           (fun () ->
             Std.chain_compare
               (fun () -> T.compare_op cell1.op cell2.op)
               (fun () -> T.compare_frame cell1.frame cell2.frame))
           (fun () -> compare_stack cell1.prev cell2.prev)
     | Empty, _ -> -1
     | _, Empty -> 1

   let equal_stack (h1 : stack) (h2 : stack) = X.equal h1.node h2.node

   let hasfold_stack state (stack : stack) =
     match stack.node with
     | Empty -> Hash.fold_int state 0
     | Cons { prev; op; frame } ->
         Hash.fold_int (T.hasfold_op (T.hasfold_frame state frame) op) prev.tag *)