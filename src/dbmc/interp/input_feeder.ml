open Core
open Dj_common

type t = Id.t * Concrete_stack.t -> int

let from_list ?(default = 42) inputs ?(history = ref inputs) : t =
 fun _ ->
  let r = List.hd_exn !history in
  history := List.tl_exn !history ;
  match r with Some i -> i | None -> default

let memorized_from_list ?(default = 42) inputs
    (history : (Id.t * Concrete_stack.t * int option) list ref) : t =
  let inputs = ref inputs in
  fun (x, stk) ->
    let r = List.hd_exn !inputs in
    inputs := List.tl_exn !inputs ;
    history := !history @ [ (x, stk, r) ] ;
    match r with Some i -> i | None -> default

let query_model model target_stack (x, call_stack) : int option =
  let stk = Rstack.relativize target_stack call_stack in

  Format.printf "Target stack: %s\n" (Concrete_stack.to_string target_stack);
  Format.printf "Call stack: %s\n" (Concrete_stack.to_string call_stack);
  Format.printf "Relativized stack: %s\n" (Rstack.to_string stk);
  Format.printf "Call stack in R-stack string form: %s\n" (call_stack |> Rstack.from_concrete |> Rstack.to_string);

  let name = Lookup_key.to_str2 x stk in
  let other_name = Lookup_key.to_str2 x (call_stack |> Rstack.from_concrete) in 

  Format.printf "Query name: %s\n" name;
  Format.printf "Dumped model:\n";
  Solver.SuduZ3.dump_model model;

  (* Solver.SuduZ3.get_int_s model name *)
  Solver.SuduZ3.get_int_s model other_name


let from_model ?(history = ref []) model target_stack : t =
  let input_feeder = query_model model target_stack in
  fun query ->
    let answer = input_feeder query in
    history := answer :: !history ;
    Option.value ~default:42 answer


(* 
let query_model_new model target_stack ctx (x, call_stack) : int option = 
  let stk = Rstack.relativize target_stack call_stack in
  let name = Lookup_key.to_str2 x stk in
  let new_name = String.split_on_chars ~on:['_'] name |> List.rev |>  List.tl_exn |> List.rev |> String.concat ~sep:"_" in 
  let x_sym = Z3.Symbol.mk_string ctx new_name in 
  let x_exp = Z3.Arithmetic.Integer.mk_const ctx x_sym in 
  let x_val = Z3.Model.eval model x_exp true in 
  match x_val with
  | Some(x) -> Some(int_of_string @@ Z3.Expr.to_string x) 
  | None -> None

let from_model_new model target_stack ctx : t = 
  let input_feeder = query_model_new model target_stack ctx in
  fun query ->
    let answer = input_feeder query in
    Option.value ~default:42 answer
*)