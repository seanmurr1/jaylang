open Core
open Dbmc_lib

let generate_inputs 
    test_generator
  : (int list * int) list * 'a option =
  (* let generation_callback inputs steps = prints results *)

  let inputs = [1;2] in
  let step = 3 in
  let answers = [(inputs, step)] in
  let generator_opt = Some test_generator in
  answers, generator_opt

let ctx = Z3.mk_context []

module Z3API = Dmbc_solver.Solver.Make (struct let ctx = ctx end) ()

(* 
type solution =
  (symbol -> Ast.value option) * Relative_stack.concrete_stack option
 *)
(* Noting one model may generate more solutions *)
let build_input_sequence
    _solution
    _program
    _target
  : int list =
  []

let solution_input_feeder model target_stack =
  fun (x, call_stack) : int ->
  let x = x |> Id.of_ast_id in
  let stk = Relative_stack.relativize target_stack call_stack in
  print_endline @@ (x |> Id.sexp_of_t |> Sexp.to_string);
  print_endline @@ (stk |> Relative_stack.sexp_of_t |> Sexp.to_string);

  let sym = Symbol.id x stk in
  Z3API.get_int_s model (Symbol.to_string_mach sym)

let generate program target_x =
  let solver  = Z3.Solver.mk_solver ctx None in
  let phis = Odefa_symbolic_interpreter.Dbmc.lookup_main program target_x in

  List.iter phis ~f:(fun phi ->
      let z3_phi = Z3API.z3_phis_of_smt_phi phi in
      Z3.Solver.add solver [z3_phi];
      print_endline @@ Constraint.to_string phi;  
      print_endline @@ Z3.Expr.to_string z3_phi;
      Out_channel.newline stdout
    );
  match Z3API.check_and_get_model solver with
  | Some model ->
    let target_stack = Z3API.get_top_stack model |> snd in
    let input_feeder = solution_input_feeder model target_stack in
    let target = (target_x, target_stack) in
    let _ = Odefa_interpreter.Naive_interpreter.eval ~input_feeder ~target program in
    ()
  | None -> ()


(* 
previous step
test_generator.ml 
-> Generator.generate_inputs
-> Generator.input_sequence_from_solution
-> Odefa_interpreter.Interpreter.eval : ()
      with ~input_source:read_from_solver
           ~clause_callback:stop_at_stop_var
           e
      where
      -- read_from_solver (Var(x,stk)) : value = 
        and mutate input_record
      -- stop_at_stop_var clause = a callback fun to check whether stop

Relative_stack
  -- concretize stack
  -- relativize

input[a;b]

input[-b,c]

target = [a;c]


 *)