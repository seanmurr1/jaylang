open Core
open Dbmc

let usage_msg = "jil -i <file> [<input_i>]"
let source_file = ref ""
let inputs = ref []

let mode = ref ""

let anon_fun i_raw =
  let this_i = int_of_string_opt i_raw in
  inputs := !inputs @ [ this_i ]

let run_program source =
  let program = Dj_common.File_utils.read_source source in
  let session =
    {
      (Interpreter.make_default_session ()) with
      input_feeder = Input_feeder.from_list !inputs;
    }
  in
  try Interpreter.eval session program with
  | Interpreter.Terminate v -> Format.printf "%a" Interpreter.pp_dvalue v
  | ex -> raise ex

(*****ADDITIONS BELOW******)

(* Variable generator (only random integers for now) *)
(* let var_gen = Int.quickcheck_generator *)
let limited_var_gen = Int.gen_incl (-100) 100

let test_program_concolic source = 
  let program = Dj_common.File_utils.read_source source in 
  let session = 
    {
      (Interpreter.make_default_session ()) with 
      input_feeder = fun _ -> (Quickcheck.random_value ~seed:`Nondeterministic limited_var_gen)
    }
  in 
  (* try Interpreter.test_concolically session program with *)
  try Concolic.concolic_eval program with
  | Interpreter.Terminate v -> Format.printf "%a" Interpreter.pp_dvalue v 
  | Concolic.All_Branches_Hit -> Format.printf "All branches hit.\n"
  | ex -> raise ex 

let speclist = 
  [("-i", Arg.Set_string source_file, "Input source file");
   ("-m", Arg.Set_string mode, "Interpreter mode")]

let () = 
  Arg.parse speclist anon_fun usage_msg;
  match !mode with 
  | "concolic" -> test_program_concolic !source_file
  | "normal" -> run_program !source_file
  | _ -> ()

  