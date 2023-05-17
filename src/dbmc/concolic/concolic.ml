open Core
open Graph
open Dj_common
open Log.Export
open Jayil
open Ast

module SuduZ3 = Solver.SuduZ3
open SuduZ3

type dvalue =
  | Direct of value
  | FunClosure of Ident.t * function_value * denv
  | RecordClosure of record_value * denv
  | AbortClosure of denv

and dvalue_with_stack = dvalue * Concrete_stack.t
and denv = dvalue_with_stack Ident_map.t

let value_of_dvalue = function
  | Direct v -> v
  | FunClosure (_fid, fv, _env) -> Value_function fv
  | RecordClosure (r, _env) -> Value_record r
  | AbortClosure _ -> Value_bool false

let rec pp_dvalue oc = function
  | Direct v -> Jayil.Ast_pp.pp_value oc v
  | FunClosure _ -> Format.fprintf oc "(fc)"
  | RecordClosure (r, env) -> pp_record_c (r, env) oc
  | AbortClosure _ -> Format.fprintf oc "(abort)"

and pp_record_c (Record_value r, env) oc =
  let pp_entry oc (x, v) =
    Fmt.pf oc "%a = %a" Jayil.Ast_pp.pp_ident x Jayil.Ast_pp.pp_var v
  in
  (Fmt.braces (Fmt.iter_bindings ~sep:(Fmt.any ", ") Ident_map.iter pp_entry))
    oc r

let rec dvalue_to_string dv = 
  match dv with 
  | Direct v -> Jayil.Ast_pp.show_value v 
  | FunClosure(x, fval, env) -> let Ident(s) = x in "(FC: `"^s^"`, "^(env_to_string env)^")"
  | _ -> "unsupported"
and env_to_string env = 
  let seq = Ident_map.to_seq env in 
  let f_print (i, (v, stk)) = 
    let Ident(s) = i in 
    s ^ "=>" ^ (dvalue_to_string v) ^ "_" ^ (stk |> Rstack.from_concrete |> Rstack.to_string) ^ ", " 
  in
  BatSeq.to_string f_print seq;

exception Found_target of { x : Id.t; stk : Concrete_stack.t; v : dvalue }
exception Found_abort of dvalue
exception Terminate of dvalue
exception Reach_max_step of Id.t * Concrete_stack.t
exception Run_the_same_stack_twice of Id.t * Concrete_stack.t
exception Run_into_wrong_stack of Id.t * Concrete_stack.t

type mode =
  | Plain
  | With_target_x of Id.t
  | With_full_target of Id.t * Concrete_stack.t

type clause_cb = Id.t -> Concrete_stack.t -> value -> unit
type debug_mode = No_debug | Debug_clause of clause_cb

module G = Imperative.Digraph.ConcreteBidirectional (Id_with_stack)

type session = {
  (* mode *)
  input_feeder : Input_feeder.t;
  mode : mode;
  (* tuning *)
  step : int ref;
  max_step : int option;
  (* book-keeping *)
  alias_graph : G.t;
  (* debug *)
  is_debug : bool; (* TODO: get rid of this *)
  debug_mode : debug_mode;
  val_def_map : (Id_with_stack.t, clause_body * dvalue) Hashtbl.t;
  term_detail_map : (Lookup_key.t, Term_detail.t) Hashtbl.t;
  block_map : Cfg.block Jayil.Ast.Ident_map.t;
  rstk_picked : (Rstack.t, bool) Hashtbl.t;
  lookup_alert : Lookup_key.t Hash_set.t;
}

let make_default_session () =
  {
    input_feeder = Fn.const 42;
    mode = Plain;
    max_step = None;
    is_debug = false;
    debug_mode = No_debug;
    step = ref 0;
    alias_graph = G.create ();
    val_def_map = Hashtbl.create (module Id_with_stack);
    block_map = Jayil.Ast.Ident_map.empty;
    term_detail_map = Hashtbl.create (module Lookup_key);
    rstk_picked = Hashtbl.create (module Rstack);
    lookup_alert = Hash_set.create (module Lookup_key);
  }

let create_session ?max_step ?(debug_mode = No_debug) (state : Global_state.t)
    (config : Global_config.t) mode input_feeder : session =
  (* = With_full_target (config.target, target_stk) *)
  {
    input_feeder;
    mode;
    max_step;
    is_debug = config.debug_interpreter;
    debug_mode;
    step = ref 0;
    alias_graph = G.create ();
    block_map = state.block_map;
    val_def_map = Hashtbl.create (module Id_with_stack);
    term_detail_map = state.term_detail_map;
    rstk_picked = state.rstk_picked;
    lookup_alert = state.lookup_alert;
  }
  
(**************** Branch Tracking: ****************)
exception All_Branches_Hit
exception Unreachable_Branch

(* Branch status types: *)
type status = Hit | Unhit
type branch_status = {mutable true_branch: status; mutable false_branch: status}
type branch = True_branch of ident | False_branch of ident

(* Tracks if a given branch has been hit in our testing yet. *)
let branches = Ident_hashtbl.create 2 

let target_branch : (Lookup_key.t * Z3.Expr.expr) option ref = ref None
(* let target_stack = ref Concrete_stack.empty *)

let status_to_string status = 
  match status with 
  | Hit -> "HIT"
  | Unhit -> "UNHIT"

let print_branch_status x branch_status = 
  let Ident(s) = x in 
  Format.printf "%s: True=%s; False=%s\n" s (status_to_string branch_status.true_branch) (status_to_string branch_status.false_branch)

let print_branches () =
   Format.printf "\nBranch Information:\n";
   Ident_hashtbl.iter (fun x s -> print_branch_status x s) branches

(* Adds a branch to tracking. *)
let add_branch (x : ident) : unit = 
  Ident_hashtbl.add branches x {true_branch = Unhit; false_branch = Unhit};
  ()

let update_target_branch (x_key : Lookup_key.t) (condition_key : Lookup_key.t) (b : bool) : unit = 
  let formula = Riddler.eqv condition_key (Value_bool (not b)) in
  let branch_status = Ident_hashtbl.find branches x_key.x in 
  match b, branch_status.true_branch, branch_status.false_branch with 
  | true, _, Unhit | false, Unhit, _ -> 
    Format.printf "Updating target branch to: %s:%b, with condition %s\n" (Lookup_key.to_string x_key) (not b) (Z3.Expr.to_string formula);
    target_branch := Some(x_key, formula);
  | _, _, _ -> ()

(* Marks a branch as hit. *)
(* TODO: if we hit target, set target to NONE *)
let hit_branch (x : ident) (b : bool) : unit = 
  let Ident(s) = x in
  Format.printf "Hitting: %s %b\n" s b;
  let branch_status = Ident_hashtbl.find branches x in 
  match b, branch_status.true_branch, branch_status.false_branch with 
  | true, Unhit, _ -> branch_status.true_branch <- Hit; 
  | false, _, Unhit ->  branch_status.false_branch <- Hit; 
  | _, _, _ -> ()

(* Checks if a given branch is hit. *)
let is_branch_hit (x : ident) (b : bool) : status = 
  let branch_status = Ident_hashtbl.find branches x in 
  match b with 
  | true -> branch_status.true_branch
  | false -> branch_status.false_branch

(* Find all branches in an expression. *)
let rec find_branches (e : expr) : unit = 
  let (Expr clauses) = e in 
  List.fold clauses ~init:() ~f:(fun () clause -> find_branches_in_clause clause)

(* Find all branches in a clause. *)  
and find_branches_in_clause (clause : clause) : unit = 
  let (Clause (Var (x, _), cbody)) = clause in
  match cbody with 
  | Conditional_body (x2, e1, e2) -> 
      add_branch x;
      find_branches e1;
      find_branches e2; 
  | Value_body (Value_function (Function_value (x2, e1))) -> 
      find_branches e1;
  | _ -> () 

(* Checks if all branches have been hit. *)
let all_branches_hit () = 
  let folder (x : ident) (status : branch_status) (accum : ident option) = 
    match status.true_branch, status.false_branch with 
    | Unhit, Unhit -> Some(x) 
    | Unhit, Hit -> Some(x) 
    | Hit, Unhit -> Some(x)
    | Hit, Hit -> accum
  in 
  Ident_hashtbl.fold folder branches None 

(*************** SMT Solver *************)
let solver = Z3.Solver.mk_solver SuduZ3.ctx None

let implication_store = Hashtbl.create (module Lookup_key)

let parent_implications = Hashtbl.create (module Lookup_key)

let p_to_s (k, b) =
  "("^(Lookup_key.to_string k)^":"^(Bool.to_string b)^")"

let l_to_s l = 
  List.fold l ~init:"" ~f:(fun c p -> c^(p_to_s p))

let print_parents () = 
  Printf.printf "PARENTS:\n";
  Hashtbl.iteri parent_implications ~f:(fun ~key ~data -> Printf.printf "%s --> %s\n" (Lookup_key.to_string key) (l_to_s data));
  Printf.printf "DONE\n";
  ()

let add_implication formula parent = 
  Printf.printf "IMPLICATION: %s => %s\n" (Lookup_key.to_string parent) (Z3.Expr.to_string formula); 
  let store = Hashtbl.find implication_store parent in 
  match store with 
  | None -> Hashtbl.add_exn implication_store ~key:parent ~data:[formula]
  | Some(lst) -> Hashtbl.set implication_store ~key:parent ~data:(formula :: lst)

let parse_parents parents = 
  List.fold parents ~init:([], []) ~f:(fun (exps, parents) (parent, direction) -> 
    ((Riddler.eqv parent (Value_bool direction)) :: exps, parent :: parents))

let gen_antecedents children = 
  List.fold children ~init:([], []) ~f:(fun (exps, parents) key -> 
    match Hashtbl.find parent_implications key with 
    | None -> (exps, parents)
    | Some(parent_lst) -> let (new_exps, new_parents) = parse_parents parent_lst in 
      (new_exps @ exps, new_parents @ parents)
    ) 

let rec get_dependencies children =
  List.fold children ~init:[] ~f:(fun deps key ->
    match Hashtbl.find parent_implications key with 
    | None -> deps 
    | Some(lst) -> let (exps, parents) = parse_parents lst in 
      deps @ exps @ (get_dependencies parents)
    ) 

(* Create right associative chain of implications. *)
let rec gen_formula children formula = 
  match gen_antecedents children with
  | ([], _) -> formula
  | (exps, parents) -> 
    let antecedent = if List.length exps >1 then Riddler.and_ exps else List.hd_exn exps in 
    let implication = Riddler.(@=>) antecedent formula in 
    gen_formula parents implication

let add_formula children parent formula = 
  let new_formula = gen_formula children formula in 
  match parent with 
  | None -> (Printf.printf "ADDED: %s\n" (Z3.Expr.to_string new_formula)); Z3.Solver.add solver [new_formula]
  | Some(parent) -> add_implication new_formula parent

let add_parents child_key condition_key direction ret_key = 
  match (Hashtbl.find parent_implications child_key), (Hashtbl.find parent_implications condition_key) with 
  | None, None -> Hashtbl.set parent_implications ~key:child_key ~data:[(condition_key, direction)]
  | Some(lst), None -> Hashtbl.set parent_implications ~key:child_key ~data:((condition_key, direction) :: lst)
  | None, Some(lst) -> Hashtbl.set parent_implications ~key:child_key ~data:((condition_key, direction) :: lst)
  | Some(lst1), Some(lst2) -> Hashtbl.set parent_implications ~key:child_key ~data:((condition_key, direction) :: lst1 @ lst2)

let add_parents2 child_key dependencies = 
  let cur = match Hashtbl.find parent_implications child_key with 
  | None -> [] 
  | Some(lst) -> lst 
  in
  List.fold dependencies ~init:cur ~f:(fun c p -> 
    match Hashtbl.find parent_implications p with 
    | None -> cur 
    | Some(lst) -> Hashtbl.set parent_implications ~key:child_key ~data:(lst @ cur); lst @ cur
    )


let flush_implications parent_key condition_key direction = 
  let antecedent = Riddler.eqv condition_key (Value_bool direction) in
  let store = Hashtbl.find implication_store condition_key in 
  match store with 
  | None -> ()
  | Some(lst) -> 
    let consequent = Riddler.and_ lst in
    let implication = Riddler.(@=>) antecedent consequent in
    (* add_formula_helper parent_key implication; *)
    add_formula [condition_key] parent_key implication;
    Hashtbl.remove implication_store condition_key

(****************************)

let first_run = ref true

let print_solver_formulas solver =
  let assertions = Z3.Solver.get_assertions solver in
let rec print_formulas formulas =
  match formulas with
  | [] -> ()
  | hd::tl ->
    Printf.printf "%s\n" (Z3.Expr.to_string hd);
    print_formulas tl in
print_formulas assertions

let solve_SMT_branch () = 
  match !target_branch with 
  | None -> None 
  | Some(key, condition) -> 
    Z3.Solver.add solver [condition];
    Z3.Solver.add solver [Riddler.picked key];
    let model = get_model_exn solver @@ Z3.Solver.check solver [] in 
    Some(model)

let generate_input_feeder () = 
  match solve_SMT_branch () with 
  | None -> raise Unreachable_Branch
  | Some(model) -> Input_feeder.from_model2 model 

let cond_fid b = if b then Ident "$tt" else Ident "$ff"

(* This function will add a directed edge x1 -> x2 in the alias graph. Thus
   x1 here needs to be the *later* defined variable. *)
let add_alias x1 x2 session : unit =
  let alias_graph = session.alias_graph in
  G.add_edge alias_graph x1 x2

let add_val_def_mapping x vdef session : unit =
  let val_def_mapping = session.val_def_map in
  Hashtbl.add_exn ~key:x ~data:vdef val_def_mapping

let debug_update_read_node session x stk =
  match (session.is_debug, session.mode) with
  | true, With_full_target (_, target_stk) ->
      let r_stk = Rstack.relativize target_stk stk in
      let block = Cfg.(find_block_by_id x session.block_map) in
      let key = Lookup_key.of3 x r_stk block in
      (* Fmt.pr "@[Update Get to %a@]\n" Lookup_key.pp key; *)
      Hashtbl.change session.term_detail_map key ~f:(function
        | Some td -> Some { td with get_count = td.get_count + 1 }
        | None -> failwith "not term_detail")
  | _, _ -> ()

let debug_update_write_node session x stk =
  match (session.is_debug, session.mode) with
  | true, With_full_target (_, target_stk) ->
      let r_stk = Rstack.relativize target_stk stk in
      let block = Cfg.(find_block_by_id x session.block_map) in
      let key = Lookup_key.of3 x r_stk block in
      (* Fmt.pr "@[Update Set to %a@]\n" Lookup_key.pp key; *)
      Hashtbl.change session.term_detail_map key ~f:(function
        | Some td -> Some { td with is_set = true }
        | None -> failwith "not term_detail")
  | _, _ -> ()

let debug_stack session x stk (v, _) =
  match (session.is_debug, session.mode) with
  | true, With_full_target (_, target_stk) ->
      let rstk = Rstack.relativize target_stk stk in
      Fmt.pr "@[%a = %a\t\t R = %a@]\n" Id.pp x pp_dvalue v Rstack.pp rstk
  | _, _ -> ()

let raise_if_with_stack session x stk v =
  match session.mode with
  | With_full_target (target_x, target_stk) when Ident.equal target_x x ->
      if Concrete_stack.equal_flip target_stk stk
      then raise (Found_target { x; stk; v })
      else
        Fmt.(
          pr "found %a at stack %a, expect %a\n" pp_ident x Concrete_stack.pp
            target_stk Concrete_stack.pp stk)
  | With_target_x target_x when Ident.equal target_x x ->
      raise (Found_target { x; stk; v })
  | _ -> ()

let alert_lookup session x stk =
  match session.mode with
  | With_full_target (_, target_stk) ->
      let r_stk = Rstack.relativize target_stk stk in
      let block = Cfg.(find_block_by_id x session.block_map) in
      let key = Lookup_key.of3 x r_stk block in
      Fmt.epr "@[Update Alert to %a\t%a@]\n" Lookup_key.pp key Concrete_stack.pp
        stk ;
      Hash_set.add session.lookup_alert key
  | _ -> ()

let rec same_stack s1 s2 =
  match (s1, s2) with
  | (cs1, fid1) :: ss1, (cs2, fid2) :: ss2 ->
      Ident.equal cs1 cs2 && Ident.equal fid1 fid2 && same_stack ss1 ss2
  | [], [] -> true
  | _, _ -> false

let debug_clause ~session x v stk =
  ILog.app (fun m -> m "@[%a = %a@]" Id.pp x pp_dvalue v) ;

  (match session.debug_mode with
  | Debug_clause clause_cb -> clause_cb x stk (value_of_dvalue v)
  | No_debug -> ()) ;

  raise_if_with_stack session x stk v ;
  debug_stack session x stk (v, stk) ;
  ()

let generate_lookup_key x stk = 
  let rstk : Rstack.t = Rstack.from_concrete stk in 
  let block : Cfg.block = {id = x; clauses = []; kind = Main} in
  let key : Lookup_key.t = {x = x; r_stk = rstk; block = block} in 
  key

(* OB: we cannot enter the same stack twice. *)
let rec eval_exp ~session stk env e parent_key direction : denv * dvalue =
  ILog.app (fun m -> m "@[-> %a@]\n" Concrete_stack.pp stk) ;
  (match session.mode with
  | With_full_target (_, target_stk) ->
      let r_stk = Rstack.relativize target_stk stk in
      Hashtbl.change session.rstk_picked r_stk ~f:(function
        | Some true -> Some false
        | Some false -> raise (Run_into_wrong_stack (Ast_tools.first_id e, stk))
        | None -> None)
  | _ -> ()) ;

  let (Expr clauses) = e in
  let denv, vs' =
    List.fold_map ~f:(eval_clause ~session stk parent_key direction) ~init:env clauses
  in
  (denv, List.last_exn vs')

(* OB: once stack is to change, there must be an `eval_exp` *)
and eval_clause ~session stk parent_key direction env clause : denv * dvalue =
  (* print_parents (); *)

  let (Clause (Var (x, _), cbody)) = clause in
  (match session.max_step with
  | None -> ()
  | Some t ->
      Int.incr session.step ;
      if !(session.step) > t then raise (Reach_max_step (x, stk)) else ()) ;

  debug_update_write_node session x stk ;

  let x_key = generate_lookup_key x stk in 

  let (v : dvalue) =
    match cbody with
    | Value_body ((Value_function vf) as v) ->
        (* x = fun ... ; *)
        let retv = FunClosure (x, vf, env) in
        let () = add_val_def_mapping (x, stk) (cbody, retv) session in
        (* Printf.printf "Adding function closure: %s\n" @@ dvalue_to_string retv; *)
        add_formula [] parent_key @@ Riddler.eq_term_v x_key (Some(v));
        retv
    | Value_body ((Value_record r) as v) ->
        (* x = {...} ; *)
        let retv = RecordClosure (r, env) in
        let () = add_val_def_mapping (x, stk) (cbody, retv) session in
        add_formula [] parent_key @@ Riddler.eq_term_v x_key (Some(v));
        retv
    | Value_body v ->
        (* x = <bool or int> ; *)
        let retv = Direct v in
        let () = add_val_def_mapping (x, stk) (cbody, retv) session in
        add_formula [] parent_key @@ Riddler.eq_term_v x_key (Some(v));
        retv
    | Var_body vx ->
        (* x = y ; *)
        let (Var (y, _)) = vx in
        let ret_val, ret_stk = fetch_val_with_stk ~session ~stk env vx in
        let y_key = generate_lookup_key y ret_stk in 
        add_formula [y_key] parent_key @@ Riddler.eq x_key y_key;
        let _ = add_parents2 x_key [y_key] in 
        add_alias (x, stk) (y, ret_stk) session ;
        ret_val
    | Conditional_body (x2, e1, e2) ->
        (* x = if y then e1 else e2 ; *)
        let branch_result = fetch_val_to_bool ~session ~stk env x2 in 
        let _, condition_stk = fetch_val_with_stk ~session ~stk env x2 in
        let (Var (y, _)) = x2 in
        let condition_key = generate_lookup_key y condition_stk in 
        (* Hit branch: *)
        hit_branch x branch_result;
        (* Check for new branch target: *)
        update_target_branch x_key condition_key branch_result;

        let e, stk' =
          if branch_result
          then (e1, Concrete_stack.push (x, cond_fid true) stk)
          else (e2, Concrete_stack.push (x, cond_fid false) stk)
        in

        (* Evalutate branch with new parent condition: *)
        let ret_env, ret_val = eval_exp ~session stk' env e (Some(condition_key)) (Some(branch_result))in
        let (Var (ret_id, _) as last_v) = Ast_tools.retv e in
        let _, ret_stk = fetch_val_with_stk ~session ~stk:stk' ret_env last_v in

        (* Map x to result of 'if' statement: *)
        let ret_key = generate_lookup_key ret_id ret_stk in 

        (* add_formula @@ Riddler.eq x_key ret_key; *) (* TODO FIX BELOW? *)
        add_formula [ret_key] (Some(condition_key)) @@ Riddler.eq x_key ret_key;
        flush_implications parent_key condition_key branch_result;
        (* Add parent relationship to return variable: *)
        add_parents x_key condition_key branch_result ret_key;

        (* TODO: add Pick x_key => parents? *)
        let dependencies = match parent_key, direction with 
        | Some(key), Some(d) -> Riddler.eqv key (Value_bool d) :: get_dependencies [key]
        | _, _ -> []
        in
        let pick_formula = Riddler.(@=>) (Riddler.picked x_key) (Riddler.and_ dependencies) in
        Printf.printf "Pick formula: %s\n" (Z3.Expr.to_string pick_formula);
        Z3.Solver.add solver [pick_formula];

        add_alias (x, stk) (ret_id, ret_stk) session ;
        ret_val
    | Input_body ->
        (* TODO: the interpreter may propagate the dummy value (through the value should never be used in any control flow)  *)
        let n = session.input_feeder (x, stk) in
        let retv = Direct (Value_int n) in
        let () = add_val_def_mapping (x, stk) (cbody, retv) session in

        let Ident(s) = x in 
        Format.printf "Feed %d to %s\n" n s;
        add_formula [] parent_key @@ Riddler.eq_term_v x_key None;
        retv
    | Appl_body (vx1, (Var (x2, _) as vx2)) -> (
        (* x = f y ; *)
        match fetch_val ~session ~stk env vx1 with
        | FunClosure (fid, Function_value (Var (arg, _), body), fenv) ->
            let v2, v2_stk = fetch_val_with_stk ~session ~stk env vx2 in
            let stk2 = Concrete_stack.push (x, fid) stk in
            let env2 = Ident_map.add arg (v2, stk) fenv in
            add_alias (arg, stk) (x2, v2_stk) session ;

            (* Enter function: *)
            let Var(xid, _) = vx1 in 
            let _, f_stk = fetch_val_with_stk ~session ~stk env vx1 in 
            let key_f = generate_lookup_key xid f_stk in 
            let key_para = generate_lookup_key arg stk in 
            let key_arg = generate_lookup_key x2 v2_stk in 
            add_formula [key_f; key_arg] parent_key @@ Riddler.same_funenter key_f fid key_para key_arg;

            let ret_env, ret_val = eval_exp ~session stk2 env2 body parent_key direction in
            let (Var (ret_id, _) as last_v) = Ast_tools.retv body in
            let _, ret_stk =
              fetch_val_with_stk ~session ~stk:stk2 ret_env last_v
            in
            add_alias (x, stk) (ret_id, ret_stk) session ;

            (* Exit function: *)
            let key_out = generate_lookup_key ret_id ret_stk in 
            (* TODO FIX*)
            add_formula [key_out; key_f; key_arg] parent_key @@ Riddler.same_funexit key_f fid x_key key_out;
            (* TODO: need to add parent relationship based on key_out *)
            let _ = add_parents2 x_key [key_out; key_f; key_arg] in

            ret_val
        | _ -> failwith "app to a non fun")
    | Match_body (vx, p) ->
        let match_res = Value_bool (check_pattern ~session ~stk env vx p) in
        let retv = Direct (match_res) in
        let () = add_val_def_mapping (x, stk) (cbody, retv) session in
        (* TODO: SMT tracking fix with riddler stuff TODO: check if [] should be empty or smoething with vx...*)
        add_formula [] parent_key @@ Riddler.eq_term_v x_key (Some(match_res));
        retv
    | Projection_body (v, key) -> (
        match fetch_val ~session ~stk env v with
        | RecordClosure (Record_value r, denv) ->
            let (Var (proj_x, _) as vv) = Ident_map.find key r in
            let dvv, vv_stk = fetch_val_with_stk ~session ~stk denv vv in
            add_alias (x, stk) (proj_x, vv_stk) session ;
            (* TODO: SMT tracking fix with riddler stuff *)
            let proj_key = generate_lookup_key proj_x vv_stk in 
            add_formula [proj_key] parent_key @@ Riddler.eq x_key proj_key;
            dvv
        | Direct (Value_record (Record_value _record)) ->
            (* let vv = Ident_map.find key record in
               fetch_val env vv *)
            failwith "project should also have a closure"
        | _ -> failwith "project on a non record")
    | Not_body vx ->
        (* x = not y ; *)
        let v = fetch_val_to_direct ~session ~stk env vx in
        let bv =
          match v with
          | Value_bool b -> Value_bool (not b)
          | _ -> failwith "incorrect not"
        in
        let retv = Direct bv in
        let () = add_val_def_mapping (x, stk) (cbody, retv) session in

        let (Var (y, _)) = vx in
        let y_key = generate_lookup_key y stk in 
        add_formula [y_key] parent_key @@ Riddler.not_ x_key y_key;
        let _ = add_parents2 x_key [y_key] in

        retv
    | Binary_operation_body (vx1, op, vx2) ->
        (* x = y OP z ; *)
        let v1 = fetch_val_to_direct ~session ~stk env vx1
        and v2 = fetch_val_to_direct ~session ~stk env vx2 in
        let v =
          match (op, v1, v2) with
          | Binary_operator_plus, Value_int n1, Value_int n2 ->
              Value_int (n1 + n2)
          | Binary_operator_minus, Value_int n1, Value_int n2 ->
              Value_int (n1 - n2)
          | Binary_operator_times, Value_int n1, Value_int n2 ->
              Value_int (n1 * n2)
          | Binary_operator_divide, Value_int n1, Value_int n2 ->
              Value_int (n1 / n2)
          | Binary_operator_modulus, Value_int n1, Value_int n2 ->
              Value_int (n1 mod n2)
          | Binary_operator_less_than, Value_int n1, Value_int n2 ->
              Value_bool (n1 < n2)
          | Binary_operator_less_than_or_equal_to, Value_int n1, Value_int n2 ->
              Value_bool (n1 <= n2)
          | Binary_operator_equal_to, Value_int n1, Value_int n2 ->
              Value_bool (n1 = n2)
          | Binary_operator_equal_to, Value_bool b1, Value_bool b2 ->
              Value_bool (Bool.( = ) b1 b2)
          | Binary_operator_and, Value_bool b1, Value_bool b2 ->
              Value_bool (b1 && b2)
          | Binary_operator_or, Value_bool b1, Value_bool b2 ->
              Value_bool (b1 || b2)
          | Binary_operator_not_equal_to, Value_int n1, Value_int n2 ->
              Value_bool (n1 <> n2)
          | _, _, _ -> failwith "incorrect binop"
        in
        let retv = Direct v in
        let () = add_val_def_mapping (x, stk) (cbody, retv) session in

        let (Var (y, _)) = vx1 in
        let (Var (z, _)) = vx2 in
        let _, stk1 = fetch_val_with_stk ~session ~stk env vx1 in 
        let _, stk2 = fetch_val_with_stk ~session ~stk env vx2 in 
        let y_key = generate_lookup_key y stk1 in 
        let z_key = generate_lookup_key z stk2 in 
        add_formula [y_key; z_key] parent_key @@ Riddler.binop x_key op y_key z_key;
        let _ = add_parents2 x_key [y_key; z_key] in 

        retv
        (* | Abort_body ->
             raise @@ Found_abort x
           | Assert_body vx ->
             let v = fetch_val_to_direct ~session ~stk env vx in
             let bv =
               match v with
               | Value_bool b -> Value_bool b
               | _ -> failwith "failed assert"
             in
             Direct bv *)
        (* TODO: What should the interpreter do with an assume statement? *)
    | Abort_body -> (
        let ab_v = AbortClosure env in
        let () = add_val_def_mapping (x, stk) (cbody, ab_v) session in
        match session.mode with
        | Plain -> raise @@ Found_abort ab_v
        | With_target_x target ->
            if Id.equal target x
            then raise @@ Found_target { x; stk; v = ab_v }
            else raise @@ Found_abort ab_v
        | With_full_target (target, tar_stk) ->
            if Id.equal target x && Concrete_stack.equal_flip tar_stk stk
            then raise @@ Found_target { x; stk; v = ab_v }
            else raise @@ Found_abort ab_v)
    | Assert_body _ | Assume_body _ ->
        let retv = Direct (Value_bool true) in
        let () = add_val_def_mapping (x, stk) (cbody, retv) session in
        retv
    (* failwith "not supported yet" *)
  in
  debug_clause ~session x v stk ;
  (Ident_map.add x (v, stk) env, v)

and fetch_val_with_stk ~session ~stk env (Var (x, _)) :
    dvalue * Concrete_stack.t =
  let res = Ident_map.find x env in
  debug_update_read_node session x stk ;
  res

and fetch_val ~session ~stk env x : dvalue =
  fst (fetch_val_with_stk ~session ~stk env x)

and fetch_val_to_direct ~session ~stk env vx : value =
  match fetch_val ~session ~stk env vx with
  | Direct v -> v
  | _ -> failwith "eval to non direct value"

and fetch_val_to_bool ~session ~stk env vx : bool =
  match fetch_val ~session ~stk env vx with
  | Direct (Value_bool b) -> b
  | _ -> failwith "eval to non bool"

and check_pattern ~session ~stk env vx pattern : bool =
  let is_pass =
    match (fetch_val ~session ~stk env vx, pattern) with
    | Direct (Value_int _), Int_pattern -> true
    | Direct (Value_bool _), Bool_pattern -> true
    | Direct (Value_function _), _ -> failwith "fun must be a closure"
    | Direct (Value_record _), _ -> failwith "record must be a closure"
    | RecordClosure (Record_value record, _), Rec_pattern key_set ->
        Ident_set.for_all (fun id -> Ident_map.mem id record) key_set
    | RecordClosure (Record_value record, _), Strict_rec_pattern key_set ->
        Ident_set.equal key_set (Ident_set.of_enum @@ Ident_map.keys record)
    | FunClosure (_, _, _), Fun_pattern -> true
    | _, Any_pattern -> true
    | _, _ -> false
  in
  is_pass

(* Random integer generator. *)
(* let random_var_gen = Int.gen_incl (-100) 100 *)

let random_var_gen = Int.gen_incl (-2) 2
let create_concolic_session input_feeder = 
  {
    (make_default_session ()) with 
    input_feeder = input_feeder
  }

let default_concolic_session = create_concolic_session (fun _ -> (Quickcheck.random_value ~seed:`Nondeterministic random_var_gen)) 

(* Creates a new session for a concolic execution run. *)
let generate_new_session () = 
  match all_branches_hit (), !target_branch with 
  | None, _ -> raise All_Branches_Hit 
  | Some(unhit), None -> if !first_run then default_concolic_session else raise Unreachable_Branch
  | Some(_), Some(_) -> 
      let new_input_feeder = generate_input_feeder () in 
      create_concolic_session new_input_feeder

let rec eval e =
  Format.printf "------------------------------\n";
  Format.printf "Running program...\n";
  print_branches ();

  let target_branch_str = 
  match !target_branch with 
  | None -> "None"
  | Some(key, condition) -> (Lookup_key.to_string key)^":"^(Z3.Expr.to_string condition)
  in 
  Format.printf "\nTarget branch (cond): %s\n" target_branch_str;

  (* Check if execution is complete by generating a new session: *)
  let session = generate_new_session () in
  
  (* Now, we have a new session; reset tracking variables: *)
  target_branch := None;
  Z3.Solver.reset solver;
  Hashtbl.clear implication_store;
  Hashtbl.clear parent_implications;

  (* Create new environment and evaluate program: *)
  let empty_env = Ident_map.empty in
  try
    let v = snd (eval_exp ~session Concrete_stack.empty empty_env e None None) in
    (* Print evaluated result and run again. *)
    Format.printf "Evaluated to: %a\n" pp_dvalue v;
    first_run := false;
    eval e
  with
  (* TODO: Error cases: TODO, if we hit abort, re-run if setting is applied. *)
  | Reach_max_step (x, stk) ->
      Fmt.epr "Reach max steps\n" ;
      (* alert_lookup target_stk x stk session.lookup_alert; *)
      raise (Reach_max_step (x, stk))
  | Run_the_same_stack_twice (x, stk) ->
      Fmt.epr "Run into the same stack twice\n" ;
      alert_lookup session x stk ;
      raise (Run_the_same_stack_twice (x, stk))
  | Run_into_wrong_stack (x, stk) ->
      Fmt.epr "Run into wrong stack\n" ;
      alert_lookup session x stk ;
      raise (Run_into_wrong_stack (x, stk))


(* Concolically execute/test program. *)
let concolic_eval e = 
  (* Collect branch information from AST: *)
  find_branches e;

  Format.printf "\nStarting concolic execution...\n";

  (* Repeatedly evaluate program: *)
  eval e
