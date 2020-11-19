open Core
open Z3

module type Context = sig
  val ctx : Z3.context
end

module Make (C : Context) () = struct
  let ctx = C.ctx

  let _counter = ref 0

  let get_new_sym () = 
    let last = !_counter in 
    let name = "$c" ^ (string_of_int last) in
    Int.incr _counter;
    Symbol.mk_string ctx name
  let intS = Arithmetic.Integer.mk_sort ctx
  let boolS = Boolean.mk_sort ctx
  let intC = Datatype.mk_constructor_s ctx "Int"
      (Symbol.mk_string ctx "is-Int") [Symbol.mk_string ctx "i"] [Some intS] [1]
  let boolC = Datatype.mk_constructor_s ctx "Bool"
      (Symbol.mk_string ctx "is-Bool") [Symbol.mk_string ctx "b"] [Some boolS] [1]
  let funC = Datatype.mk_constructor_s ctx "Fun"
      (Symbol.mk_string ctx "is-Fun") [] [] []

  (* let bottomC = Datatype.mk_constructor_s ctx "Bottom"
      (Symbol.mk_string ctx "is-Bottom") [] [] [] *)

  let valS = Datatype.mk_sort_s ctx "IntOrBoolOrFun"
      [intC; boolC; funC]

  let intR, boolR, funR = 
    match Datatype.get_recognizers valS with
    | r1::r2::r3::[] -> r1, r2, r3
    | _ -> failwith "recogniziers mismatch"

  let ifInt e = FuncDecl.apply intR [e]
  let ifBool e = FuncDecl.apply boolR [e]
  let ifFun e = FuncDecl.apply funR [e]


  let getInt, getBool = 
    match Datatype.get_accessors valS with
    | [a1]::[a2]::[]::[] -> a1, a2
    | _ -> failwith "accessors mismatch"
  let intD = Datatype.Constructor.get_constructor_decl intC
  let boolD = Datatype.Constructor.get_constructor_decl boolC
  let funD = Datatype.Constructor.get_constructor_decl funC
  (* let bottomD = Datatype.Constructor.get_constructor_decl bottomC *)

  let int_ i = FuncDecl.apply intD [Arithmetic.Integer.mk_numeral_i ctx i]
  let bool_ b = FuncDecl.apply boolD [Boolean.mk_val ctx b]
  let fun_ = FuncDecl.apply funD []
  (* let bottom_ = FuncDecl.apply bottomD [] *)

  let true_ = bool_ true
  let false_ = bool_ false

  let var_ n = Expr.mk_const_s ctx n valS

  let eq e1 e2 = Boolean.mk_eq ctx e1 e2

  let and_ e1 e2 = Boolean.mk_and ctx [e1; e2]

  let join = Boolean.mk_and ctx

  let not_ = Boolean.mk_not ctx

  let bop case inj fn e1 e2 =
    let p1 = FuncDecl.apply case [e1] in
    let p2 = FuncDecl.apply case [e2] in
    let p3 = fn p1 p2 in
    FuncDecl.apply inj [p3]

  let fn_two_ints fop y e1 e2 = 
    let ey = bop getInt intD fop e1 e2 in
    join [eq y ey; ifInt e1; ifInt e2]

  let fn_two_bools fop y e1 e2 = 
    let ey = bop getBool boolD fop e1 e2 in
    join [eq y ey; ifBool e1; ifBool e2]

  let fn_plus = fn_two_ints (fun e1 e2 -> Arithmetic.mk_add ctx [e1; e2])
  let fn_minus = fn_two_ints (fun e1 e2 -> Arithmetic.mk_sub ctx [e1; e2])
  let fn_times = fn_two_ints (fun e1 e2 -> Arithmetic.mk_mul ctx [e1; e2])
  let fn_divide = fn_two_ints (Arithmetic.mk_div ctx)
  let fn_modulus = fn_two_ints (Arithmetic.Integer.mk_mod ctx)
  let fn_lt = fn_two_ints (Arithmetic.mk_lt ctx)
  let fn_le = fn_two_ints (Arithmetic.mk_le ctx)

  let fn_and = fn_two_bools and_
  let fn_or = fn_two_bools (fun e1 e2 -> Boolean.mk_or ctx [e1; e2])
  let fn_xor = fn_two_bools (Boolean.mk_xor ctx)

  let fn_eq y x1 x2 =
    eq y (eq x1 x2)

  let ground_truth = eq true_ true_

  open Odefa_symbolic_interpreter
  open Constraint
  open Interpreter_types
  open Odefa_ast.Ast    
  let symbol_suffix_of_relative_stack
      (Relative_stack.Relative_stack(costk,stk)) : string =
    let costk_name =
      String.concat ~sep:"$" @@ List.map ~f:(fun (Ident(s)) -> s) costk
    in
    let stk_name =
      String.concat ~sep:"$" @@ List.map ~f:(fun (Ident(s)) -> s) stk
    in
    Printf.sprintf "$$%s$$%s" costk_name stk_name
  ;;

  let name_of_csymbol = function
    | SpecialSymbol SSymTrue -> "$$$true"
    | Symbol (Ident id, relstk) -> 
      id ^ symbol_suffix_of_relative_stack relstk

  let var_of_symbol sym = 
    sym |> name_of_csymbol |> var_

  let name_of_ids ids =
    String.concat ~sep:"," @@ List.map ~f:(fun (Ident(s)) -> s) ids

  let rec z3_phis_of_smt_phi = function
    | Constraint_value (sx, cv) -> 
      let x = var_of_symbol sx in
      let v = match cv with
        | Int i -> int_ i
        | Bool b -> bool_ b
        | Function _ -> fun_
        | Record _ -> failwith "no record yet"
      in
      eq x v
    (* [eq x v; not_ (eq x bottom_)] *)
    | Constraint_alias (sx, sy) -> 
      let x = var_of_symbol sx in
      let y = var_of_symbol sy in
      eq x y
    (* [eq x y; not_ (eq x bottom_); not_ (eq y bottom_)] *)
    | Constraint_binop (sy, sx1, op, sx2) ->
      let y = var_of_symbol sy in
      let x1 = var_of_symbol sx1 in
      let x2 = var_of_symbol sx2 in
      let fop = match op with
        | Binary_operator_plus -> fn_plus
        | Binary_operator_minus -> fn_minus
        | Binary_operator_times -> fn_times
        | Binary_operator_divide -> fn_divide
        | Binary_operator_modulus -> fn_modulus
        | Binary_operator_less_than -> fn_le
        | Binary_operator_less_than_or_equal_to -> fn_lt
        | Binary_operator_equal_to -> fn_eq
        | Binary_operator_and -> fn_and
        | Binary_operator_or -> fn_or
        | Binary_operator_xor -> fn_xor
      in
      fop y x1 x2
    (* [eq y (fop x1 x2); not_ (eq y bottom_); not_ (eq x1 bottom_); not_ (eq x2 bottom_)] *)
    | Constraint_ids (s1, xs1, s2, xs2) ->
      let x = var_ @@ (name_of_ids xs1) ^ symbol_suffix_of_relative_stack s1 in
      let y = var_ @@ (name_of_ids xs2) ^ symbol_suffix_of_relative_stack s2 in
      eq x y
    (* [eq x y; not_ (eq x bottom_); not_ (eq y bottom_)] *)
    | Constraint_and (c1, c2) ->
      let e1 = z3_phis_of_smt_phi c1 in
      let e2 = z3_phis_of_smt_phi c2 in
      Boolean.mk_and ctx [e1; e2]
    | Constraint_exclusive cs ->
      let payloads = List.map cs ~f:z3_phis_of_smt_phi in
      let choice_vars = List.map payloads ~f:(fun _ -> Z3.Boolean.mk_const ctx (get_new_sym ())) in
      let chosen_payloads = List.mapi payloads ~f:(fun ci payload ->
          let ci_var = List.nth_exn choice_vars ci in
          let other_vars = List.filteri choice_vars ~f:(fun i _ -> Int.(ci <> i)) in
          let exclusion = 
            other_vars
            |> Z3.Boolean.mk_or ctx
            |> Z3.Boolean.mk_not ctx
          in
          let payload' = and_ payload exclusion in
          Z3.Boolean.mk_implies ctx ci_var payload'
        ) in
      let must_one_choice = Z3.Boolean.mk_or ctx choice_vars in
      join (must_one_choice::chosen_payloads)
    | Constraint_projection _
    | Constraint_type _ 
    | Constraint_stack _
      -> ground_truth

end

(*
let ctx = Z3.mk_context []

 module Z3API = Make (struct let ctx = ctx end) ()

   let e1 = Z3API.int_ 3
   let e2 = Z3API.bool_ true
   let e3 = Z3API.fun_ ()
   let x1 = Z3API.var_ "x1"
   let x2 = Z3API.var_ "x2"
   let x3 = Z3API.var_ "x3"
   let eq1 = Z3API.eq x1 e1
   let eq2 = Z3API.eq x2 e2
   let eq3 = Z3API.eq x3 e3

   let solver  = Solver.mk_solver ctx None

   let () =
   Solver.add solver [eq1; eq2; eq3];
   print_endline @@ Solver.to_string solver;
   match Solver.check solver [] with
   | Solver.SATISFIABLE ->
    begin
      match Solver.get_model solver with
      | None -> print_endline "none"
      | Some model -> print_endline @@ Model.to_string model
    end
   | Solver.UNSATISFIABLE ->
    print_endline "UNSAT"
   | Solver.UNKNOWN ->
    failwith @@ Printf.sprintf "Unknown result in solve: %s"
      (Solver.get_reason_unknown solver) *)



