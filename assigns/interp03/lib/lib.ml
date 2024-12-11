
open Utils
include My_parser

exception AssertFail
exception DivByZero
exception RecWithoutArg
exception CompareFunVals

let rec unify ty constraints =
  let collect_and_sort_free_vars =
    let rec collect ty =
      match ty with
      | TVar x -> [x]
      | TFun (t1, t2)
      | TPair (t1, t2) ->
          collect t1 @ collect t2
      | TList t
      | TOption t ->
          collect t
      | _ -> []
    in
    fun ty ->
      let sorted = List.sort compare (collect ty) in
      let rec dedup acc = function
        | [] -> List.rev acc
        | [x] -> List.rev (x :: acc)
        | x :: y :: xs ->
            if compare x y = 0 then dedup acc (y :: xs)
            else dedup (x :: acc) (y :: xs)
      in
      dedup [] sorted
  in
  let rec occurs var ty =
    match ty with
    | TVar y -> var = y
    | TFun (t1, t2)
    | TPair (t1, t2) ->
        occurs var t1 || occurs var t2
    | TList t
    | TOption t ->
        occurs var t
    | _ -> false
  in
  let rec subtypes subst ty =
    match ty with
    | TVar x ->
        (try List.assoc x subst with Not_found -> ty)
    | TFun (t1, t2) ->
        TFun (subtypes subst t1, subtypes subst t2)
    | TPair (t1, t2) ->
        TPair (subtypes subst t1, subtypes subst t2)
    | TList t ->
        TList (subtypes subst t)
    | TOption t ->
        TOption (subtypes subst t)
    | other -> other
  in
  let sub_constraints subst cons =
    List.map (fun (a, b) -> (subtypes subst a, subtypes subst b)) cons
  in
  match constraints with
  | [] ->
      let fv = collect_and_sort_free_vars ty in
      Some (Forall (fv, ty))
  | (t1, t2) :: rest_constraints when t1 = t2 ->
      unify ty rest_constraints
  | (TVar x, t) :: rest
  | (t, TVar x) :: rest ->
      if occurs x t then None
      else
        let subst = [(x, t)] in
        let new_ty = subtypes subst ty in
        let new_constraints = sub_constraints subst rest in
        unify new_ty new_constraints
  | (TFun (ta1, ta2), TFun (tb1, tb2)) :: rest ->
      unify ty ((ta1, tb1) :: (ta2, tb2) :: rest)
  | (TPair (pa1, pa2), TPair (pb1, pb2)) :: rest ->
      unify ty ((pa1, pb1) :: (pa2, pb2) :: rest)
  | (TList ta, TList tb) :: rest
  | (TOption ta, TOption tb) :: rest ->
      unify ty ((ta, tb) :: rest)
  | _ -> None



  let type_of (type_env : stc_env) (expression : expr) : ty_scheme option =
    let rec apply substitution type_expr =
      match type_expr with
      | TVar var_name ->
          (match List.assoc_opt var_name substitution with
           | Some resolved_type -> resolved_type
           | None -> TVar var_name)
      | TFun (arg_type, return_type) -> TFun (apply substitution arg_type, apply substitution return_type)
      | TPair (first_type, second_type) -> TPair (apply substitution first_type, apply substitution second_type)
      | TList elem_type -> TList (apply substitution elem_type)
      | TOption option_type -> TOption (apply substitution option_type)
      | other_type -> other_type
    in
    let instance (type_vars, type_body) =
      let generate_substitutions = List.map (fun var -> (var, TVar (gensym ()))) in
      apply (generate_substitutions type_vars) type_body      
    in
    let rec infer inference_env expr =
      let fresh_type () = TVar (gensym ()) in
      let combine_constraints constraints1 constraints2 = constraints1 @ constraints2 in
      let infer_binary_op operator expr1 expr2 =
        let type1, constraints1 = infer inference_env expr1 in
        let type2, constraints2 = infer inference_env expr2 in
        let result_type, additional_constraints = 
          match operator with
          | Add | Sub | Mul | Div | Mod ->
              (TInt, [(type1, TInt); (type2, TInt)])
          | AddF | SubF | MulF | DivF | PowF ->
              (TFloat, [(type1, TFloat); (type2, TFloat)])
          | And | Or ->
              (TBool, [(type1, TBool); (type2, TBool)])
          | Eq | Neq ->
              let fresh = fresh_type () in
              (TBool, [(type1, fresh); (type2, fresh)])
          | Lt | Lte | Gt | Gte ->
              (TBool, [(type1, type2)])
          | Cons ->
              (TList type1, [(type2, TList type1)])
          | Concat ->
              let fresh_elem_type = fresh_type () in
              (TList fresh_elem_type, [(type1, TList fresh_elem_type); (type2, TList fresh_elem_type)])
          | Comma ->
              (TPair (type1, type2), [])
        in
        (result_type, additional_constraints @ constraints1 @ constraints2)
      in
      let infer_function arg_name arg_type body_expr =
        let arg_type, updated_env = 
          match arg_type with
          | Some explicit_type -> (explicit_type, Env.add arg_name (Forall ([], explicit_type)) inference_env)
          | None -> 
              let fresh_arg_type = fresh_type () in
              (fresh_arg_type, Env.add arg_name (Forall ([], fresh_arg_type)) inference_env)
        in
        let body_type, body_constraints = infer updated_env body_expr in
        (TFun (arg_type, body_type), body_constraints)
      in
      let infer_let_binding is_recursive let_name let_value let_body =
        if not is_recursive then
          let value_type, value_constraints = infer inference_env let_value in
          let extended_env = Env.add let_name (Forall ([], value_type)) inference_env in
          let body_type, body_constraints = infer extended_env let_body in
          (body_type, combine_constraints value_constraints body_constraints)
        else
          let fresh_arg_type = fresh_type () in
          let fresh_ret_type = fresh_type () in
          let recursive_env = Env.add let_name (Forall ([], TFun (fresh_arg_type, fresh_ret_type))) inference_env in
          let _, value_constraints = infer recursive_env let_value in
          let extended_env = Env.add let_name (Forall ([], TFun (fresh_arg_type, fresh_ret_type))) inference_env in
          let body_type, body_constraints = infer extended_env let_body in
          (body_type, combine_constraints value_constraints body_constraints)
      in
      match expr with
      | Unit -> (TUnit, [])
      | True | False -> (TBool, [])
      | Int _ -> (TInt, [])
      | Float _ -> (TFloat, [])
      | Var var_name -> (
          match Env.find_opt var_name inference_env with
          | Some (Forall (vars, type_body)) -> (instance (vars, type_body), [])
          | None -> failwith ("Unbound variable: " ^ var_name)
        )
      | ENone -> (TOption (fresh_type ()), [])
      | ESome inner_expr ->
          let inner_type, inner_constraints = infer inference_env inner_expr in
          (TOption inner_type, inner_constraints)
      | Nil -> (TList (fresh_type ()), [])
      | OptMatch { matched; some_name; some_case; none_case } ->
          let matched_type, matched_constraints = infer inference_env matched in
          let elem_type = fresh_type () in
          let some_env = Env.add some_name (Forall ([], elem_type)) inference_env in
          let some_case_type, some_case_constraints = infer some_env some_case in
          let none_case_type, none_case_constraints = infer inference_env none_case in
          let constraints = 
            (matched_type, TOption elem_type) ::
            (some_case_type, none_case_type) ::
            combine_constraints matched_constraints (combine_constraints some_case_constraints none_case_constraints)
          in
          (some_case_type, constraints)
      | Bop (op, left_expr, right_expr) -> infer_binary_op op left_expr right_expr
      | If (cond_expr, then_expr, else_expr) ->
          let cond_type, cond_constraints = infer inference_env cond_expr in
          let then_type, then_constraints = infer inference_env then_expr in
          let else_type, else_constraints = infer inference_env else_expr in
          (else_type, [(cond_type, TBool); (then_type, else_type)] @ combine_constraints cond_constraints (combine_constraints then_constraints else_constraints))
      | Fun (param_name, param_type, body_expr) -> infer_function param_name param_type body_expr
      | App (func_expr, arg_expr) ->
          let func_type, func_constraints = infer inference_env func_expr in
          let arg_type, arg_constraints = infer inference_env arg_expr in
          let fresh_ret_type = fresh_type () in
          let constraints = (func_type, TFun (arg_type, fresh_ret_type)) :: combine_constraints func_constraints arg_constraints in
          (fresh_ret_type, constraints)
      | Let { is_rec; name; value; body } -> infer_let_binding is_rec name value body
      | Assert False ->
          let fresh = fresh_type () in
          (fresh, [])
      | Assert assertion_expr ->
          let assertion_type, assertion_constraints = infer inference_env assertion_expr in
          (TUnit, (assertion_type, TBool) :: assertion_constraints)
      | Annot (annotated_expr, expected_type) ->
          let actual_type, actual_constraints = infer inference_env annotated_expr in
          (expected_type, (actual_type, expected_type) :: actual_constraints)
      | PairMatch { matched; fst_name; snd_name; case } ->
          let matched_type, matched_constraints = infer inference_env matched in
          let first_elem_type = fresh_type () in
          let second_elem_type = fresh_type () in
          let extended_env = 
            Env.add fst_name (Forall ([], first_elem_type)) (Env.add snd_name (Forall ([], second_elem_type)) inference_env)
          in
          let case_type, case_constraints = infer extended_env case in
          (case_type, (matched_type, TPair (first_elem_type, second_elem_type)) :: combine_constraints matched_constraints case_constraints)
      | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } ->
          let matched_type, matched_constraints = infer inference_env matched in
          let elem_type = fresh_type () in
          let hd_env = Env.add hd_name (Forall ([], elem_type)) inference_env in
          let tl_env = Env.add tl_name (Forall ([], TList elem_type)) hd_env in
          let cons_case_type, cons_case_constraints = infer tl_env cons_case in
          let nil_case_type, nil_case_constraints = infer inference_env nil_case in
          let constraints =
            (matched_type, TList elem_type) ::
            (cons_case_type, nil_case_type) ::
            combine_constraints matched_constraints (combine_constraints cons_case_constraints nil_case_constraints)
          in
          (nil_case_type, constraints)
    in
  
    try
      let inferred_type, constraints = infer type_env expression in
      match unify inferred_type constraints with
      | Some unified_type -> Some unified_type
      | None -> None
    with
    | _ -> None



    let rec eval_expr environment expr : value =
      let rec evaluate expression =
        match expression with
        | Unit -> VUnit
        | True -> VBool true
        | False -> VBool false
        | Int num -> VInt num
        | Float num -> VFloat num
        | ENone -> VNone
        | Nil -> VList []
        | Var variable -> Env.find variable environment
        | Fun (param, _, body) -> VClos {name=None; arg=param; body=body; env=environment}
        | App (func_expr, arg_expr) -> eval_app (evaluate func_expr) (evaluate arg_expr)
        | Bop (operator, left_expr, right_expr) -> eval_bop operator (evaluate left_expr) (evaluate right_expr)
        | ESome some_expr -> VSome (eval_expr environment some_expr)
        | OptMatch {matched=opt_value; some_name=opt_name; some_case=opt_case; none_case=none_case} ->
            eval_opt_match (evaluate opt_value) opt_name opt_case none_case
        | If (condition, then_branch, else_branch) -> eval_if (evaluate condition) then_branch else_branch
        | ListMatch {matched=list_value; hd_name=head_name; tl_name=tail_name; cons_case=cons_case; nil_case=nil_case} ->
            eval_list_match (evaluate list_value) head_name tail_name cons_case nil_case
        | PairMatch {matched=pair_value; fst_name=first_name; snd_name=second_name; case=case_expr} ->
            eval_pair_match (evaluate pair_value) first_name second_name case_expr
        | Assert assert_expr -> eval_assert (evaluate assert_expr)
        | Let {is_rec=is_recursive; name=let_name; value=let_value; body=let_body} ->
            eval_let is_recursive let_name let_value let_body
        | Annot (annot_expr, _) -> evaluate annot_expr
    
      and eval_app func arg =
        match func with
        | VClos {env=closure_env; name=closure_name; arg=closure_arg; body=closure_body} ->
            let extended_env = match closure_name with
              | None -> closure_env
              | Some name -> Env.add name func closure_env
            in
            eval_expr (Env.add closure_arg arg extended_env) closure_body
        | _ -> failwith "Error"
    
      and eval_bop operator left_val right_val =
        match operator, left_val, right_val with
        | Add, VInt left_int, VInt right_int -> VInt (left_int + right_int)
        | AddF, VFloat left_float, VFloat right_float -> VFloat (left_float +. right_float)
        | Sub, VInt left_int, VInt right_int -> VInt (left_int - right_int)
        | SubF, VFloat left_float, VFloat right_float -> VFloat (left_float -. right_float)
        | Mul, VInt left_int, VInt right_int -> VInt (left_int * right_int)
        | MulF, VFloat left_float, VFloat right_float -> VFloat (left_float *. right_float)
        | Div, VInt left_int, VInt right_int -> if right_int = 0 then raise DivByZero else VInt (left_int / right_int)
        | DivF, VFloat left_float, VFloat right_float -> VFloat (left_float /. right_float)
        | Mod, VInt left_int, VInt right_int -> if right_int = 0 then failwith "Error: div by 0" else VInt (left_int mod right_int)
        | PowF, VFloat base, VFloat exponent -> VFloat (base ** exponent)
        | Eq, _, _ -> eval_eq left_val right_val
        | Neq, _, _ -> eval_neq left_val right_val
        | Lt, _, _ -> eval_lt left_val right_val
        | Lte, _, _ -> eval_lte left_val right_val
        | Gt, _, _ -> eval_gt left_val right_val
        | Gte, _, _ -> eval_gte left_val right_val
        | And, VBool false, _ -> VBool false
        | And, VBool true, bool_expr -> bool_expr
        | Or, VBool true, _ -> VBool true
        | Or, VBool false, bool_expr -> bool_expr
        | Comma, _, _ -> VPair (left_val, right_val)
        | Cons, head, VList tail -> VList (head :: tail)
        | Concat, VList list1, VList list2 -> VList (list1 @ list2)
        | _ -> failwith "Error"
    
      and eval_eq left_val right_val =
        match left_val, right_val with
        | VClos _, _ | _, VClos _ -> raise CompareFunVals
        | VInt left_int, VInt right_int -> VBool (left_int = right_int)
        | VFloat left_float, VFloat right_float -> VBool (left_float = right_float)
        | VBool left_bool, VBool right_bool -> VBool (left_bool = right_bool)
        | VUnit, VUnit -> VBool true
        | VList list1, VList list2 -> VBool (list1 = list2)
        | VPair (fst1, snd1), VPair (fst2, snd2) -> VBool (fst1 = fst2 && snd1 = snd2)
        | VSome opt1, VSome opt2 -> VBool (opt1 = opt2)
        | VNone, VNone -> VBool true
        | _ -> VBool false
    
      and eval_neq left_val right_val =
        match eval_eq left_val right_val with
        | VBool result -> VBool (not result)
        | _ -> failwith "Error"
    
      and eval_lt left_val right_val =
        match left_val, right_val with
        | VInt left_int, VInt right_int -> VBool (left_int < right_int)
        | VFloat left_float, VFloat right_float -> VBool (left_float < right_float)
        | VBool left_bool, VBool right_bool -> VBool ((not left_bool) && right_bool)
        | VList list1, VList list2 -> VBool (list1 < list2)
        | VSome opt1, VSome opt2 -> VBool (opt1 < opt2)
        | VNone, VSome _ -> VBool true
        | VNone, VNone -> VBool false
        | _ -> failwith "Error"
    
      and eval_lte left_val right_val =
        match left_val, right_val with
        | VInt left_int, VInt right_int -> VBool (left_int <= right_int)
        | VFloat left_float, VFloat right_float -> VBool (left_float <= right_float)
        | VBool left_bool, VBool right_bool -> VBool ((not right_bool) || left_bool)
        | VList list1, VList list2 -> VBool (list1 <= list2)
        | VSome opt1, VSome opt2 -> VBool (opt1 <= opt2)
        | VNone, VSome _ -> VBool true
        | VNone, VNone -> VBool true
        | _ -> failwith "Error"
    
      and eval_gt left_val right_val =
        match left_val, right_val with
        | VInt left_int, VInt right_int -> VBool (left_int > right_int)
        | VFloat left_float, VFloat right_float -> VBool (left_float > right_float)
        | VBool left_bool, VBool right_bool -> VBool (left_bool && not right_bool)
        | VPair (fst1, snd1), VPair (fst2, snd2) -> VBool ((fst1, snd1) > (fst2, snd2))
        | VSome opt1, VSome opt2 -> VBool (opt1 > opt2)
        | VNone, VSome _ -> VBool false
        | VNone, VNone -> VBool false
        | VList list1, VList list2 -> VBool (list1 > list2)
        | _ -> failwith "Error"
    
      and eval_gte left_val right_val =
        match left_val, right_val with
        | VInt left_int, VInt right_int -> VBool (left_int >= right_int)
        | VFloat left_float, VFloat right_float -> VBool (left_float >= right_float)
        | VBool left_bool, VBool right_bool -> VBool (left_bool || not right_bool)
        | VList list1, VList list2 -> VBool (list1 >= list2)
        | VSome opt1, VSome opt2 -> VBool (opt1 >= opt2)
        | VSome _, VNone -> VBool true
        | VNone, VNone -> VBool true
        | VUnit, VUnit -> VBool true
        | _ -> failwith "Error"
    
      and eval_opt_match opt_value opt_name opt_case none_case =
        match opt_value with
        | VSome some_val -> eval_expr (Env.add opt_name some_val environment) opt_case
        | VNone -> eval_expr environment none_case
        | _ -> failwith "Error"
    
      and eval_if condition then_branch else_branch =
        match condition with
        | VBool true -> evaluate then_branch
        | VBool false -> evaluate else_branch
        | _ -> failwith "Error"
    
      and eval_list_match list_value head_name tail_name cons_case nil_case =
        match list_value with
        | VList (head::tail) ->
            eval_expr (Env.add tail_name (VList tail) (Env.add head_name head environment)) cons_case
        | VList [] -> eval_expr environment nil_case
        | _ -> failwith "Error"
    
      and eval_pair_match pair_value first_name second_name case_expr =
        match pair_value with
        | VPair (fst, snd) -> eval_expr (Env.add second_name snd (Env.add first_name fst environment)) case_expr
        | _ -> failwith "Error"
    
      and eval_assert assertion =
        match assertion with
        | VBool true -> VUnit
        | _ -> raise AssertFail
    
      and eval_let is_recursive let_name let_value let_body =
        if not is_recursive then
          eval_expr (Env.add let_name (evaluate let_value) environment) let_body
        else
          match evaluate let_value with
          | VClos {name=None; arg=closure_arg; body=closure_body; env=closure_env} ->
              let rec_env = Env.add let_name (VClos {name=Some let_name; arg=closure_arg; body=closure_body; env=closure_env}) environment in
              eval_expr rec_env let_body
          | VClos {name=Some _; _} -> raise RecWithoutArg
          | _ -> failwith "Error"
      in evaluate expr
    


let type_check prog =
  let rec go env = function
    | [] -> Some (Forall ([], TUnit))
    | { is_rec; name; value } :: rest ->
      match type_of env (Let { is_rec; name; value; body = Var name }) with
      | Some ty -> go (Env.add name ty env) rest
      | None -> None
  in
  go Env.empty prog

  let eval p =
    let rec nest = function
      | [] -> Unit
      | [{is_rec;name;value}] -> Let {is_rec;name;value;body = Var name}
      | {is_rec;name;value} :: ls -> Let {is_rec;name;value;body = nest ls}
    in eval_expr Env.empty (nest p)

let interp input =
  match parse input with
  | Some prog -> (
      match type_check prog with
      | Some ty -> Ok (eval prog, ty)
      | None -> Error TypeError
    )
  | None -> Error ParseError