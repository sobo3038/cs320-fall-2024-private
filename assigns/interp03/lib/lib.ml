open Utils
include My_parser

exception AssertFail
exception DivByZero
exception RecWithoutArg
exception CompareFunVals

(* Unification *)
let rec unify ty constraints =
  let rec free_vars ty =
    match ty with
    | TVar x -> [x]
    | TFun (t1, t2) | TPair (t1, t2) -> free_vars t1 @ free_vars t2
    | TList t | TOption t -> free_vars t
    | _ -> []
  in
  let rec occurs x ty =
    match ty with
    | TVar y -> x = y
    | TFun (t1, t2) | TPair (t1, t2) -> occurs x t1 || occurs x t2
    | TList t | TOption t -> occurs x t
    | _ -> false
  in
  let rec apply_subst subst ty =
    match ty with
    | TVar x -> (try List.assoc x subst with Not_found -> ty)
    | TFun (t1, t2) -> TFun (apply_subst subst t1, apply_subst subst t2)
    | TPair (t1, t2) -> TPair (apply_subst subst t1, apply_subst subst t2)
    | TList t -> TList (apply_subst subst t)
    | TOption t -> TOption (apply_subst subst t)
    | _ -> ty
  in
  let apply_subst_to_constraints subst constraints =
    List.map (fun (t1, t2) -> (apply_subst subst t1, apply_subst subst t2)) constraints
  in
  let sort_uniq cmp lst =
    let sorted = List.sort cmp lst in
    let rec dedup acc = function
      | [] -> List.rev acc
      | [x] -> List.rev (x :: acc)
      | x :: (y :: _ as rest) -> if cmp x y = 0 then dedup acc rest else dedup (x :: acc) rest
    in
    dedup [] sorted
  in
  match constraints with
  | [] -> Some (Forall (sort_uniq compare (free_vars ty), ty))
  | (t1, t2) :: rest when t1 = t2 -> unify ty rest
  | (TVar x, t) :: rest | (t, TVar x) :: rest ->
      if occurs x t then None
      else
        let subst = [(x, t)] in
        let updated_ty = apply_subst subst ty in
        let updated_constraints = apply_subst_to_constraints subst rest in
        unify updated_ty updated_constraints
  | (TFun (t1a, t1b), TFun (t2a, t2b)) :: rest ->
      unify ty ((t1a, t2a) :: (t1b, t2b) :: rest)
  | (TPair (t1a, t1b), TPair (t2a, t2b)) :: rest ->
      unify ty ((t1a, t2a) :: (t1b, t2b) :: rest)
  | (TList t1, TList t2) :: rest | (TOption t1, TOption t2) :: rest ->
      unify ty ((t1, t2) :: rest)
  | _ -> None


(* Type Inference *)
let type_of env expr =
  (* Helper Functions *)
  
  (* Applies a substitution to a type *)
  let rec apply_subst subst ty =
    match ty with
    | TVar x -> (try List.assoc x subst with Not_found -> ty)
    | TFun (t1, t2) -> TFun (apply_subst subst t1, apply_subst subst t2)
    | TPair (t1, t2) -> TPair (apply_subst subst t1, apply_subst subst t2)
    | TList t -> TList (apply_subst subst t)
    | TOption t -> TOption (apply_subst subst t)
    | _ -> ty
  in

  (* Gathers all free variables in a type *)
  let rec free_vars ty =
    match ty with
    | TVar x -> [x]
    | TFun (t1, t2) | TPair (t1, t2) -> free_vars t1 @ free_vars t2
    | TList t | TOption t -> free_vars t
    | _ -> []
  in

  (* Custom sort_uniq function to deduplicate free variables *)
  let sort_uniq cmp lst =
    let sorted = List.sort cmp lst in
    let rec dedup acc = function
      | [] -> List.rev acc
      | [x] -> List.rev (x :: acc)
      | x :: (y :: _ as rest) -> if cmp x y = 0 then dedup acc rest else dedup (x :: acc) rest
    in
    dedup [] sorted
  in

  (* Instantiates a type scheme with fresh type variables *)
  let instantiate (vars, ty) =
    let subst = List.map (fun var -> (var, TVar (gensym ()))) vars in
    apply_subst subst ty
  in

  (* Unifies constraints and returns the most general unifier *)
  let rec unify ty constraints =
    match constraints with
    | [] -> 
        let free = sort_uniq compare (free_vars ty) in
        Some (Forall (free, ty))
    | (t1, t2) :: rest when t1 = t2 -> unify ty rest
    | (TVar x, t) :: rest | (t, TVar x) :: rest ->
        if List.mem x (free_vars t) then None
        else
          let subst = [(x, t)] in
          unify (apply_subst subst ty) (List.map (fun (t1, t2) -> (apply_subst subst t1, apply_subst subst t2)) rest)
    | (TFun (t1a, t1b), TFun (t2a, t2b)) :: rest ->
        unify ty ((t1a, t2a) :: (t1b, t2b) :: rest)
    | (TPair (t1a, t1b), TPair (t2a, t2b)) :: rest ->
        unify ty ((t1a, t2a) :: (t1b, t2b) :: rest)
    | (TList t1, TList t2) :: rest | (TOption t1, TOption t2) :: rest ->
        unify ty ((t1, t2) :: rest)
    | _ -> None
  in

  (* Infers the type of an expression *)
  let rec infer env expr =
    match expr with
    | Unit -> (TUnit, [])
    | True | False -> (TBool, [])
    | Int _ -> (TInt, [])
    | Float _ -> (TFloat, [])
    | Var x -> (
        match Env.find_opt x env with
        | Some (Forall (vars, ty)) -> (instantiate (vars, ty), [])
        | None -> failwith ("Unbound variable: " ^ x)
      )
    | Fun (arg, annot, body) ->
        let arg_ty = match annot with
          | Some ty -> ty
          | None -> TVar (gensym ())
        in
        let env' = Env.add arg (Forall ([], arg_ty)) env in
        let body_ty, constraints = infer env' body in
        (TFun (arg_ty, body_ty), constraints)
    | App (f, arg) ->
        let fun_ty, c1 = infer env f in
        let arg_ty, c2 = infer env arg in
        let ret_ty = TVar (gensym ()) in
        (ret_ty, (fun_ty, TFun (arg_ty, ret_ty)) :: c1 @ c2)
    | If (cond, then_branch, else_branch) ->
        let cond_ty, c1 = infer env cond in
        let then_ty, c2 = infer env then_branch in
        let else_ty, c3 = infer env else_branch in
        (then_ty, (cond_ty, TBool) :: (then_ty, else_ty) :: c1 @ c2 @ c3)
    | Let { is_rec = false; name; value; body } ->
        let val_ty, c1 = infer env value in
        let env' = Env.add name (Forall ([], val_ty)) env in
        let body_ty, c2 = infer env' body in
        (body_ty, c1 @ c2)
    | Let { is_rec = true; name; value; body } ->
        let fresh_ty = TVar (gensym ()) in
        let env' = Env.add name (Forall ([], fresh_ty)) env in
        let val_ty, c1 = infer env' value in
        let env'' = Env.add name (Forall ([], val_ty)) env in
        let body_ty, c2 = infer env'' body in
        (body_ty, c1 @ c2)
    | PairMatch { matched; fst_name; snd_name; case } ->
        let matched_ty, c1 = infer env matched in
        let fst_ty = TVar (gensym ()) in
        let snd_ty = TVar (gensym ()) in
        let env' = Env.add fst_name (Forall ([], fst_ty)) (Env.add snd_name (Forall ([], snd_ty)) env) in
        let case_ty, c2 = infer env' case in
        (case_ty, (matched_ty, TPair (fst_ty, snd_ty)) :: c1 @ c2)
    | _ -> failwith "Unsupported expression in infer"
  in

  (* Main body of type_of *)
  try
    let ty, constraints = infer env expr in
    match unify ty constraints with
    | Some scheme -> Some scheme
    | None -> None
  with _ -> None

  

(* Evaluation *)
let rec eval_expr env expr =
  match expr with
  | Unit -> VUnit
  | True -> VBool true
  | False -> VBool false
  | Int n -> VInt n
  | Float f -> VFloat f
  | ENone -> VNone
  | Nil -> VList []
  | Var x -> Env.find x env
  | Fun (arg, _, body) -> VClos { name = None; arg; body; env }
  | App (f, arg) -> (
      match eval_expr env f with
      | VClos { name = _; arg = param; body; env = closure_env } ->
          let arg_val = eval_expr env arg in
          let env' = Env.add param arg_val closure_env in
          eval_expr env' body    
      | _ -> failwith "Application to non-function"
    )
  | Bop (op, e1, e2) -> (
      let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      match (op, v1, v2) with
      | (Add, VInt x, VInt y) -> VInt (x + y)
      | (Sub, VInt x, VInt y) -> VInt (x - y)
      | (Mul, VInt x, VInt y) -> VInt (x * y)
      | (Div, VInt x, VInt y) when y <> 0 -> VInt (x / y)
      | (Mod, VInt x, VInt y) when y <> 0 -> VInt (x mod y)
      | (And, VBool b1, VBool b2) -> VBool (b1 && b2)
      | (Or, VBool b1, VBool b2) -> VBool (b1 || b2)
      | _ -> failwith "Unsupported binary operation or mismatched types"
    )
  | If (cond, then_branch, else_branch) -> (
      match eval_expr env cond with
      | VBool true -> eval_expr env then_branch
      | VBool false -> eval_expr env else_branch
      | _ -> failwith "Non-boolean condition in if-expression"
    )
  | Let { is_rec = false; name; value; body } ->
      let value_val = eval_expr env value in
      eval_expr (Env.add name value_val env) body
  | Let { is_rec = true; name; value; body } -> (
      match value with
      | Fun (arg, _, body_fun) ->
          let rec_env = Env.add name (VClos { name = Some name; arg; body = body_fun; env }) env in
          eval_expr rec_env body
      | _ -> raise RecWithoutArg
    )
  | OptMatch { matched; some_name; some_case; none_case } -> (
      match eval_expr env matched with
      | VSome v -> eval_expr (Env.add some_name v env) some_case
      | VNone -> eval_expr env none_case
      | _ -> failwith "Expected an option"
    )
  | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } -> (
      match eval_expr env matched with
      | VList (vh :: vt) ->
          let env = Env.add hd_name vh (Env.add tl_name (VList vt) env) in
          eval_expr env cons_case
      | VList [] -> eval_expr env nil_case
      | _ -> failwith "Expected a list"
    )
  | PairMatch { matched; fst_name; snd_name; case } -> (
      match eval_expr env matched with
      | VPair (v1, v2) ->
          let env = Env.add fst_name v1 (Env.add snd_name v2 env) in
          eval_expr env case
      | _ -> failwith "Expected a pair"
    )
  | ESome e -> VSome (eval_expr env e)
  | Annot (e, _) -> eval_expr env e
  | Assert e -> (
      match eval_expr env e with
      | VBool true -> VUnit
      | VBool false -> raise AssertFail
      | _ -> failwith "Assertion expects a boolean"
    )


(* Type Checking *)
let type_check prog =
  let rec go env = function
    | [] -> Some (Forall ([], TUnit))
    | { is_rec; name; value } :: rest ->
        (match type_of env (Let { is_rec; name; value; body = Var name }) with
        | Some ty -> go (Env.add name ty env) rest
        | None -> None)
  in
  go Env.empty prog

(* Program Evaluation *)
let eval prog =
  let rec nest = function
    | [] -> Unit
    | [{ is_rec; name; value }] -> Let { is_rec; name; value; body = Var name }
    | { is_rec; name; value } :: rest -> Let { is_rec; name; value; body = nest rest }
  in
  eval_expr Env.empty (nest prog)

(* Interpreter *)
let interp input =
  match parse input with
  | Some prog -> (match type_check prog with Some ty -> Ok (eval prog, ty) | None -> Error TypeError)
  | None -> Error ParseError
