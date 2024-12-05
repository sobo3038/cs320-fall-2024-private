open Utils
include My_parser

exception AssertFail
exception DivByZero
exception RecWithoutArg
exception CompareFunVals

let substitute subst ty =
  let rec apply subst ty =
    match ty with
    | TVar x -> (
        match List.assoc_opt x subst with
        | Some t -> apply subst t
        | None -> ty)
    | TFun (a, b) -> TFun (apply subst a, apply subst b)
    | TPair (a, b) -> TPair (apply subst a, apply subst b)
    | TList t -> TList (apply subst t)
    | TOption t -> TOption (apply subst t)
    | _ -> ty
  in
  apply subst ty

let unify ty constraints =
  let rec contains_binding x subst =
    match subst with
    | [] -> false
    | (y, _) :: rest -> x = y || contains_binding x rest
  in

  let rec find_binding x subst =
    match subst with
    | [] -> None
    | (y, t) :: rest -> if x = y then Some t else find_binding x rest
  in

  let rec unify_types t1 t2 subst =
    match (t1, t2) with
    | TVar x, TVar y when x = y -> Some subst
    | TVar x, t when not (contains_binding x subst) -> Some ((x, t) :: subst)
    | t, TVar x when not (contains_binding x subst) -> Some ((x, t) :: subst)
    | TVar x, t -> (
        match find_binding x subst with
        | Some bound_ty -> unify_types bound_ty t subst
        | None -> Some ((x, t) :: subst))
    | t, TVar x -> (
        match find_binding x subst with
        | Some bound_ty -> unify_types t bound_ty subst
        | None -> Some ((x, t) :: subst))
    | TFun (a1, b1), TFun (a2, b2) -> (
        match unify_types a1 a2 subst with
        | Some new_subst -> unify_types b1 b2 new_subst
        | None -> None)
    | TPair (a1, b1), TPair (a2, b2) -> (
        match unify_types a1 a2 subst with
        | Some new_subst -> unify_types b1 b2 new_subst
        | None -> None)
    | TList t1, TList t2 | TOption t1, TOption t2 -> unify_types t1 t2 subst
    | TUnit, TUnit | TInt, TInt | TFloat, TFloat | TBool, TBool -> Some subst
    | _ -> None
  in

  let rec solve constraints subst =
    match constraints with
    | [] -> Some subst
    | (t1, t2) :: rest -> (
        match unify_types (substitute subst t1) (substitute subst t2) subst with
        | Some new_subst -> solve rest new_subst
        | None -> None)
  in

  match solve constraints [] with
  | Some subst -> Some (Forall ([], substitute subst ty))
  | None -> None


  let type_of env expr =
  let rec infer env expr =
    match expr with
    | Unit -> (TUnit, [])
    | True | False -> (TBool, [])
    | Int _ -> (TInt, [])
    | Float _ -> (TFloat, [])
    | Nil -> (TList (TVar (gensym ())), [])
    | Var x -> (
        match Env.find_opt x env with
        | Some (Forall (_, t)) -> (t, [])
        | None -> failwith "Unbound variable")
    | If (cond, then_branch, else_branch) ->
        let (t1, c1) = infer env cond in
        let (t2, c2) = infer env then_branch in
        let (t3, c3) = infer env else_branch in
        (t2, (t1, TBool) :: (t2, t3) :: (c1 @ c2 @ c3))
    | Fun (arg, annot, body) ->
        let arg_ty = Option.value annot ~default:(TVar (gensym ())) in
        let env = Env.add arg (Forall ([], arg_ty)) env in
        let (body_ty, constraints) = infer env body in
        (TFun (arg_ty, body_ty), constraints)
    | App (f, arg) ->
        let (f_ty, c1) = infer env f in
        let (arg_ty, c2) = infer env arg in
        let ret_ty = TVar (gensym ()) in
        (ret_ty, (f_ty, TFun (arg_ty, ret_ty)) :: (c1 @ c2))
    | Let { is_rec = _; name; value; body } ->
        let (v_ty, c1) = infer env value in
        (match unify v_ty c1 with
         | Some (Forall (_, unified_ty)) ->
             let env = Env.add name (Forall ([], unified_ty)) env in
             infer env body
         | None -> failwith "Unification failed")
    | _ -> failwith "Not implemented"
  in
  let (ty, constraints) = infer env expr in
  match unify ty constraints with
  | Some (Forall (_, final_ty)) -> Some (Forall ([], final_ty))
  | None -> None



let rec eval_expr env expr =
  match expr with
  | Unit -> VUnit
  | True -> VBool true
  | False -> VBool false
  | Int n -> VInt n
  | Float f -> VFloat f
  | Var x -> (try Env.find x env with Not_found -> failwith "Unbound variable")
  | If (cond, then_branch, else_branch) -> (
      match eval_expr env cond with
      | VBool true -> eval_expr env then_branch
      | VBool false -> eval_expr env else_branch
      | _ -> failwith "Non-boolean condition")
  | Fun (arg, _, body) -> VClos { name = None; arg; body; env }
  | App (f, arg) -> (
      match eval_expr env f with
      | VClos { name = _; arg = param; body; env = closure_env } ->
          let arg_val = eval_expr env arg in
          eval_expr (Env.add param arg_val closure_env) body
      | _ -> failwith "Non-function application")
  | Let { is_rec = false; name; value; body } ->
      let value_val = eval_expr env value in
      eval_expr (Env.add name value_val env) body
  | Let { is_rec = true; name; value; body } -> (
      match value with
      | Fun (arg, _, body_fun) ->
          let rec_env = Env.add name (VClos { name = Some name; arg; body = body_fun; env }) env in
          eval_expr rec_env body
      | _ -> raise RecWithoutArg)
  | _ -> failwith "Not implemented"





let type_check =
  let rec go ctxt = function
    | [] -> Some (Forall ([], TUnit))
    | { is_rec = _; name; value } :: ls ->
        match type_of ctxt (Let { is_rec = false; name; value; body = Var name }) with
        | Some ty -> (
            match ls with
            | [] -> Some ty
            | _ -> go (Env.add name ty ctxt) ls)
        | None -> None
  in
  go Env.empty




let eval p =
  let rec nest = function
    | [] -> Unit
    | [{ is_rec; name; value }] -> Let { is_rec; name; value; body = Var name }
    | { is_rec; name; value } :: ls -> Let { is_rec; name; value; body = nest ls }
  in
  eval_expr Env.empty (nest p)



let interp input =
  match parse input with
  | Some prog -> (
      match type_check prog with
      | Some ty -> Ok (eval prog, ty)
      | None -> Error TypeError)
  | None -> Error ParseError
