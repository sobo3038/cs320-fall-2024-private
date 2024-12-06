open Utils
include My_parser

exception AssertFail
exception DivByZero
exception RecWithoutArg
exception CompareFunVals

let rec substitute subst ty =
  match ty with
  | TVar x -> (try List.assoc x subst with Not_found -> ty)
  | TFun (t1, t2) -> TFun (substitute subst t1, substitute subst t2)
  | TPair (t1, t2) -> TPair (substitute subst t1, substitute subst t2)
  | TList t -> TList (substitute subst t)
  | TOption t -> TOption (substitute subst t)
  | _ -> ty

let substitute_constraints subst constraints =
  List.map (fun (t1, t2) -> (substitute subst t1, substitute subst t2)) constraints

let rec unify ty constraints =
  match constraints with
  | [] -> Some (Forall ([], ty))
  | (t1, t2) :: rest when t1 = t2 -> unify ty rest
  | (TVar x, t) :: rest | (t, TVar x) :: rest ->
      if substitute [(x, t)] t = TVar x then None 
      else
        let subst = [(x, t)] in
        unify (substitute subst ty) (substitute_constraints subst rest)
  | (TFun (t1a, t1b), TFun (t2a, t2b)) :: rest ->
      unify ty ((t1a, t2a) :: (t1b, t2b) :: rest)
  | (TPair (t1a, t1b), TPair (t2a, t2b)) :: rest ->
      unify ty ((t1a, t2a) :: (t1b, t2b) :: rest)
  | (TList t1, TList t2) :: rest | (TOption t1, TOption t2) :: rest ->
      unify ty ((t1, t2) :: rest)
  | _ -> None

let rec type_of env expr =
  match expr with
  | Unit -> Some (Forall ([], TUnit))
  | True | False -> Some (Forall ([], TBool))
  | Int _ -> Some (Forall ([], TInt))
  | Float _ -> Some (Forall ([], TFloat))
  | Var x -> Env.find_opt x env
  | Fun (arg, annot, body) ->
      let arg_ty = Option.value annot ~default:(TVar (gensym ())) in
      let env = Env.add arg (Forall ([], arg_ty)) env in
      (match type_of env body with
      | Some (Forall (_, body_ty)) -> Some (Forall ([], TFun (arg_ty, body_ty)))
      | None -> None)
  | App (f, arg) ->
      let arg_ty = TVar (gensym ()) in
      let ret_ty = TVar (gensym ()) in
      (match type_of env f, type_of env arg with
      | Some (Forall (_, f_ty)), Some (Forall (_, actual_arg_ty)) ->
          let constraints = [(f_ty, TFun (arg_ty, ret_ty)); (arg_ty, actual_arg_ty)] in
          (match unify ret_ty constraints with
          | Some (Forall (_, unified_ty)) -> Some (Forall ([], unified_ty))
          | None -> None)
      | _ -> None)
  | If (cond, then_branch, else_branch) ->
      (match type_of env cond, type_of env then_branch, type_of env else_branch with
      | Some (Forall (_, TBool)), Some (Forall (_, t1)), Some (Forall (_, t2)) ->
          let constraints = [(t1, t2)] in
          (match unify t1 constraints with
          | Some (Forall (_, unified_ty)) -> Some (Forall ([], unified_ty))
          | None -> None)
      | _ -> None)
  | Let { is_rec; name; value; body } ->
      let env' = 
        if is_rec then
          let rec_ty = TVar (gensym ()) in
          Env.add name (Forall ([], rec_ty)) env
        else env
      in
      (match type_of env' value with
      | Some (Forall (_, value_ty)) ->
          let env' = Env.add name (Forall ([], value_ty)) env' in
          type_of env' body
      | None -> None)
  | _ -> None

let rec eval_expr env expr =
  match expr with
  | Unit -> VUnit
  | True -> VBool true
  | False -> VBool false
  | Int n -> VInt n
  | Float f -> VFloat f
  | Var x -> (try Env.find x env with Not_found -> failwith "Unbound variable")
  | If (cond, then_branch, else_branch) ->
      (match eval_expr env cond with
      | VBool true -> eval_expr env then_branch
      | VBool false -> eval_expr env else_branch
      | _ -> failwith "Non-boolean condition")
  | Fun (arg, _, body) -> VClos { name = None; arg; body; env }
  | App (f, arg) ->
      (match eval_expr env f with
      | VClos { name = _; arg = param; body; env = closure_env } ->
          let arg_val = eval_expr env arg in
          let env' = Env.add param arg_val closure_env in
          eval_expr env' body
      | _ -> failwith "Application to non-function")
  | Let { is_rec = false; name; value; body } ->
      let value_val = eval_expr env value in
      eval_expr (Env.add name value_val env) body
  | Let { is_rec = true; name; value; body } ->
      (match value with
      | Fun (arg, _, body_fun) ->
          let rec_env = Env.add name (VClos { name = Some name; arg; body = body_fun; env }) env in
          eval_expr rec_env body
      | _ -> raise RecWithoutArg)
  | _ -> failwith "Unsupported expression"

let type_check =
  let rec go ctxt = function
    | [] -> Some (Forall ([], TUnit))
    | { is_rec = _; name; value } :: ls ->
        match type_of ctxt (Let { is_rec = false; name; value; body = Var name }) with
        | Some ty -> go (Env.add name ty ctxt) ls
        | None -> None
  in go Env.empty

let eval p =
  let rec nest = function
    | [] -> Unit
    | [{ is_rec; name; value }] -> Let { is_rec; name; value; body = Var name }
    | { is_rec; name; value } :: ls -> Let { is_rec; name; value; body = nest ls }
  in eval_expr Env.empty (nest p)

let interp input =
  match parse input with
  | Some prog -> (
      match type_check prog with
      | Some ty -> Ok (eval prog, ty)
      | None -> Error TypeError)
  | None -> Error ParseError
