open Utils

let parse = My_parser.parse;;
exception AssertFail
exception DivByZero
let desugar prog =
  let rec translate_toplevel = function
    | [] -> Unit
    | { is_rec; name; args; ty; value } :: rest ->
        let rec curry_args args expr =
          match args with
          | [] -> expr
          | (x, t) :: xs -> Fun (x, t, curry_args xs expr)
        in
        Let {
          is_rec;
          name;
          ty = List.fold_right (fun (_, t) acc -> FunTy (t, acc)) args ty;
          value = curry_args args (translate_expr value);
          body = translate_toplevel rest;
        }
  and translate_expr = function
    | SUnit -> Unit
    | STrue -> True
    | SFalse -> False
    | SNum n -> Num n
    | SVar x -> Var x
    | SFun { arg = (x, t); args; body } ->
        List.fold_right (fun (a, t) acc -> Fun (a, t, acc)) ((x, t) :: args) (translate_expr body)
    | SApp (e1, e2) -> App (translate_expr e1, translate_expr e2)
    | SLet { is_rec; name; args; ty; value; body } ->
        Let {
          is_rec;
          name;
          ty = List.fold_right (fun (_, t) acc -> FunTy (t, acc)) args ty;
          value = List.fold_right (fun (a, t) acc -> Fun (a, t, acc)) args (translate_expr value);
          body = translate_expr body;
        }
    | SIf (cond, t_branch, f_branch) ->
        If (translate_expr cond, translate_expr t_branch, translate_expr f_branch)
    | SBop (op, left, right) -> Bop (op, translate_expr left, translate_expr right)
    | SAssert e -> Assert (translate_expr e)
  in
  translate_toplevel prog

let type_of expr =
  let rec check_type env = function
    | Unit -> Ok UnitTy
    | True | False -> Ok BoolTy
    | Num _ -> Ok IntTy
    | Var x -> (try Ok (Env.find x env) with Not_found -> Error (UnknownVar x))
    | If (cond, t_branch, f_branch) ->
        (match (check_type env cond, check_type env t_branch, check_type env f_branch) with
        | Ok BoolTy, Ok t1, Ok t2 when t1 = t2 -> Ok t1
        | Ok BoolTy, Ok t1, Ok t2 -> Error (IfTyErr (t1, t2))
        | Ok ty, _, _ -> Error (IfCondTyErr ty)
        | err, _, _ -> err)
    | Bop (op, left, right) ->
        (match (check_type env left, check_type env right) with
        | Ok IntTy, Ok IntTy -> if op = And || op = Or then Error (OpTyErrL (op, BoolTy, IntTy)) else Ok IntTy
        | Ok BoolTy, Ok BoolTy -> if op = And || op = Or then Ok BoolTy else Error (OpTyErrL (op, IntTy, BoolTy))
        | _ -> Error (OpTyErrR (op, BoolTy, IntTy)))
    | Fun (x, t, body) ->
        let extended_env = Env.add x t env in
        (match check_type extended_env body with Ok ret_t -> Ok (FunTy (t, ret_t)) | err -> err)
    | App (func, arg) ->
        (match (check_type env func, check_type env arg) with
        | Ok (FunTy (arg_ty, ret_ty)), Ok t when t = arg_ty -> Ok ret_ty
        | Ok (FunTy (arg_ty, _)), Ok t -> Error (FunArgTyErr (arg_ty, t))
        | Ok t, _ -> Error (FunAppTyErr t)
        | err, _ -> err)
    | Let { is_rec; name; ty; value; body } ->
        let temp_env = if is_rec then Env.add name ty env else env in
        (match check_type temp_env value with
        | Ok value_ty when value_ty = ty -> check_type (Env.add name ty temp_env) body
        | Ok value_ty -> Error (LetTyErr (ty, value_ty))
        | err -> err)
    | Assert e -> (match check_type env e with Ok BoolTy -> Ok UnitTy | Ok t -> Error (AssertTyErr t) | err -> err)
  in
  check_type Env.empty expr

  let eval expr =
    let rec execute env = function
      | Unit -> VUnit
      | True -> VBool true
      | False -> VBool false
      | Num n -> VNum n
      | Var x -> (
          try Env.find x env
          with Not_found -> failwith ("Undefined variable: " ^ x)
        )
      | If (cond, t_branch, f_branch) -> (
          match execute env cond with
          | VBool true -> execute env t_branch
          | VBool false -> execute env f_branch
          | _ -> failwith "Condition must evaluate to a boolean"
        )
      | Bop (op, left, right) ->
          let v1 = execute env left in
          let v2 = execute env right in
          (match (op, v1, v2) with
          | Add, VNum n1, VNum n2 -> VNum (n1 + n2)
          | Sub, VNum n1, VNum n2 -> VNum (n1 - n2)
          | Mul, VNum n1, VNum n2 -> VNum (n1 * n2)
          | Div, VNum n1, VNum n2 -> if n2 = 0 then raise DivByZero else VNum (n1 / n2)
          | Mod, VNum n1, VNum n2 -> if n2 = 0 then raise DivByZero else VNum (n1 mod n2)
          | Lt, VNum n1, VNum n2 -> VBool (n1 < n2)
          | Lte, VNum n1, VNum n2 -> VBool (n1 <= n2)
          | Gt, VNum n1, VNum n2 -> VBool (n1 > n2)
          | Gte, VNum n1, VNum n2 -> VBool (n1 >= n2)
          | Eq, VNum n1, VNum n2 -> VBool (n1 = n2)
          | Eq, VBool b1, VBool b2 -> VBool (b1 = b2)
          | Neq, VNum n1, VNum n2 -> VBool (n1 <> n2)
          | Neq, VBool b1, VBool b2 -> VBool (b1 <> b2)
          | And, VBool b1, VBool b2 -> VBool (b1 && b2)
          | Or, VBool b1, VBool b2 -> VBool (b1 || b2)
          | _ -> failwith "Invalid binary operation"
          )
      | Fun (arg, _, body) -> VClos { name = None; arg; body; env }
      | App (func, arg) -> (
          match execute env func with
          | VClos { name; arg = param; body; env = closure_env } ->
              let arg_val = execute env arg in
              let extended_env =
                match name with
                | Some func_name ->
                    Env.add func_name (VClos { name; arg = param; body; env = closure_env })
                      (Env.add param arg_val closure_env)
                | None -> Env.add param arg_val closure_env
              in
              execute extended_env body
          | _ -> failwith "Application must be to a function"
        )
      | Let { is_rec; name; value; body; _ } -> (
          let value_closure =
            match (is_rec, value) with
            | true, Fun (arg, _, body) ->
                VClos { name = Some name; arg; body; env }
            | false, _ -> execute env value
            | _ -> failwith "Invalid let binding"
          in
          let extended_env = Env.add name value_closure env in
          execute extended_env body
        )
      | Assert e -> (
          match execute env e with
          | VBool true -> VUnit
          | _ -> raise AssertFail
        )
    in
    execute Env.empty expr
  

let interp str =
  match parse str with
  | Some prog -> (
      let desugared = desugar prog in
      match type_of desugared with
      | Ok _ -> Ok (eval desugared)
      | Error e -> Error e)
  | None -> Error ParseErr
