open Utils

(* Parse function *)
let parse = My_parser.parse

(* Desugar function *)
let desugar (prog : prog) : expr =
  let rec transform_fun_ty args ty =
    match args with
    | [] -> ty
    | (_, arg_ty) :: remaining -> FunTy (arg_ty, transform_fun_ty remaining ty)
  in
  let rec create_nested_funs args body =
    match args with
    | [] -> body
    | (arg_name, arg_ty) :: remaining ->
        Fun (arg_name, arg_ty, create_nested_funs remaining body)
  in
  let rec desugar_expr = function
    | SUnit -> Unit
    | STrue -> True
    | SFalse -> False
    | SNum n -> Num n
    | SVar x -> Var x
    | SFun { arg = (x, ty); args; body } ->
        Fun (x, ty, create_nested_funs args (desugar_expr body))
    | SApp (e1, e2) -> App (desugar_expr e1, desugar_expr e2)
    | SLet { is_rec; name; args; ty; value; body } ->
        Let {
          is_rec;
          name;
          ty = transform_fun_ty args ty;
          value = create_nested_funs args (desugar_expr value);
          body = desugar_expr body;
        }
    | SIf (e1, e2, e3) ->
        If (desugar_expr e1, desugar_expr e2, desugar_expr e3)
    | SBop (op, e1, e2) -> Bop (op, desugar_expr e1, desugar_expr e2)
    | SAssert e -> Assert (desugar_expr e)
  in
  let rec desugar_program = function
    | [] -> Unit
    | { is_rec; name; args; ty; value } :: rest ->
        Let {
          is_rec;
          name;
          ty = transform_fun_ty args ty;
          value = create_nested_funs args (desugar_expr value);
          body = desugar_program rest;
        }
  in
  desugar_program prog

(* Type-checking function *)
let type_of (expr : expr) : (ty, error) result =
  let rec typecheck env expr =
    match expr with
    | Unit -> Ok UnitTy
    | Num _ -> Ok IntTy
    | True | False -> Ok BoolTy
    | Var x -> (
        match Env.find_opt x env with
        | Some ty -> Ok ty
        | None -> Error (UnknownVar x))
    | Let { is_rec; name; ty = expected_ty; value; body } ->
        let extended_env =
          if is_rec then Env.add name expected_ty env else env
        in
        (match typecheck extended_env value with
        | Ok actual_ty when actual_ty = expected_ty ->
            typecheck (Env.add name expected_ty extended_env) body
        | Ok actual_ty -> Error (LetTyErr (expected_ty, actual_ty))
        | Error e -> Error e)
    | Fun (arg, arg_ty, body) ->
        let extended_env = Env.add arg arg_ty env in
        (match typecheck extended_env body with
        | Ok body_ty -> Ok (FunTy (arg_ty, body_ty))
        | Error e -> Error e)
    | App (e1, e2) -> (
        match typecheck env e1 with
        | Ok (FunTy (arg_ty, ret_ty)) -> (
            match typecheck env e2 with
            | Ok actual_ty when actual_ty = arg_ty -> Ok ret_ty
            | Ok actual_ty -> Error (FunArgTyErr (arg_ty, actual_ty))
            | Error e -> Error e)
        | Ok ty -> Error (FunAppTyErr ty)
        | Error e -> Error e)
    | If (cond, then_, else_) -> (
        match typecheck env cond with
        | Ok BoolTy -> (
            match typecheck env then_ with
            | Ok then_ty -> (
                match typecheck env else_ with
                | Ok else_ty when then_ty = else_ty -> Ok then_ty
                | Ok else_ty -> Error (IfTyErr (then_ty, else_ty))
                | Error e -> Error e)
            | Error e -> Error e)
        | Ok ty -> Error (IfCondTyErr ty)
        | Error e -> Error e)
    | Bop (op, e1, e2) -> (
        match typecheck env e1 with
        | Error e -> Error e
        | Ok l_ty -> (
            match typecheck env e2 with
            | Error e -> Error e
            | Ok r_ty -> (
                match (op, l_ty, r_ty) with
                | (Add | Sub | Mul | Div | Mod), IntTy, IntTy -> Ok IntTy
                | (And | Or), BoolTy, BoolTy -> Ok BoolTy
                | (Lt | Lte | Gt | Gte | Eq | Neq), IntTy, IntTy -> Ok BoolTy
                | (Lt | Lte | Gt | Gte | Eq | Neq), BoolTy, BoolTy -> Ok BoolTy
                | (_, IntTy, _) -> Error (OpTyErrR (op, IntTy, r_ty))
                | (_, _, IntTy) -> Error (OpTyErrL (op, IntTy, l_ty))
                | (_, BoolTy, _) -> Error (OpTyErrR (op, BoolTy, r_ty))
                | (_, _, BoolTy) -> Error (OpTyErrL (op, BoolTy, l_ty))
                | _ -> Error (OpTyErrL (op, l_ty, r_ty)))))
    | Assert e -> (
        match typecheck env e with
        | Ok BoolTy -> Ok UnitTy
        | Ok ty -> Error (AssertTyErr ty)
        | Error e -> Error e)
  in
  typecheck Env.empty expr

(* Evaluation function *)
exception DivByZero
exception AssertFail

let eval (expr : expr) : value =
  let rec eval_expr env expr =
    match expr with
    | Unit -> VUnit
    | Num n -> VNum n
    | True -> VBool true
    | False -> VBool false
    | Var x -> Env.find x env
    | Let { is_rec; name; ty = _; value; body } ->
        let env' =
          if is_rec then
            let rec_vclos = VClos { name = Some name; arg = ""; body = value; env } in
            Env.add name rec_vclos env
          else env
        in
        let v = eval_expr env' value in
        let env'' = Env.add name v env' in
        eval_expr env'' body
    | Fun (arg, _, body) -> VClos { name = None; arg; body; env }
    | App (e1, e2) -> (
        match eval_expr env e1 with
        | VClos { name = _; arg; body; env = closure_env } ->
            let v2 = eval_expr env e2 in
            let env_with_arg = Env.add arg v2 closure_env in
            eval_expr env_with_arg body
        | _ -> raise (Invalid_argument "Expected function"))
    | If (cond, then_, else_) -> (
        match eval_expr env cond with
        | VBool true -> eval_expr env then_
        | VBool false -> eval_expr env else_
        | _ -> raise (Invalid_argument "Expected boolean"))
    | Bop (op, e1, e2) ->
        let v1 = eval_expr env e1 in
        let v2 = eval_expr env e2 in
        (match (v1, v2, op) with
        | VNum n1, VNum n2, Add -> VNum (n1 + n2)
        | VNum n1, VNum n2, Sub -> VNum (n1 - n2)
        | VNum n1, VNum n2, Mul -> VNum (n1 * n2)
        | VNum n1, VNum n2, Div ->
            if n2 = 0 then raise DivByZero else VNum (n1 / n2)
        | VNum n1, VNum n2, Mod ->
            if n2 = 0 then raise DivByZero else VNum (n1 mod n2)
        | VNum n1, VNum n2, Lt -> VBool (n1 < n2)
        | VNum n1, VNum n2, Lte -> VBool (n1 <= n2)
        | VNum n1, VNum n2, Gt -> VBool (n1 > n2)
        | VNum n1, VNum n2, Gte -> VBool (n1 >= n2)
        | VNum n1, VNum n2, Eq -> VBool (n1 = n2)
        | VNum n1, VNum n2, Neq -> VBool (n1 <> n2)
        | VBool b1, VBool b2, And -> VBool (b1 && b2)
        | VBool b1, VBool b2, Or -> VBool (b1 || b2)
        | _ -> raise (Invalid_argument "Operator type mismatch"))
    | Assert e -> (
        match eval_expr env e with
        | VBool true -> VUnit
        | _ -> raise AssertFail)
  in
  eval_expr Env.empty expr

(* Interpreter function *)
let interp (input : string) : (value, error) result =
  match parse input with
  | Some prog -> (
      let expr = desugar prog in
      match type_of expr with
      | Ok _ -> Ok (eval expr)
      | Error e -> Error e)
  | None -> Error ParseErr
