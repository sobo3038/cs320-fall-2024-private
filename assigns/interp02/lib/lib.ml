open Utils

(* Parse function *)
let parse = My_parser.parse

(* Desugar function *)
let desugar (prog : prog) : expr =
  let rec desugar_toplets (toplets : toplet list) : expr =
    match toplets with
    | [] -> Unit
    | { is_rec; name; args; ty; value } :: rest ->
        let function_type =
          List.fold_right (fun (_, arg_ty) acc -> FunTy (arg_ty, acc)) args ty
        in
        let desugared_value =
          List.fold_right
            (fun (arg_name, arg_ty) acc -> Fun (arg_name, arg_ty, acc))
            args
            (desugar_expr value)
        in
        Let
          {
            is_rec;
            name;
            ty = function_type;
            value = desugared_value;
            body = desugar_toplets rest;
          }
  and desugar_expr = function
    | SLet { is_rec; name; args; ty; value; body } ->
        let function_type =
          List.fold_right (fun (_, arg_ty) acc -> FunTy (arg_ty, acc)) args ty
        in
        let desugared_value =
          List.fold_right
            (fun (arg_name, arg_ty) acc -> Fun (arg_name, arg_ty, acc))
            args
            (desugar_expr value)
        in
        Let
          {
            is_rec;
            name;
            ty = function_type;
            value = desugared_value;
            body = desugar_expr body;
          }
    | SFun { arg; args; body } ->
        List.fold_right
          (fun (arg_name, arg_ty) acc -> Fun (arg_name, arg_ty, acc))
          (arg :: args)
          (desugar_expr body)
    | SIf (cond, then_, else_) ->
        If (desugar_expr cond, desugar_expr then_, desugar_expr else_)
    | SApp (e1, e2) -> App (desugar_expr e1, desugar_expr e2)
    | SBop (op, e1, e2) -> Bop (op, desugar_expr e1, desugar_expr e2)
    | SAssert e -> Assert (desugar_expr e)
    | SUnit -> Unit
    | STrue -> True
    | SFalse -> False
    | SNum n -> Num n
    | SVar x -> Var x
  in
  desugar_toplets prog

(* Type-checking function *)
let rec type_of env = function
  | Unit -> Ok UnitTy
  | True | False -> Ok BoolTy
  | Num _ -> Ok IntTy
  | Var x -> (
    if (Env.mem x env) then Ok (Env.find x env)
    else Error (UnknownVar x)
  )
  | If (e1, e2, e3) -> (
    match (type_of env e1, type_of env e2, type_of env e3) with
    | Ok BoolTy, Ok t2, Ok t3 when t2 = t3 -> Ok t2
    | Ok BoolTy, Ok t2, Ok t3 -> Error (IfTyErr (t2, t3))
    | Ok t1, Ok _, Ok _ -> Error (IfCondTyErr t1)
    | Ok _, Error e, _ -> Error e
    | Ok _, _, Error e -> Error e
    | Error e, _, _ -> Error e
  )
  | Bop (op, e1, e2) -> (
      match (type_of env e1, type_of env e2) with
      | Ok t1, Ok t2 -> (
        match op with
        | Add | Sub | Mul | Div | Mod ->
          (match (t1, t2) with
            | IntTy, IntTy -> Ok IntTy
            | _, IntTy -> Error (OpTyErrL (op, t2, t1))
            | IntTy, _ -> Error (OpTyErrR (op, t1, t2))
            | _ -> failwith (string_of_ty t1 ^ " " ^ string_of_ty t2))
        | Lt | Lte | Gt | Gte ->
          (match (t1, t2) with
            | IntTy, IntTy -> Ok BoolTy
            | _, IntTy -> Error (OpTyErrL (op, t2, t1))
            | IntTy, _ -> Error (OpTyErrR (op, t1, t2))
            | _ -> failwith (string_of_ty t1 ^ " " ^ string_of_ty t2))
        | Eq | Neq ->
          if t1 <> t2 then Error (OpTyErrL (op, t1, t2))
          else Ok BoolTy
        | And | Or ->
          (match (t1, t2) with
            | BoolTy, BoolTy -> Ok BoolTy
            | _, BoolTy -> Error (OpTyErrL (op, t2, t1))
            | BoolTy, _ -> Error (OpTyErrR (op, t1, t2))
            | _ -> failwith (string_of_ty t1 ^ " " ^ string_of_ty t2))
      )
      | Ok _, Error e -> Error e
      | Error e, _ -> Error e
    )
  | Fun (x, ty, e) -> (
    let env' = Env.add x ty env in
    (match type_of env' e with
      | Ok ty_out -> Ok (FunTy (ty, ty_out))
      | e -> e)
  )
  | App (e1, e2) -> (
      match (type_of env e1, type_of env e2) with
      | Ok (FunTy (ty_arg, ty_out)), Ok t2 when ty_arg = t2 -> Ok ty_out
      | Ok (FunTy (ty_arg, _)), Ok t2 -> Error (FunArgTyErr (ty_arg, t2))
      | Ok t1, Ok _ -> Error (FunAppTyErr t1)
      | Ok _, Error e -> Error e
      | Error e, _ -> Error e
    )
  | Let { is_rec; name; ty; value; body } -> (
    let env' = if is_rec then Env.add name ty env else env in
    match type_of env' value with
    | Ok ty_value when ty = ty_value -> 
      let env'' = Env.add name ty env' in
      type_of env'' body
    | Ok ty_value -> Error (LetTyErr (ty, ty_value))
    | e -> e
  )
  | Assert e -> (
    match type_of env e with
    | Ok BoolTy -> Ok UnitTy
    | Ok t -> Error (AssertTyErr t)
    | e -> e
  )
let type_of = type_of Env.empty




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
        let rec_env =
          if is_rec then
            Env.add name (VClos { name = Some name; arg = ""; body = value; env }) env
          else env
        in
        let v = eval_expr rec_env value in
        eval_expr (Env.add name v rec_env) body
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
