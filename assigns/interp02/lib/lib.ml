open Utils

(* Parse function *)
let parse = My_parser.parse

(* Desugar function *)
let rec desugar prog =
  let rec build_fun_ty args ty =
    match args with
    | [] -> ty
    | (_, arg_ty) :: xs -> FunTy (arg_ty, build_fun_ty xs ty)
  in
  let rec desugar_args args body =
    match args with
    | [] -> body
    | (x, ty) :: xs -> Fun (x, ty, desugar_args xs body)
  in
  let rec desugar_expr = function
    | SUnit -> Unit
    | STrue -> True
    | SFalse -> False
    | SNum n -> Num n
    | SVar x -> Var x
    | SFun { arg = (x, ty); args; body } ->
        Fun (x, ty, desugar_args args (desugar_expr body))
    | SApp (e1, e2) -> App (desugar_expr e1, desugar_expr e2)
    | SLet { is_rec; name; args; ty; value; body } ->
        Let {
          is_rec;
          name;
          ty = build_fun_ty args ty;
          value = desugar_args args (desugar_expr value);
          body = desugar_expr body;
        }
    | SIf (e1, e2, e3) -> If (desugar_expr e1, desugar_expr e2, desugar_expr e3)
    | SBop (op, e1, e2) -> Bop (op, desugar_expr e1, desugar_expr e2)
    | SAssert e -> Assert (desugar_expr e)
  in
  match prog with
  | [] -> Unit
  | toplet :: rest ->
      Let {
        is_rec = toplet.is_rec;
        name = toplet.name;
        ty = build_fun_ty toplet.args toplet.ty;
        value = desugar_args toplet.args (desugar_expr toplet.value);
        body = desugar rest;
      }


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

let rec eval env expr =
  let eval_binary_op op v1 v2 =
    match op, v1, v2 with
    | Add, VNum x, VNum y -> VNum (x + y)
    | Sub, VNum x, VNum y -> VNum (x - y)
    | Mul, VNum x, VNum y -> VNum (x * y)
    | Div, VNum x, VNum y -> if y = 0 then raise DivByZero else VNum (x / y)
    | Mod, VNum x, VNum y -> if y = 0 then raise DivByZero else VNum (x mod y)
    | Lt, VNum x, VNum y -> VBool (x < y)
    | Lte, VNum x, VNum y -> VBool (x <= y)
    | Gt, VNum x, VNum y -> VBool (x > y)
    | Gte, VNum x, VNum y -> VBool (x >= y)
    | Eq, VNum x, VNum y -> VBool (x = y)
    | Neq, VNum x, VNum y -> VBool (x <> y)
    | And, VBool x, VBool y -> VBool (x && y)
    | Or, VBool x, VBool y -> VBool (x || y)
    | _ -> failwith "Invalid"
  in
  match expr with
  | Unit -> VUnit
  | True -> VBool true
  | False -> VBool false
  | Num n -> VNum n
  | Var x ->
      if Env.mem x env then Env.find x env
      else failwith ("Variable " ^ x ^ " not found")
  | If (cond, then_, else_) ->
      (match eval env cond with
       | VBool true -> eval env then_
       | VBool false -> eval env else_
       | _ -> failwith "If condition must evaluate to a boolean")
  | Bop (op, left, right) ->
      let v1 = eval env left in
      let v2 = eval env right in
      eval_binary_op op v1 v2
  | Fun (arg, _, body) -> VClos { name = None; arg; body; env }
  | App (func, arg) ->
      (match eval env func with
       | VClos { name = _; arg = param; body; env = closure_env } ->
           let arg_value = eval env arg in
           eval (Env.add param arg_value closure_env) body
       | _ -> failwith "Expected a function application")
  | Let { is_rec; name; ty = _; value; body } ->
      let env' =
        if is_rec then
          match value with
          | Fun (arg, _, body) ->
              Env.add name (VClos { name = Some name; arg; body; env }) env
          | _ -> failwith "Recursive let requires a function"
        else env
      in
      let value_evaluated = eval env' value in
      eval (Env.add name value_evaluated env') body
  | Assert e ->
      (match eval env e with
       | VBool true -> VUnit
       | _ -> raise AssertFail)


let eval = eval Env.empty

(* Interpreter function *)
let interp (input : string) : (value, error) result =
  match parse input with
  | Some prog -> (
      let expr = desugar prog in
      match type_of expr with
      | Ok _ -> Ok (eval expr)
      | Error e -> Error e)
  | None -> Error ParseErr