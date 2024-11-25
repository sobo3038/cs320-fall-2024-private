open Utils

let parse = My_parser.parse;;

let rec build_fun_ty args ty =
  match args with
  | [] -> ty
  | (_, arg_ty) :: xs -> FunTy (arg_ty, build_fun_ty xs ty)

let rec desugar_args args body =
  match args with
  | [] -> body
  | (x, ty) :: xs -> Fun (x, ty, desugar_args xs body)

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
    let desugared_value = desugar_args args (desugar_expr value) in
    Let { is_rec; name; ty = build_fun_ty args ty; value = desugared_value; body = desugar_expr body }
  | SIf (e1, e2, e3) -> If (desugar_expr e1, desugar_expr e2, desugar_expr e3)
  | SBop (op, e1, e2) -> Bop (op, desugar_expr e1, desugar_expr e2)
  | SAssert e -> Assert (desugar_expr e)

let rec desugar prog =
  match prog with
  | [] -> Unit
  | toplet :: rest -> (
    let desugared_value = desugar_args toplet.args (desugar_expr toplet.value) in
    Let {
      is_rec = toplet.is_rec;
      name = toplet.name;
      ty = build_fun_ty toplet.args toplet.ty;
      value = desugared_value;
      body = desugar rest
    }
  )

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

exception AssertFail
exception DivByZero

let rec eval env = function
  | Unit -> VUnit
  | True -> VBool true
  | False -> VBool false
  | Num n -> VNum n
  | Var x -> (
    if (Env.mem x env) then Env.find x env
    else failwith ("undefined variable " ^ x)
  )
  | If (e1, e2, e3) ->
    (match eval env e1 with
     | VBool true -> eval env e2
     | VBool false -> eval env e3
     | _ -> failwith "If condition must be a boolean")
  | Bop (op, e1, e2) ->
    let v1 = eval env e1 in
    let v2 = eval env e2 in
    eval_bop op v1 v2
  | Fun (x, _, e) -> VClos { name = None; arg = x; body = e; env }
  | App (e1, e2) ->
    (* print_endline ("expression: " ^ string_of_expr e1 ^ " " ^ string_of_expr e2);
    print_endline ("env: " ^ string_of_env (Env.to_list env)); *)
    let v1 = eval env e1 in
    let v2 = eval env e2 in
    (match v1 with
    | VClos { name = None; arg; body; env } ->
      let env' = Env.add arg v2 env in
      (* print_endline ("body: " ^ string_of_expr body);
      print_newline (); *)
      eval env' body
     | VClos { name = Some name; arg; body; env } ->
       let env' = Env.add name (VClos { name = Some name; arg; body; env }) (Env.add arg v2 env) in
       (* print_endline ("body: " ^ string_of_expr body);
       print_newline (); *)
       eval env' body
     | _ -> failwith "Application must be to a function")
  | Let { is_rec; name; ty = _; value; body } ->(
      match is_rec, value with  
      | true, Fun (arg, _, e) ->
        let env' = Env.add name (VClos { name = Some name; arg = arg; body = e; env }) env in
        let v = eval env' value in
        let env'' = Env.add name v env in
        eval env'' body
      | false, _ ->
        let v = eval env value in
        let env' = Env.add name v env in
        eval env' body
      | _ -> failwith "Invalid let binding"
    )
  | Assert e ->
    (match eval env e with
     | VBool true -> VUnit
     | _ -> raise AssertFail
     )

and eval_bop op v1 v2 =
  match (op, v1, v2) with
  | (Add, VNum n1, VNum n2) -> VNum (n1 + n2)
  | (Sub, VNum n1, VNum n2) -> VNum (n1 - n2)
  | (Mul, VNum n1, VNum n2) -> VNum (n1 * n2)
  | (Div, VNum n1, VNum n2) -> if n2 = 0 then raise DivByZero else VNum (n1 / n2)
  | (Mod, VNum n1, VNum n2) -> if n2 = 0 then raise DivByZero else VNum (n1 mod n2)
  | (Lt, VNum n1, VNum n2) -> VBool (n1 < n2)
  | (Lte, VNum n1, VNum n2) -> VBool (n1 <= n2)
  | (Gt, VNum n1, VNum n2) -> VBool (n1 > n2)
  | (Gte, VNum n1, VNum n2) -> VBool (n1 >= n2)
  | (Eq, VNum n1, VNum n2) -> VBool (n1 = n2)
  | (Eq, VBool n1, VBool n2) -> VBool (n1 = n2)
  | (Neq, VNum n1, VNum n2) -> VBool (n1 <> n2)
  | (Neq, VBool n1, VBool n2) -> VBool (n1 <> n2)
  | (And, VBool b1, VBool b2) -> VBool (b1 && b2)
  | (Or, VBool b1, VBool b2) -> VBool (b1 || b2)
  | _ -> failwith "Invalid binary operation " 

let eval = eval Env.empty

let interp str =
  match parse str with
  | Some prog -> (
    let expr = desugar prog in
    match type_of expr with
    | Ok _ -> Ok (eval expr)
    | Error e -> Error e
  )
  | _ -> Error ParseErr