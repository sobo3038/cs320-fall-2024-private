open Utils

(* Parse function *)
let parse = My_parser.parse

(* Desugar function *)
let desugar (prog : prog) : expr =
  let rec desugar_expr (e : sfexpr) : expr =
    match e with
    | SUnit -> Unit
    | STrue -> True
    | SFalse -> False
    | SNum n -> Num n
    | SVar x -> Var x
    | SFun { arg = (x, ty); args; body } ->
        let rec build_fun args body =
          match args with
          | [] -> desugar_expr body
          | (arg_name, arg_ty) :: rest -> Fun (arg_name, arg_ty, build_fun rest body)
        in
        Fun (x, ty, build_fun args body)
    | SApp (e1, e2) -> App (desugar_expr e1, desugar_expr e2)
    | SLet { is_rec; name; args; ty; value; body } ->
        let rec build_fun_ty args ret_ty =
          match args with
          | [] -> ret_ty
          | (_, arg_ty) :: rest -> FunTy (arg_ty, build_fun_ty rest ret_ty)
        in
        let desugared_value = 
          match args with
          | [] -> desugar_expr value
          | _ -> 
              let rec build_fun args body =
                match args with
                | [] -> desugar_expr body
                | (arg_name, arg_ty) :: rest -> Fun (arg_name, arg_ty, build_fun rest body)
              in
              build_fun args value
        in
        Let { 
          is_rec; 
          name; 
          ty = build_fun_ty args ty; 
          value = desugared_value; 
          body = desugar_expr body 
        }
    | SIf (e1, e2, e3) -> If (desugar_expr e1, desugar_expr e2, desugar_expr e3)
    | SBop (op, e1, e2) -> Bop (op, desugar_expr e1, desugar_expr e2)
    | SAssert e -> Assert (desugar_expr e)
  in

  let rec desugar_toplets = function
    | [] -> Unit
    | toplet :: rest ->
        let desugared_value = 
          match toplet.args with
          | [] -> desugar_expr toplet.value
          | _ ->
              let rec build_fun args body =
                match args with
                | [] -> desugar_expr body
                | (arg_name, arg_ty) :: rest -> Fun (arg_name, arg_ty, build_fun rest body)
              in
              build_fun toplet.args toplet.value
        in

        let rec build_fun_ty args ret_ty =
          match args with
          | [] -> ret_ty
          | (_, arg_ty) :: rest -> FunTy (arg_ty, build_fun_ty rest ret_ty)
        in

        Let {
          is_rec = toplet.is_rec;
          name = toplet.name;
          ty = build_fun_ty toplet.args toplet.ty;
          value = desugared_value;
          body = desugar_toplets rest
        }
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

let rec eval env = function
  | Unit -> VUnit
  | True -> VBool true
  | False -> VBool false
  | Num n -> VNum n
  | Var x -> 
      (match Env.find_opt x env with
       | Some v -> v
       | None -> failwith ("Unbound variable: " ^ x))
  | If (cond, then_expr, else_expr) ->
      (match eval env cond with
       | VBool true -> eval env then_expr
       | VBool false -> eval env else_expr
       | _ -> failwith "Condition in if-expression must be a boolean")
  | Bop (op, e1, e2) ->
      let v1 = eval env e1 in
      let v2 = eval env e2 in
      (match (op, v1, v2) with
       | (Add, VNum n1, VNum n2) -> VNum (n1 + n2)
       | (Sub, VNum n1, VNum n2) -> VNum (n1 - n2)
       | (Mul, VNum n1, VNum n2) -> VNum (n1 * n2)
       | (Div, VNum n1, VNum n2) -> 
           if n2 = 0 then raise DivByZero else VNum (n1 / n2)
       | (Mod, VNum n1, VNum n2) -> 
           if n2 = 0 then raise DivByZero else VNum (n1 mod n2)
       | (Lt, VNum n1, VNum n2) -> VBool (n1 < n2)
       | (Lte, VNum n1, VNum n2) -> VBool (n1 <= n2)
       | (Gt, VNum n1, VNum n2) -> VBool (n1 > n2)
       | (Gte, VNum n1, VNum n2) -> VBool (n1 >= n2)
       | (Eq, VNum n1, VNum n2) -> VBool (n1 = n2)
       | (Eq, VBool b1, VBool b2) -> VBool (b1 = b2)
       | (Neq, VNum n1, VNum n2) -> VBool (n1 <> n2)
       | (Neq, VBool b1, VBool b2) -> VBool (b1 <> b2)
       | (And, VBool b1, VBool b2) -> VBool (b1 && b2)
       | (Or, VBool b1, VBool b2) -> VBool (b1 || b2)
       | _ -> failwith "Type mismatch in binary operation")
  | Fun (x, _, body) -> VClos { name = None; arg = x; body; env }
  | App (e1, e2) ->
      (match eval env e1 with
       | VClos { name; arg; body; env = clos_env } ->
           let arg_val = eval env e2 in
           let new_env = match name with
             | Some f -> Env.add f (VClos { name; arg; body; env = clos_env }) 
                         (Env.add arg arg_val clos_env)
             | None -> Env.add arg arg_val clos_env
           in
           eval new_env body
       | _ -> failwith "Application to non-function value")
  | Let { is_rec; name; ty = _; value; body } ->
      let rec_env = if is_rec then Env.add name (VClos { name = Some name; arg = ""; body = value; env }) env else env in
      let v = eval rec_env value in
      eval (Env.add name v env) body
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