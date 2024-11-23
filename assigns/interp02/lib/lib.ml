open Utils

(* Parse a string into a program *)
let parse (s : string) : prog option =
  try My_parser.parse s
  with _ -> None

  let desugar (p : prog) : expr =
    let rec desugar_toplets (toplets : toplet list) : expr =
      match toplets with
      | [] -> Unit
      | { is_rec; name; args; ty; value } :: rest ->
          let desugared_value =
            List.fold_right
              (fun (arg_name, arg_ty) acc -> Fun (arg_name, arg_ty, acc))
              args
              (desugar_sfexpr value)
          in
          Let { is_rec; name; ty; value = desugared_value; body = desugar_toplets rest }
    and desugar_sfexpr (e : sfexpr) : expr =
      match e with
      | SUnit -> Unit
      | STrue -> True
      | SFalse -> False
      | SNum n -> Num n
      | SVar x -> Var x
      | SFun { arg; args; body } ->
          List.fold_right
            (fun (arg_name, arg_ty) acc -> Fun (arg_name, arg_ty, acc))
            ((fst arg, snd arg) :: args)
            (desugar_sfexpr body)
      | SApp (f, x) -> App (desugar_sfexpr f, desugar_sfexpr x)
      | SLet { is_rec; name; args; ty; value; body } ->
          let desugared_value =
            List.fold_right
              (fun (arg_name, arg_ty) acc -> Fun (arg_name, arg_ty, acc))
              args
              (desugar_sfexpr value)
          in
          Let { is_rec; name; ty; value = desugared_value; body = desugar_sfexpr body }
      | SIf (cond, then_, else_) ->
          If (desugar_sfexpr cond, desugar_sfexpr then_, desugar_sfexpr else_)
      | SBop (op, lhs, rhs) -> Bop (op, desugar_sfexpr lhs, desugar_sfexpr rhs)
      | SAssert e -> Assert (desugar_sfexpr e)
    in
    desugar_toplets p
  

(* Type-check an expression *)
let type_of (e : expr) : (ty, error) result =
  let rec type_check (ctx : (string * ty) list) (e : expr) : (ty, error) result =
    match e with
    | Unit -> Ok UnitTy
    | True | False -> Ok BoolTy
    | Num _ -> Ok IntTy
    | Var x -> (
        match List.assoc_opt x ctx with
        | Some ty -> Ok ty
        | None -> Error (UnknownVar x))
    | If (cond, then_, else_) -> (
        match type_check ctx cond with
        | Ok BoolTy -> (
            match type_check ctx then_, type_check ctx else_ with
            | Ok t1, Ok t2 when t1 = t2 -> Ok t1
            | Ok t1, Ok t2 -> Error (IfTyErr (t1, t2))
            | _, Error e | Error e, _ -> Error e)
        | Ok ty -> Error (IfCondTyErr ty)
        | Error e -> Error e)
    | Bop (op, lhs, rhs) -> (
        match type_check ctx lhs, type_check ctx rhs with
        | Ok l_ty, Ok r_ty ->
            (match op, l_ty, r_ty with
             | (Add | Sub | Mul | Div | Mod), IntTy, IntTy -> Ok IntTy
             | (Lt | Lte | Gt | Gte | Eq | Neq), IntTy, IntTy -> Ok BoolTy
             | (And | Or), BoolTy, BoolTy -> Ok BoolTy
             | (Add | Sub | Mul | Div | Mod | Lt | Lte | Gt | Gte | Eq | Neq), IntTy, _ -> Error (OpTyErrR (op, IntTy, r_ty))
             | (Add | Sub | Mul | Div | Mod | Lt | Lte | Gt | Gte | Eq | Neq), _, IntTy -> Error (OpTyErrL (op, IntTy, l_ty))
             | (And | Or), BoolTy, _ -> Error (OpTyErrR (op, BoolTy, r_ty))
             | (And | Or), _, BoolTy -> Error (OpTyErrL (op, BoolTy, l_ty))
             | _ -> Error (OpTyErrL (op, IntTy, l_ty)))
        | Error e, _ | _, Error e -> Error e)
    | Fun (arg, arg_ty, body) -> (
        match type_check ((arg, arg_ty) :: ctx) body with
        | Ok body_ty -> Ok (FunTy (arg_ty, body_ty))
        | Error e -> Error e)
    | App (f, x) -> (
        match type_check ctx f with
        | Ok (FunTy (arg_ty, ret_ty)) -> (
            match type_check ctx x with
            | Ok ty when ty = arg_ty -> Ok ret_ty
            | Ok ty -> Error (FunArgTyErr (arg_ty, ty))
            | Error e -> Error e)
        | Ok ty -> Error (FunAppTyErr ty)
        | Error e -> Error e)
    | Let { is_rec; name; ty; value; body } ->
        let ctx' = if is_rec then (name, ty) :: ctx else ctx in
        (match type_check ctx' value with
        | Ok value_ty when value_ty = ty -> type_check ((name, ty) :: ctx) body
        | Ok value_ty -> Error (LetTyErr (ty, value_ty))
        | Error e -> Error e)
    | Assert e -> (
        match type_check ctx e with
        | Ok BoolTy -> Ok UnitTy
        | Ok ty -> Error (AssertTyErr ty)
        | Error e -> Error e)
  in
  type_check [] e

(* Evaluate an expression *)
exception AssertFail
exception DivByZero

let eval (e : expr) : value =
  let rec eval (env : value env) (e : expr) : value =
    match e with
    | Unit -> VUnit
    | True -> VBool true
    | False -> VBool false
    | Num n -> VNum n
    | Var x -> Env.find x env
    | If (cond, then_, else_) -> (
        match eval env cond with
        | VBool true -> eval env then_
        | VBool false -> eval env else_
        | _ -> raise (Failure "Type error in if condition"))
    | Bop (op, lhs, rhs) ->
        let v1 = eval env lhs in
        let v2 = eval env rhs in
        (match op, v1, v2 with
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
         | Neq, VNum n1, VNum n2 -> VBool (n1 <> n2)
         | And, VBool b1, VBool b2 -> VBool (b1 && b2)
         | Or, VBool b1, VBool b2 -> VBool (b1 || b2)
         | _ -> raise (Failure "Type error in binary operation"))
    | Fun (arg, _, body) -> VClos { name = None; arg; body; env }
    | App (f, x) -> (
        match eval env f with
        | VClos { name; arg; body; env = closure_env } ->
            let arg_val = eval env x in
            let env' = Env.add arg arg_val closure_env in
            let env'' = match name with
              | Some n -> Env.add n (VClos { name; arg; body; env = closure_env }) env'
              | None -> env'
            in
            eval env'' body
        | _ -> raise (Failure "Type error in function application"))
    | Let { is_rec; name; value; body; _ } ->
        let value_v =
          if is_rec then
            VClos { name = Some name; arg = ""; body = value; env }
          else eval env value
        in
        eval (Env.add name value_v env) body
    | Assert e -> (
        match eval env e with
        | VBool true -> VUnit
        | _ -> raise AssertFail)
  in
  eval Env.empty e

(* Interpreter function *)
let interp (s : string) : (value, error) result =
  match parse s with
  | None -> Error ParseErr
  | Some prog ->
      try
        let desugared = desugar prog in
        match type_of desugared with
        | Error e -> Error e
        | Ok _ ->
            try Ok (eval desugared)
            with
            | DivByZero -> Error (OpTyErrL (Div, IntTy, IntTy))  (* or another appropriate error *)
            | AssertFail -> Error (AssertTyErr BoolTy)
            | Failure msg -> Error (UnknownVar msg)  (* or another appropriate error *)
      with
      | Failure msg -> Error (UnknownVar msg)  (* or another appropriate error *)