open Utils
(* Parse a string into a program *)
let parse (s : string) : prog option =
 try My_parser.parse s
 with _ -> None


(* Desugar a program into an expression *)
let desugar (prog : prog) : expr =
  let rec desugar_toplet toplet body =
    match toplet with
    | { is_rec; name; args = []; ty; value } ->
        Let { is_rec; name; ty; value = desugar_expr value; body }
    | { is_rec; name; args; ty; value } ->
        let curried_fun =
          List.fold_right
            (fun (arg_name, arg_ty) acc ->
              Fun (arg_name, arg_ty, acc))
            args
            (desugar_expr value)
        in
        Let { is_rec; name; ty; value = curried_fun; body }
  and desugar_expr expr =
    match expr with
    | SUnit -> Unit
    | STrue -> True
    | SFalse -> False
    | SNum n -> Num n
    | SVar x -> Var x
    | SIf (cond, then_, else_) ->
        If (desugar_expr cond, desugar_expr then_, desugar_expr else_)
    | SBop (op, lhs, rhs) ->
        Bop (op, desugar_expr lhs, desugar_expr rhs)
    | SApp (f, arg) ->
        App (desugar_expr f, desugar_expr arg)
    | SLet { is_rec; name; args = []; ty; value; body } ->
        Let
          {
            is_rec;
            name;
            ty;
            value = desugar_expr value;
            body = desugar_expr body;
          }
    | SLet { is_rec; name; args; ty; value; body } ->
        let curried_fun =
          List.fold_right
            (fun (arg_name, arg_ty) acc ->
              Fun (arg_name, arg_ty, acc))
            args
            (desugar_expr value)
        in
        Let
          {
            is_rec;
            name;
            ty;
            value = curried_fun;
            body = desugar_expr body;
          }
    | SFun { arg; args; body } ->
        let curried_fun =
          List.fold_right
            (fun (arg_name, arg_ty) acc ->
              Fun (arg_name, arg_ty, acc))
            (arg :: args)
            (desugar_expr body)
        in
        curried_fun
    | SAssert e ->
        Assert (desugar_expr e)
  in
  List.fold_right desugar_toplet prog Unit



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
       | Ok IntTy, Ok IntTy when op = Add || op = Sub || op = Mul || op = Div || op = Mod ->
           Ok IntTy
       | Ok IntTy, Ok IntTy when op = Lt || op = Lte || op = Gt || op = Gte || op = Eq || op = Neq ->
           Ok BoolTy
       | Ok BoolTy, Ok BoolTy when op = And || op = Or -> Ok BoolTy
       | Ok l_ty, Ok r_ty ->
           if l_ty <> IntTy then Error (OpTyErrL (op, IntTy, l_ty))
           else Error (OpTyErrR (op, IntTy, r_ty))
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
       | _ -> raise AssertFail)
   | Bop (op, lhs, rhs) -> (
       match eval env lhs, eval env rhs with
       | VNum v1, VNum v2 -> (
           match op with
           | Add -> VNum (v1 + v2)
           | Sub -> VNum (v1 - v2)
           | Mul -> VNum (v1 * v2)
           | Div -> if v2 = 0 then raise DivByZero else VNum (v1 / v2)
           | Mod -> if v2 = 0 then raise DivByZero else VNum (v1 mod v2)
           | _ -> raise AssertFail)
       | _ -> raise AssertFail)
   | Fun (arg, _, body) -> VClos { name = None; arg; body; env }
   | App (f, x) -> (
       match eval env f with
       | VClos { name = _; arg; body; env = closure_env } ->
           let arg_val = eval env x in
           eval (Env.add arg arg_val closure_env) body
       | _ -> raise AssertFail)
   | Let { is_rec; name; value; body; _ } ->
       let value_v =
         if is_rec then VClos { name = Some name; arg = ""; body = value; env }
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
 | Some prog -> (
     let desugared = desugar prog in
     match type_of desugared with
     | Error e -> Error e
     | Ok _ -> Ok (eval desugared))



