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


 let type_of (expr : expr) : (ty, error) result =
  let rec typecheck env expr =
    match expr with
    | Unit -> Ok UnitTy
    | Num _ -> Ok IntTy
    | True | False -> Ok BoolTy
    | Var x ->
        (match Env.find_opt x env with
         | Some ty -> Ok ty
         | None -> Error (UnknownVar x))
    | Let { is_rec; name; ty = expected_ty; value; body } ->
        let extended_env = if is_rec then Env.add name expected_ty env else env in
        (match typecheck extended_env value with
         | Ok actual_ty ->
             if actual_ty = expected_ty then
               typecheck (Env.add name expected_ty extended_env) body
             else
               Error (LetTyErr (expected_ty, actual_ty))
         | Error e -> Error e)
    | Fun (arg, arg_ty, body) ->
        let extended_env = Env.add arg arg_ty env in
        (match typecheck extended_env body with
         | Ok body_ty -> Ok (FunTy (arg_ty, body_ty))
         | Error e -> Error e)
    | App (e1, e2) ->
        (match typecheck env e1 with
         | Ok (FunTy (arg_ty, ret_ty)) ->
             (match typecheck env e2 with
              | Ok actual_ty ->
                  if actual_ty = arg_ty then Ok ret_ty
                  else Error (FunArgTyErr (arg_ty, actual_ty))
              | Error e -> Error e)
         | Ok ty -> Error (FunAppTyErr ty)
         | Error e -> Error e)
    | If (cond, then_, else_) ->
        (match typecheck env cond with
         | Ok BoolTy ->
             (match typecheck env then_ with
              | Ok then_ty ->
                  (match typecheck env else_ with
                   | Ok else_ty ->
                       if then_ty = else_ty then Ok then_ty
                       else Error (IfTyErr (then_ty, else_ty))
                   | Error e -> Error e)
              | Error e -> Error e)
         | Ok ty -> Error (IfCondTyErr ty)
         | Error e -> Error e)
    | Bop (op, e1, e2) ->
        (match typecheck env e1 with
         | Error e -> Error e
         | Ok l_ty ->
             (match typecheck env e2 with
              | Error e -> Error e
              | Ok r_ty ->
                  (match (op, l_ty, r_ty) with
                   | (Add | Sub | Mul | Div | Mod), IntTy, IntTy -> Ok IntTy
                   | (And | Or), BoolTy, BoolTy -> Ok BoolTy
                   | (Lt | Lte | Gt | Gte | Eq | Neq), IntTy, IntTy -> Ok BoolTy
                   | (Lt | Lte | Gt | Gte | Eq | Neq), BoolTy, BoolTy -> Ok BoolTy
                   | (_, IntTy, _) -> Error (OpTyErrR (op, IntTy, r_ty))
                   | (_, _, IntTy) -> Error (OpTyErrL (op, IntTy, l_ty))
                   | (_, BoolTy, _) -> Error (OpTyErrR (op, BoolTy, r_ty))
                   | (_, _, BoolTy) -> Error (OpTyErrL (op, BoolTy, l_ty))
                   | _ -> Error (OpTyErrL (op, l_ty, r_ty)))))
    | Assert e ->
        (match typecheck env e with
         | Ok BoolTy -> Ok UnitTy
         | Ok ty -> Error (AssertTyErr ty)
         | Error e -> Error e)
  in
  typecheck Env.empty expr

 


   let eval (expr : expr) : value =
    let rec eval_expr env expr =
        match expr with
        | Unit -> VUnit
        | Num n -> VNum n
        | True -> VBool true
        | False -> VBool false
        | Var x -> Env.find x env
        | Let { is_rec; name; ty = _; value; body } ->
            let extended_env =
                if is_rec then
                    let closure =
                        match value with
                        | Fun (arg, _, body) -> VClos { name = Some name; arg; body; env }
                        | _ ->
                            let gensym_arg = gensym () in
                            let wrapped_body = Fun (gensym_arg, UnitTy, value) in
                            VClos { name = Some name; arg = gensym_arg; body = wrapped_body; env }
                    in
                    Env.add name closure env
                else
                    let v = eval_expr env value in
                    Env.add name v env
            in
            eval_expr extended_env body
        | Fun (arg, _, body) -> VClos { name = None; arg; body; env }
        | App (e1, e2) -> (
            match eval_expr env e1 with
            | VClos { name = Some fname; arg; body; env = closure_env } ->
                let v2 = eval_expr env e2 in
                let extended_env =
                    Env.add fname (VClos { name = Some fname; arg; body; env = closure_env })
                        (Env.add arg v2 closure_env)
                in
                eval_expr extended_env body
            | VClos { name = None; arg; body; env = closure_env } ->
                let v2 = eval_expr env e2 in
                let extended_env = Env.add arg v2 closure_env in
                eval_expr extended_env body
            | _ -> assert false
        )
        | If (cond, then_, else_) -> (
            match eval_expr env cond with
            | VBool true -> eval_expr env then_
            | VBool false -> eval_expr env else_
            | _ -> assert false 
        )
        | Bop (op, e1, e2) -> (
            match op with
            | And -> (
                match eval_expr env e1 with
                | VBool false -> VBool false 
                | VBool true -> eval_expr env e2 
                | _ -> assert false 
            )
            | Or -> (
                match eval_expr env e1 with
                | VBool true -> VBool true 
                | VBool false -> eval_expr env e2 
                | _ -> assert false 
            )
            | _ -> (
                let v1 = eval_expr env e1 in
                let v2 = eval_expr env e2 in
                match (v1, v2, op) with
                | (VNum n1, VNum n2, Add) -> VNum (n1 + n2)
                | (VNum n1, VNum n2, Sub) -> VNum (n1 - n2)
                | (VNum n1, VNum n2, Mul) -> VNum (n1 * n2)
                | (VNum n1, VNum n2, Div) -> if n2 = 0 then raise DivByZero else VNum (n1 / n2)
                | (VNum n1, VNum n2, Mod) -> if n2 = 0 then raise DivByZero else VNum (n1 mod n2)
                | (VNum n1, VNum n2, Lt) -> VBool (n1 < n2)
                | (VNum n1, VNum n2, Lte) -> VBool (n1 <= n2)
                | (VNum n1, VNum n2, Gt) -> VBool (n1 > n2)
                | (VNum n1, VNum n2, Gte) -> VBool (n1 >= n2)
                | (VNum n1, VNum n2, Eq) -> VBool (n1 = n2)
                | (VNum n1, VNum n2, Neq) -> VBool (n1 <> n2)
                | _ -> assert false 
            )
        )
        | Assert e -> (
            match eval_expr env e with
            | VBool true -> VUnit
            | VBool false -> raise AssertFail
            | _ -> assert false 
        )
    in
    eval_expr Env.empty expr


let interp str =
 match parse str with
 | Some prog -> (
     let desugared = desugar prog in
     match type_of desugared with
     | Ok _ -> Ok (eval desugared)
     | Error e -> Error e)
 | None -> Error ParseErr



