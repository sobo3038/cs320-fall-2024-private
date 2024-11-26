open Utils


let parse = My_parser.parse;;

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
        let add_and_check env' =
          match typecheck env' value with
          | Ok actual_ty when actual_ty = expected_ty ->
              typecheck (Env.add name actual_ty env') body
          | Ok actual_ty -> Error (LetTyErr (expected_ty, actual_ty))
          | Error e -> Error e
        in
        if is_rec then
          let extended_env = Env.add name expected_ty env in
          add_and_check extended_env
        else add_and_check env

    | Fun (arg, arg_ty, body) ->
        let extended_env = Env.add arg arg_ty env in
        (match typecheck extended_env body with
        | Ok body_ty -> Ok (FunTy (arg_ty, body_ty))
        | Error e -> Error e)

    | App (e1, e2) ->
        let check_application fn_ty =
          match fn_ty with
          | FunTy (arg_ty, ret_ty) ->
              (match typecheck env e2 with
              | Ok actual_ty when actual_ty = arg_ty -> Ok ret_ty
              | Ok actual_ty -> Error (FunArgTyErr (arg_ty, actual_ty))
              | Error e -> Error e)
          | ty -> Error (FunAppTyErr ty)
        in
        (match typecheck env e1 with
        | Ok fn_ty -> check_application fn_ty
        | Error e -> Error e)

    | If (cond, then_, else_) ->
        let handle_then cond_ty =
          match cond_ty with
          | BoolTy ->
              (match typecheck env then_ with
              | Ok then_ty ->
                  (match typecheck env else_ with
                  | Ok else_ty when then_ty = else_ty -> Ok then_ty
                  | Ok else_ty -> Error (IfTyErr (then_ty, else_ty))
                  | Error e -> Error e)
              | Error e -> Error e)
          | ty -> Error (IfCondTyErr ty)
        in
        (match typecheck env cond with
        | Ok cond_ty -> handle_then cond_ty
        | Error e -> Error e)

    | Bop (op, e1, e2) ->
        let expected_types =
          match op with
          | Add | Sub | Mul | Div | Mod -> (IntTy, IntTy, IntTy)
          | Lt | Lte | Gt | Gte | Eq | Neq -> (IntTy, IntTy, BoolTy)
          | And | Or -> (BoolTy, BoolTy, BoolTy)
        in
        let (expected_ty1, expected_ty2, result_ty) = expected_types in
        let validate_right_operand () =
          match typecheck env e2 with
          | Ok ty2 when ty2 = expected_ty2 -> Ok result_ty
          | Ok ty2 -> Error (OpTyErrR (op, expected_ty2, ty2))
          | Error e -> Error e
        in
        (match typecheck env e1 with
        | Ok ty1 when ty1 = expected_ty1 -> validate_right_operand ()
        | Ok ty1 -> Error (OpTyErrL (op, expected_ty1, ty1))
        | Error e -> Error e)
        

    | Assert e ->
        (match typecheck env e with
        | Ok BoolTy -> Ok UnitTy
        | Ok ty -> Error (AssertTyErr ty)
        | Error e -> Error e)
  in
  typecheck Env.empty expr


  exception AssertFail
  exception DivByZero


  let eval (expr : expr) : value =
    let rec evaluate env curr =
      let add_to_env name value env = 
        Env.add name value env
      in
      match curr with
      | Unit -> VUnit
      | Num n -> VNum n
      | True -> VBool true
      | False -> VBool false
      | Var variable -> Env.find variable env
      | Let { is_rec; name; ty = _; value; body } ->
          let update_environment rec_flag =
            match rec_flag with
            | true ->
                let closure =
                  (match value with
                  | Fun (arg, _, body_fn) ->
                      VClos { name = Some name; arg = arg; body = body_fn; env = env }
                  | _ ->
                      let placeholder = gensym () in
                      let wrapped_fn = Fun (placeholder, UnitTy, value) in
                      VClos { name = Some name; arg = placeholder; body = wrapped_fn; env = env })
                in
                add_to_env name closure env
            | false ->
                let value_eval = evaluate env value in
                add_to_env name value_eval env
          in
          let updated_env = update_environment is_rec in
          evaluate updated_env body
      | Fun (arg, _, body_fn) ->
          VClos { name = None; arg = arg; body = body_fn; env = env }



          
      | App (function_expr, argument_expr) ->
          let func_value = evaluate env function_expr in
          let arg_value = evaluate env argument_expr in
          let handle_closure closure =
            match closure with
            | VClos { name = Some func_name; arg = func_arg; body; env = closure_env } ->
              let extended_env =
                Env.add func_name func_value (Env.add func_arg arg_value closure_env)
              in
              evaluate extended_env body
            | VClos { name = None; arg = func_arg; body; env = closure_env } ->
              let extended_env = Env.add func_arg arg_value closure_env in
              evaluate extended_env body
            | _ -> assert false
          in
          handle_closure func_value
        


          

      | If (condition, then_expr, else_expr) ->
          let eval_condition = evaluate env condition in
          (match eval_condition with
          | VBool true -> evaluate env then_expr
          | VBool false -> evaluate env else_expr
          | _ -> assert false)
      | Bop (operator, expr1, expr2) ->
          (match operator with
          | And ->
              (match evaluate env expr1 with
              | VBool false -> VBool false
              | VBool true -> evaluate env expr2
              | _ -> assert false)
          | Or ->
              (match evaluate env expr1 with
              | VBool true -> VBool true
              | VBool false -> evaluate env expr2
              | _ -> assert false)
          | _ ->
              let value1 = evaluate env expr1 in
              let value2 = evaluate env expr2 in
              (match (value1, value2, operator) with
              | (VNum num1, VNum num2, Add) -> VNum (num1 + num2)
              | (VNum num1, VNum num2, Sub) -> VNum (num1 - num2)
              | (VNum num1, VNum num2, Mul) -> VNum (num1 * num2)
              | (VNum num1, VNum num2, Div) ->
                  if num2 = 0 then raise DivByZero else VNum (num1 / num2)
              | (VNum num1, VNum num2, Mod) ->
                  if num2 = 0 then raise DivByZero else VNum (num1 mod num2)
              | (VNum num1, VNum num2, Lt) -> VBool (num1 < num2)
              | (VNum num1, VNum num2, Lte) -> VBool (num1 <= num2)
              | (VNum num1, VNum num2, Gt) -> VBool (num1 > num2)
              | (VNum num1, VNum num2, Gte) -> VBool (num1 >= num2)
              | (VNum num1, VNum num2, Eq) -> VBool (num1 = num2)
              | (VNum num1, VNum num2, Neq) -> VBool (num1 <> num2)
              | _ -> assert false))
      | Assert expression ->
          (match evaluate env expression with
          | VBool true -> VUnit
          | VBool false -> raise AssertFail
          | _ -> assert false)
    in
    evaluate Env.empty expr
  
  
  
  

let interp str =
 match parse str with
 | Some prog -> (
     let desugared = desugar prog in
     match type_of desugared with
     | Ok _ -> Ok (eval desugared)
     | Error e -> Error e)
 | None -> Error ParseErr
