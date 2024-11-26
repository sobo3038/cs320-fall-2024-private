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
      | Var x -> (
          match Env.find_opt x env with
          | Some ty -> Ok ty
          | None -> Error (UnknownVar x)
      )
      | Let { is_rec; name; ty = expected_ty; value; body } -> (
          if is_rec then (
              let extended_env = Env.add name expected_ty env in
              match typecheck extended_env value with
              | Ok actual_ty when actual_ty = expected_ty ->
                  typecheck (Env.add name expected_ty extended_env) body
              | Ok actual_ty -> Error (LetTyErr (expected_ty, actual_ty))
              | Error e -> Error e
          ) else (
              match typecheck env value with
              | Ok actual_ty when actual_ty = expected_ty ->
                  typecheck (Env.add name actual_ty env) body
              | Ok actual_ty -> Error (LetTyErr (expected_ty, actual_ty))
              | Error e -> Error e
          )
      )
      | Fun (arg, arg_ty, body) ->
          let extended_env = Env.add arg arg_ty env in
          (match typecheck extended_env body with
          | Ok body_ty -> Ok (FunTy (arg_ty, body_ty))
          | Error e -> Error e)
      | App (e1, e2) -> (
          match typecheck env e1 with
          | Ok (FunTy (arg_ty, ret_ty)) -> (
              match typecheck env e2 with
              | Ok actual_ty when arg_ty = actual_ty -> Ok ret_ty
              | Ok actual_ty -> Error (FunArgTyErr (arg_ty, actual_ty))
              | Error e -> Error e
          )
          | Ok ty -> Error (FunAppTyErr ty)
          | Error e -> Error e
      )
      | If (cond, then_, else_) -> (
          match typecheck env cond with
          | Ok BoolTy -> (
              match typecheck env then_ with
              | Ok ty_then -> (
                  match typecheck env else_ with
                  | Ok ty_else when ty_then = ty_else -> Ok ty_then
                  | Ok ty_else -> Error (IfTyErr (ty_then, ty_else))
                  | Error e -> Error e
              )
              | Error e -> Error e
          )
          | Ok ty -> Error (IfCondTyErr ty)
          | Error e -> Error e
      )
      | Bop (op, e1, e2) -> (
          let (expected_ty1, expected_ty2, result_ty) = match op with
          | Add | Sub | Mul | Div | Mod -> (IntTy, IntTy, IntTy)
          | Lt | Lte | Gt | Gte | Eq | Neq -> (IntTy, IntTy, BoolTy)
          | And | Or -> (BoolTy, BoolTy, BoolTy)
          in
          match typecheck env e1 with
          | Error e -> Error e 
          | Ok ty1 when ty1 <> expected_ty1 -> Error (OpTyErrL (op, expected_ty1, ty1))
          | Ok _ -> (
              match typecheck env e2 with
              | Error e -> Error e 
              | Ok ty2 when ty2 <> expected_ty2 -> Error (OpTyErrR (op, expected_ty2, ty2))
              | Ok _ -> Ok result_ty 
          )
      )

      | Assert e -> (
          match typecheck env e with
          | Ok BoolTy -> Ok UnitTy
          | Ok ty -> Error (AssertTyErr ty)
          | Error e -> Error e
      )
  in
  typecheck Env.empty expr



  let eval (expr : expr) : value =
    let rec evaluate_expression environment current_expr =
      match current_expr with
      | Unit -> VUnit
      | Num number -> VNum number
      | True -> VBool true
      | False -> VBool false
      | Var variable -> Env.find variable environment
      | Let { is_rec; name; ty = _; value; body } ->
          let updated_environment =
            if is_rec then
              let rec_closure =
                (match value with
                | Fun (argument, _, function_body) ->
                    VClos { name = Some name; arg = argument; body = function_body; env = environment }
                | _ ->
                    let generated_argument = gensym () in
                    let wrapped_function = Fun (generated_argument, UnitTy, value) in
                    VClos { name = Some name; arg = generated_argument; body = wrapped_function; env = environment })
              in
              Env.add name rec_closure environment
            else
              let evaluated_value = evaluate_expression environment value in
              Env.add name evaluated_value environment
          in
          evaluate_expression updated_environment body
      | Fun (argument, _, function_body) ->
          VClos { name = None; arg = argument; body = function_body; env = environment }
      | App (function_expr, argument_expr) ->
          let evaluated_function = evaluate_expression environment function_expr in
          let evaluated_argument = evaluate_expression environment argument_expr in
          (match evaluated_function with
          | VClos { name = Some func_name; arg; body; env = closure_environment } ->
              let extended_environment =
                Env.add func_name evaluated_function
                  (Env.add arg evaluated_argument closure_environment)
              in
              evaluate_expression extended_environment body
          | VClos { name = None; arg; body; env = closure_environment } ->
              let extended_environment = Env.add arg evaluated_argument closure_environment in
              evaluate_expression extended_environment body
          | _ -> assert false)
      | If (condition, then_expr, else_expr) ->
          let evaluated_condition = evaluate_expression environment condition in
          (match evaluated_condition with
          | VBool true -> evaluate_expression environment then_expr
          | VBool false -> evaluate_expression environment else_expr
          | _ -> assert false)
      | Bop (operator, expr1, expr2) ->
          (match operator with
          | And ->
              (match evaluate_expression environment expr1 with
              | VBool false -> VBool false
              | VBool true -> evaluate_expression environment expr2
              | _ -> assert false)
          | Or ->
              (match evaluate_expression environment expr1 with
              | VBool true -> VBool true
              | VBool false -> evaluate_expression environment expr2
              | _ -> assert false)
          | _ ->
              let value1 = evaluate_expression environment expr1 in
              let value2 = evaluate_expression environment expr2 in
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
          (match evaluate_expression environment expression with
          | VBool true -> VUnit
          | VBool false -> raise AssertFail
          | _ -> assert false)
    in
    evaluate_expression Env.empty expr
  
  
  

let interp str =
 match parse str with
 | Some prog -> (
     let desugared = desugar prog in
     match type_of desugared with
     | Ok _ -> Ok (eval desugared)
     | Error e -> Error e)
 | None -> Error ParseErr



