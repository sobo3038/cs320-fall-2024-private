
open Utils
include My_parser

exception AssertFail
exception DivByZero
exception RecWithoutArg
exception CompareFunVals

let rec unify ty constraints =
  let collect_and_sort_free_vars =
    let rec collect ty =
      match ty with
      | TVar x -> [x]
      | TFun (t1, t2)
      | TPair (t1, t2) ->
          collect t1 @ collect t2
      | TList t
      | TOption t ->
          collect t
      | _ -> []
    in
    fun ty ->
      let sorted = List.sort compare (collect ty) in
      let rec dedup acc = function
        | [] -> List.rev acc
        | [x] -> List.rev (x :: acc)
        | x :: y :: xs ->
            if compare x y = 0 then dedup acc (y :: xs)
            else dedup (x :: acc) (y :: xs)
      in
      dedup [] sorted
  in
  let rec variable_occurs var ty =
    match ty with
    | TVar y -> var = y
    | TFun (t1, t2)
    | TPair (t1, t2) ->
        variable_occurs var t1 || variable_occurs var t2
    | TList t
    | TOption t ->
        variable_occurs var t
    | _ -> false
  in
  let rec substitute_types subst ty =
    match ty with
    | TVar x ->
        (try List.assoc x subst with Not_found -> ty)
    | TFun (t1, t2) ->
        TFun (substitute_types subst t1, substitute_types subst t2)
    | TPair (t1, t2) ->
        TPair (substitute_types subst t1, substitute_types subst t2)
    | TList t ->
        TList (substitute_types subst t)
    | TOption t ->
        TOption (substitute_types subst t)
    | other -> other
  in
  let substitute_in_constraints subst cons =
    List.map (fun (a, b) -> (substitute_types subst a, substitute_types subst b)) cons
  in
  match constraints with
  | [] ->
      let fv = collect_and_sort_free_vars ty in
      Some (Forall (fv, ty))
  | (t1, t2) :: rest_constraints when t1 = t2 ->
      unify ty rest_constraints
  | (TVar x, t) :: rest
  | (t, TVar x) :: rest ->
      if variable_occurs x t then None
      else
        let subst = [(x, t)] in
        let new_ty = substitute_types subst ty in
        let new_constraints = substitute_in_constraints subst rest in
        unify new_ty new_constraints
  | (TFun (ta1, ta2), TFun (tb1, tb2)) :: rest ->
      unify ty ((ta1, tb1) :: (ta2, tb2) :: rest)
  | (TPair (pa1, pa2), TPair (pb1, pb2)) :: rest ->
      unify ty ((pa1, pb1) :: (pa2, pb2) :: rest)
  | (TList ta, TList tb) :: rest
  | (TOption ta, TOption tb) :: rest ->
      unify ty ((ta, tb) :: rest)
  | _ -> None










  





  let type_of (env : stc_env) (e : expr) : ty_scheme option =
    let inner env e =
      let rec apply subst ty =
        match ty with
        | TVar x ->
            (match List.assoc_opt x subst with
             | Some t -> t
             | None -> TVar x)
        | TFun (t1, t2) ->
            TFun (apply subst t1, apply subst t2)
        | TPair (t1, t2) ->
            TPair (apply subst t1, apply subst t2)
        | TList t ->
            TList (apply subst t)
        | TOption t ->
            TOption (apply subst t)
        | ty -> ty
      in
      let instance (vars, ty) =
        let generate_subst = List.map (fun var -> (var, TVar (gensym ()))) in
        apply (generate_subst vars) ty      
      in  
      let rec infer env expr =
        let fresh_type () = TVar (gensym ()) in
        let combine_constraints cs1 cs2 = cs1 @ cs2 in
  
        let infer_bop op e1 e2 =
          let t1, c1 = infer env e1 in
          let t2, c2 = infer env e2 in
          let result_type, additional_constraints = 
            match op with
            | Add | Sub | Mul | Div | Mod ->
                (TInt, [(t1, TInt); (t2, TInt)])
            | AddF | SubF | MulF | DivF | PowF ->
                (TFloat, [(t1, TFloat); (t2, TFloat)])
            | And | Or ->
                (TBool, [(t1, TBool); (t2, TBool)])
            | Eq | Neq ->
                let fresh = fresh_type () in
                (TBool, [(t1, fresh); (t2, fresh)])
            | Lt | Lte | Gt | Gte ->
                (TBool, [(t1, t2)])
            | Cons ->
                (TList t1, [(t2, TList t1)])
            | Concat ->
                let fresh = fresh_type () in
                (TList fresh, [(t1, TList fresh); (t2, TList fresh)])
            | Comma ->
                (TPair (t1, t2), [])
          in
          (result_type, additional_constraints @ c1 @ c2)
        in
  
        let infer_fun arg ty_opt body =
          let arg_type, updated_env = 
            match ty_opt with
            | Some ty ->
                (ty, Env.add arg (Forall ([], ty)) env)
            | None ->
                let fresh_arg = fresh_type () in
                (fresh_arg, Env.add arg (Forall ([], fresh_arg)) env)
          in
          let t_body, c_body = infer updated_env body in
          (TFun (arg_type, t_body), c_body)
        in
  
        let infer_let is_rec name value body =
          if not is_rec then
            let t_val, c_val = infer env value in
            let new_env = Env.add name (Forall ([], t_val)) env in
            let t_body, c_body = infer new_env body in
            (t_body, combine_constraints c_val c_body)
          else
            let fresh1 = fresh_type () in
            let fresh2 = fresh_type () in
            let rec_env = Env.add name (Forall ([], TFun (fresh1, fresh2))) env in
            let _, c_val = infer rec_env value in
            let body_env = Env.add name (Forall ([], TFun (fresh1, fresh2))) env in
            let t_body, c_body = infer body_env body in
            (t_body, combine_constraints c_val c_body)
        in
  
        match expr with
        | Unit -> (TUnit, [])
        | True | False -> (TBool, [])
        | Int _ -> (TInt, [])
        | Float _ -> (TFloat, [])
        | Var x -> (
            match Env.find_opt x env with
            | Some (Forall (vars, t)) -> (instance (vars, t), [])
            | None -> failwith ("Unbound variable: " ^ x)
          )
        | ENone -> (TOption (fresh_type ()), [])
        | ESome e ->
            let t, c = infer env e in
            (TOption t, c)
        | Nil -> (TList (fresh_type ()), [])
        | OptMatch { matched; some_name; some_case; none_case } ->
            let t_matched, c_matched = infer env matched in
            let fresh_elem = fresh_type () in
            let env_with_some = Env.add some_name (Forall ([], fresh_elem)) env in
            let t_some_case, c_some = infer env_with_some some_case in
            let t_none_case, c_none = infer env none_case in
            let constraints = 
              (t_matched, TOption fresh_elem) ::
              (t_some_case, t_none_case) ::
              combine_constraints c_matched (combine_constraints c_some c_none)
            in
            (t_some_case, constraints)
        | Bop (op, e1, e2) ->
            infer_bop op e1 e2
        | If (e1, e2, e3) ->
            let t1, c1 = infer env e1 in
            let t2, c2 = infer env e2 in
            let t3, c3 = infer env e3 in
            (t3, [(t1, TBool); (t2, t3)] @ combine_constraints c1 (combine_constraints c2 c3))
        | Fun (x, ty_opt, body) ->
            infer_fun x ty_opt body
        | App (e1, e2) ->
            let t_fun, c_fun = infer env e1 in
            let t_arg, c_arg = infer env e2 in
            let fresh = fresh_type () in
            let constraints = (t_fun, TFun (t_arg, fresh)) :: combine_constraints c_fun c_arg in
            (fresh, constraints)
        | Let { is_rec; name; value; body } ->
            infer_let is_rec name value body
        | Assert False -> (fresh_type (), [])
        | Assert e ->
            let t, c = infer env e in
            (TUnit, (t, TBool) :: c)
        | Annot (e, ty) ->
            let t, c = infer env e in
            (ty, (t, ty) :: c)
        | PairMatch { matched; fst_name; snd_name; case } ->
            let t_matched, c_matched = infer env matched in
            let fresh1 = fresh_type () in
            let fresh2 = fresh_type () in
            let extended_env = 
              Env.add fst_name (Forall ([], fresh1)) (Env.add snd_name (Forall ([], fresh2)) env)
            in
            let t_case, c_case = infer extended_env case in
            (t_case, (t_matched, TPair (fresh1, fresh2)) :: combine_constraints c_matched c_case)
        | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } ->
            let t_matched, c_matched = infer env matched in
            let fresh_elem = fresh_type () in
            let env_hd = Env.add hd_name (Forall ([], fresh_elem)) env in
            let env_tl = Env.add tl_name (Forall ([], TList fresh_elem)) env_hd in
            let t_cons_case, c_cons_case = infer env_tl cons_case in
            let t_nil_case, c_nil_case = infer env nil_case in
            let constraints =
              (t_matched, TList fresh_elem) ::
              (t_cons_case, t_nil_case) ::
              combine_constraints c_matched (combine_constraints c_cons_case c_nil_case)
            in
            (t_nil_case, constraints)
      in
    
      try
        let t, c = infer env e in
        let t = unify t c in
        match t with
        | Some t -> Some t 
        | None -> None
      with _ -> None
    in
    inner env e
  
  

  













    let rec eval_expr env expr : value =
      let rec evaluate e =
        let eval_bop op a b =
          match op, a, b with
          | Add, VInt m, VInt n -> VInt (m + n)
          | AddF, VFloat m, VFloat n -> VFloat (m +. n)
          | Sub, VInt m, VInt n -> VInt (m - n)
          | SubF, VFloat m, VFloat n -> VFloat (m -. n)
          | Mul, VInt m, VInt n -> VInt (m * n)
          | MulF, VFloat m, VFloat n -> VFloat (m *. n)
          | Div, VInt _, VInt 0 -> raise DivByZero
          | Div, VInt m, VInt n -> VInt (m / n)
          | DivF, VFloat m, VFloat n -> VFloat (m /. n)
          | Mod, VInt m, VInt n when n <> 0 -> VInt (m mod n)
          | Mod, VInt _, VInt 0 -> failwith "Division by zero in modulo operation"
          | Mod, VInt _, VInt _ -> failwith "Modulo operation requires two numbers"
          | PowF, VFloat m, VFloat n -> VFloat (m ** n)
          | Eq, VClos _, _ | Eq, _, VClos _ -> raise CompareFunVals
          | Eq, VInt m, VInt n -> VBool (m = n)
          | Eq, VFloat x, VFloat y -> VBool (x = y)
          | Eq, VBool p, VBool q -> VBool (p = q)
          | Eq, VUnit, VUnit -> VBool true
          | Eq, VList l1, VList l2 -> VBool (l1 = l2)
          | Eq, VPair (x1, y1), VPair (x2, y2) -> VBool (x1 = x2 && y1 = y2)
          | Eq, VSome u, VSome v -> VBool (u = v)
          | Eq, VNone, VNone -> VBool true
          | Eq, _, _ -> VBool false
          | Neq, VClos _, _ | Neq, _, VClos _ -> raise CompareFunVals
          | Neq, VInt m, VInt n -> VBool (m <> n)
          | Neq, VFloat x, VFloat y -> VBool (x <> y)
          | Neq, VBool p, VBool q -> VBool (p <> q)
          | Neq, VUnit, VUnit -> VBool false
          | Neq, VList u, VList v -> VBool (u <> v)
          | Neq, VPair (a1, b1), VPair (a2, b2) -> VBool (a1 <> a2 || b1 <> b2)
          | Neq, VSome w1, VSome w2 -> VBool (w1 <> w2)
          | Neq, VNone, VNone -> VBool false
          | Neq, _, _ -> VBool true
          | Lt, VInt m, VInt n -> VBool (m < n)
          | Lt, VFloat m, VFloat n -> VBool (m < n)
          | Lt, VBool x, VBool y -> VBool ((not x) && y)
          | Lt, VList l1, VList l2 -> VBool (l1 < l2)
          | Lt, VSome c1, VSome c2 -> VBool (c1 < c2)
          | Lt, VNone, VSome _ -> VBool true
          | Lt, VNone, VNone -> VBool false
          | Lt, _, _ -> failwith "Lt requires comparable types"
          | Lte, VInt m, VInt n -> VBool (m <= n)
          | Lte, VFloat m, VFloat n -> VBool (m <= n)
          | Lte, VBool p, VBool q -> VBool ((not q) || p)
          | Lte, VList l1, VList l2 -> VBool (l1 <= l2)
          | Lte, VSome w1, VSome w2 -> VBool (w1 <= w2)
          | Lte, VNone, VSome _ -> VBool true
          | Lte, VNone, VNone -> VBool true
          | Lte, _, _ -> VBool true
          | Gt, VInt m, VInt n -> VBool (m > n)
          | Gt, VFloat m, VFloat n -> VBool (m > n)
          | Gt, VBool p, VBool q -> VBool (p && not q)
          | Gt, VPair (x1, y1), VPair (x2, y2) -> VBool ((x1, y1) > (x2, y2))
          | Gt, VSome c1, VSome c2 -> VBool (c1 > c2)
          | Gt, VNone, VSome _ -> VBool false
          | Gt, VNone, VNone -> VBool false
          | Gt, VList la, VList lb -> VBool (la > lb)
          | Gt, _, _ -> failwith "Gt requires comparable types"
          | Gte, VInt m, VInt n -> VBool (m >= n)
          | Gte, VFloat m, VFloat n -> VBool (m >= n)
          | Gte, VBool p, VBool q -> VBool (p || not q)
          | Gte, VList l1, VList l2 -> VBool (l1 >= l2)
          | Gte, VSome v1, VSome v2 -> VBool (v1 >= v2)
          | Gte, VSome _, VNone -> VBool true
          | Gte, VNone, VNone -> VBool true
          | Gte, VUnit, VUnit -> VBool true
          | Gte, _, _ -> VBool true
          | And, VBool false, _ -> VBool false
          | And, VBool true, vb -> vb
          | And, _, _ -> failwith "Logical 'and' requires boolean operands"
          | Or, VBool true, _ -> VBool true
          | Or, VBool false, vb -> vb
          | Or, _, _ -> failwith "Logical 'or' requires boolean operands"
          | _, _, _ -> failwith "Unsupported operand types for binary operation"
        in
    
        let eval_app e1 e2 =
          match evaluate e1 with
          | VClos { env = v_env; name = v_name; arg = v_arg; body = v_body } ->
              let v_env =
                match v_name with
                | None -> v_env
                | Some nm ->
                    Env.add nm
                      (VClos { env = v_env; name = Some nm; arg = v_arg; body = v_body })
                      v_env
              in
              let arg_val = evaluate e2 in
              eval_expr (Env.add v_arg arg_val v_env) v_body
          | _ -> failwith "impossible"
        in
    
        let eval_opt_match matched some_name some_case none_case =
          match evaluate matched with
          | VSome v -> eval_expr (Env.add some_name v env) some_case
          | VNone -> eval_expr env none_case
          | _ -> failwith "Expected an option"
        in
    
        let eval_list_match matched hd_name tl_name cons_case nil_case =
          match evaluate matched with
          | VList (h :: t) ->
              eval_expr (Env.add tl_name (VList t) (Env.add hd_name h env)) cons_case
          | VList [] -> eval_expr env nil_case
          | _ -> failwith "Expected a list"
        in
    
        let eval_pair_match matched fst_name snd_name case =
          match evaluate matched with
          | VPair (x, y) ->
              eval_expr (Env.add snd_name y (Env.add fst_name x env)) case
          | _ -> failwith "Expected a pair"
        in
    
        let eval_let is_rec name value body =
          if not is_rec then
            let v_val = evaluate value in
            eval_expr (Env.add name v_val env) body
          else
            match evaluate value with
            | VClos { name = None; arg; body = cb; env = ce } ->
                let rec_env =
                  Env.add name (VClos { name = Some name; arg; body = cb; env = ce }) env
                in
                eval_expr rec_env body
            | VClos { name = Some _; _ } -> raise RecWithoutArg
            | _ -> failwith "Expected a closure in recursive let binding"
        in
    
        match e with
        | Unit -> VUnit
        | True -> VBool true
        | False -> VBool false
        | Int n -> VInt n
        | Float f -> VFloat f
        | ENone -> VNone
        | Nil -> VList []
        | Var x -> Env.find x env
        | Fun (x, _, b) -> VClos { name = None; arg = x; body = b; env }
        | App (e1, e2) -> eval_app e1 e2
        | Bop (op, a, b) -> eval_bop op (evaluate a) (evaluate b)
        | If (c, t, f) ->
            (match evaluate c with
             | VBool true -> evaluate t
             | VBool false -> evaluate f
             | _ -> failwith "Condition in if-expression must be a boolean")
        | ESome e -> VSome (evaluate e)
        | OptMatch { matched; some_name; some_case; none_case } ->
            eval_opt_match matched some_name some_case none_case
        | PairMatch { matched; fst_name; snd_name; case } ->
            eval_pair_match matched fst_name snd_name case
        | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } ->
            eval_list_match matched hd_name tl_name cons_case nil_case
        | Assert e1 ->
            (match evaluate e1 with
             | VBool true -> VUnit
             | VBool false -> raise AssertFail
             | _ -> raise AssertFail)
        | Let { is_rec; name; value; body } ->
            eval_let is_rec name value body
        | Annot (e, _) -> evaluate e
      in
      evaluate expr
    












let type_check prog =
  let rec go env = function
    | [] -> Some (Forall ([], TUnit))
    | { is_rec; name; value } :: rest ->
      match type_of env (Let { is_rec; name; value; body = Var name }) with
      | Some ty -> go (Env.add name ty env) rest
      | None -> None
  in
  go Env.empty prog

  let eval p =
    let rec nest = function
      | [] -> Unit
      | [{is_rec;name;value}] -> Let {is_rec;name;value;body = Var name}
      | {is_rec;name;value} :: ls -> Let {is_rec;name;value;body = nest ls}
    in eval_expr Env.empty (nest p)

let interp input =
  match parse input with
  | Some prog -> (
      match type_check prog with
      | Some ty -> Ok (eval prog, ty)
      | None -> Error TypeError
    )
  | None -> Error ParseError