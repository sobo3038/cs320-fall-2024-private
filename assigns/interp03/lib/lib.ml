open Utils
include My_parser
exception AssertFail
exception DivByZero
exception RecWithoutArg
exception CompareFunVals

let rec unify ty constraints =
  let rec occurs x ty =
    match ty with
    | TVar y -> x = y
    | TFun (t1, t2) | TPair (t1, t2) -> occurs x t1 || occurs x t2
    | TList t | TOption t -> occurs x t
    | _ -> false
  in
  let rec free_vars ty =
    match ty with
    | TVar x -> [x]
    | TFun (t1, t2) | TPair (t1, t2) -> free_vars t1 @ free_vars t2
    | TList t | TOption t -> free_vars t
    | _ -> []
  in
  let rec apply_subst subst ty =
    match ty with
    | TVar x -> (try List.assoc x subst with Not_found -> ty)
    | TFun (t1, t2) -> TFun (apply_subst subst t1, apply_subst subst t2)
    | TPair (t1, t2) -> TPair (apply_subst subst t1, apply_subst subst t2)
    | TList t -> TList (apply_subst subst t)
    | TOption t -> TOption (apply_subst subst t)
    | _ -> ty
  in
  let apply_subst_to_constraints subst constraints =
    List.map (fun (t1, t2) -> (apply_subst subst t1, apply_subst subst t2)) constraints
  in
  let sort_uniq cmp lst =
    let sorted = List.sort cmp lst in
    let rec uniq acc = function
      | [] -> List.rev acc
      | [x] -> List.rev (x :: acc)
      | x :: (y :: _ as rest) -> if cmp x y = 0 then uniq acc rest else uniq (x :: acc) rest
    in
    uniq [] sorted
  in
  match constraints with
  | [] -> 
    let free = sort_uniq compare (free_vars ty) in
    Some (Forall (free, ty)) 
  | (t1, t2) :: rest when t1 = t2 -> unify ty rest 
  | (TVar x, t) :: rest | (t, TVar x) :: rest ->
    if occurs x t then None 
    else
      let subst = [(x, t)] in
      let unified_ty = apply_subst subst ty in
      let unified_constraints = apply_subst_to_constraints subst rest in
      (match unify unified_ty unified_constraints with
       | Some (Forall (vars, final_ty)) ->
         let new_vars = List.filter (fun v -> v <> x) vars in
         Some (Forall (new_vars, final_ty))
       | None -> None)
  | (TFun (t1a, t1b), TFun (t2a, t2b)) :: rest ->
    unify ty ((t1a, t2a) :: (t1b, t2b) :: rest)
  | (TPair (t1a, t1b), TPair (t2a, t2b)) :: rest ->
    unify ty ((t1a, t2a) :: (t1b, t2b) :: rest)
  | (TList t1, TList t2) :: rest | (TOption t1, TOption t2) :: rest ->
    unify ty ((t1, t2) :: rest)
  | (TInt, TFloat) :: _ | (TFloat, TInt) :: _ -> None 
  | (TBool, TInt) :: _ | (TBool, TFloat) :: _ -> None 
  | _ -> None

let type_of (env : stc_env) (e : expr) : ty_scheme option =
  let rec free_vars ty =
    match ty with
    | TVar x -> [x]
    | TFun (t1, t2) | TPair (t1, t2) -> free_vars t1 @ free_vars t2
    | TList t | TOption t -> free_vars t
    | _ -> []
  in
  let rec apply_subst subst ty =
    match ty with
    | TVar x -> (try List.assoc x subst with Not_found -> ty)
    | TFun (t1, t2) -> TFun (apply_subst subst t1, apply_subst subst t2)
    | TPair (t1, t2) -> TPair (apply_subst subst t1, apply_subst subst t2)
    | TList t -> TList (apply_subst subst t)
    | TOption t -> TOption (apply_subst subst t)
    | _ -> ty
  in
  let instantiate (vars, ty) =
    let subst = List.map (fun var -> (var, TVar (gensym ()))) vars in
    apply_subst subst ty
  in
  let free_vars_in_env env =
    List.fold_left
      (fun acc (_, Forall (_, t)) -> free_vars t @ acc)
      [] (Env.to_list env)
  in
  let rec infer env = function
    | Unit -> (TUnit, [])
    | True | False -> (TBool, [])
    | Int _ -> (TInt, [])
    | Float _ -> (TFloat, [])
    | Var x -> (
        match Env.find_opt x env with
        | Some (Forall (vars, t)) -> (instantiate (vars, t), [])
        | None -> failwith ("Unbound variable: " ^ x)
      )
    | ENone -> (TOption (TVar (gensym ())), [])
    | ESome e ->
      let t, c = infer env e in
      (TOption t, c)
    | Nil -> (TList (TVar (gensym ())), [])
    | OptMatch { matched; some_name; some_case; none_case } ->
      let t_matched, c_matched = infer env matched in
      let fresh_elem = TVar (gensym ()) in
      let env_with_some = Env.add some_name (Forall ([], fresh_elem)) env in
      let t_some_case, c_some = infer env_with_some some_case in
      let t_none_case, c_none = infer env none_case in
      (t_some_case, (t_matched, TOption fresh_elem) :: (t_some_case, t_none_case) :: c_matched @ c_some @ c_none)
    | Bop (op, e1, e2) -> (
        let t1, c1 = infer env e1 in
        let t2, c2 = infer env e2 in
        match op with
        | Add | Sub | Mul | Div | Mod ->
            (TInt, (t1, TInt) :: (t2, TInt) :: c1 @ c2)
        | AddF | SubF | MulF | DivF | PowF ->
            (TFloat, (t1, TFloat) :: (t2, TFloat) :: c1 @ c2)
        | And | Or ->
            (TBool, (t1, TBool) :: (t2, TBool) :: c1 @ c2)
        | Eq | Neq ->
          let fresh = TVar (gensym ()) in
          (TBool, (t1, fresh) :: (t2, fresh) :: c1 @ c2)
        | Lt | Lte | Gt | Gte ->
          let fresh = TVar (gensym ()) in
          (TBool, (t1, fresh) :: (t2, fresh) :: c1 @ c2)
        | Cons ->
          let t1, c1 = infer env e1 in
          let t2, c2 = infer env e2 in
          (TList t1, (t2, TList t1) :: c1 @ c2)
        | Concat ->
          let t1, c1 = infer env e1 in
          let t2, c2 = infer env e2 in
          let fresh = TVar (gensym ()) in
          (TList fresh, (t1, TList fresh) :: (t2, TList fresh) :: c1 @ c2)
        | Comma ->
          let t1, c1 = infer env e1 in
          let t2, c2 = infer env e2 in
          (TPair (t1, t2), c1 @ c2)
      )
    | If (e1, e2, e3) ->
        let t1, c1 = infer env e1 in
        let t2, c2 = infer env e2 in
        let t3, c3 = infer env e3 in
        (t2, (t1, TBool) :: (t2, t3) :: c1 @ c2 @ c3)
    | Fun (x, Some ty, body) ->
        let env = Env.add x (Forall ([], ty)) env in
        let t_body, c_body = infer env body in
        (TFun (ty, t_body), c_body)
    | Fun (arg, None, body) ->
      let fresh_arg = TVar (gensym ()) in
      let env = Env.add arg (Forall ([], fresh_arg)) env in
      let t_body, c_body = infer env body in
      (TFun (fresh_arg, t_body), c_body)   
    | App (e1, e2) ->
      let t_fun, c_fun = infer env e1 in
      let t_arg, c_arg = infer env e2 in
      let fresh = TVar (gensym ()) in
      (fresh, (t_fun, TFun (t_arg, fresh)) :: c_fun @ c_arg)
    | Let { is_rec = false; name; value; body } ->
      let t_val, c_val = infer env value in
      let env = Env.add name (Forall ([], t_val)) env in
      let t_body, c_body = infer env body in
      (t_body, c_val @ c_body)
    | Let { is_rec = true; name; value; body } ->
      let fresh = TVar (gensym ()) in
      let env_with_fresh = Env.add name (Forall ([], fresh)) env in
      let t_val, c_val = infer env_with_fresh value in
      let env_free_vars = free_vars_in_env env in
      let generalized_type =
        Forall (
          List.filter (fun v -> not (List.mem v env_free_vars)) (free_vars t_val),
          t_val
        )
      in
      let env = Env.add name generalized_type env in
      let t_body, c_body = infer env body in
      (t_body, c_val @ c_body)
    | Assert False -> (TVar (gensym ()), [])
    | Assert e ->
      let t, c = infer env e in
      (TUnit, (t, TBool) :: c)  
    | Annot (e, ty) ->
        let t, c = infer env e in
        (ty, (t, ty) :: c)
    | PairMatch { matched; fst_name; snd_name; case } ->
      let t_matched, c_matched = infer env matched in
      let fresh1 = TVar (gensym ()) in
      let fresh2 = TVar (gensym ()) in
      let extended_env = Env.add fst_name (Forall ([], fresh1)) (Env.add snd_name (Forall ([], fresh2)) env) in
      let t_case, c_case = infer extended_env case in
      (t_case, (t_matched, TPair (fresh1, fresh2)) :: c_matched @ c_case)
    | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } ->
      let t_matched, c_matched = infer env matched in
      let fresh_elem = TVar (gensym ()) in
      let env_hd = Env.add hd_name (Forall ([], fresh_elem)) env in
      let env_tl = Env.add tl_name (Forall ([], TList fresh_elem)) env_hd in
      let t_cons_case, c_cons_case = infer env_tl cons_case in
      let t_nil_case, c_nil_case = infer env nil_case in
      (t_nil_case, (t_matched, TList fresh_elem) :: (t_cons_case, t_nil_case) :: c_matched @ c_cons_case @ c_nil_case)
  in
  try
    let t, c = infer env e in
    let t = unify t c in
    match t with
    | Some t -> Some t 
    | None -> None
  with _ -> None

let rec eval_expr env expr : value = 
  let rec go = function
  | Unit -> VUnit 
  | True -> VBool true 
  | False -> VBool false 
  | Int n -> VInt n
  | Float f -> VFloat f
  | ENone -> VNone
  | Nil -> VList []
  | Var x -> Env.find x env
  | Fun (x, _, body) -> VClos {name=None; arg = x; body; env}
  | App (e1, e2) -> (
        match go e1 with
        | VClos { env; name; arg; body } ->
          let env =
            match name with
            | None -> env
            | Some name -> Env.add name (VClos { env; name = Some name; arg; body }) env
          in
          let env = Env.add arg (go e2) env in
          eval_expr env body
        | _ -> failwith "impossible"
      )
  | Bop (Add, e1, e2) -> 
      (match go e1, go e2 with
      | VInt m, VInt n -> VInt (m+n)
      | _ -> failwith "impossible")
  | Bop (AddF, e1, e2) -> 
        (match go e1, go e2 with
        | VFloat m, VFloat n -> VFloat (m+.n)
        | _ -> failwith "impossible")
  | Bop (Sub, e1, e2) -> 
      (match go e1, go e2 with
      | VInt m, VInt n -> VInt (m-n)
      | _ -> failwith "impossible")
  | Bop (SubF, e1, e2) -> 
      (match go e1, go e2 with
      | VFloat m, VFloat n -> VFloat (m-.n)
      | _ -> failwith "impossible")
  | Bop (Mul, e1, e2) -> 
      (match go e1, go e2 with
      | VInt m, VInt n -> VInt (m*n)
      | _ -> failwith "impossible")
  | Bop (MulF, e1, e2) -> 
        (match go e1, go e2 with
        | VFloat m, VFloat n -> VFloat (m*.n)
        | _ -> failwith "impossible")
  | Bop (Div, e1, e2) -> 
      (match go e1 with
      | (VInt m) -> (
          match go e2 with
          | (VInt 0) -> raise DivByZero
          | (VInt n) -> (VInt (m / n))
          | _ -> failwith (""))
        | _ -> failwith (""))
  | Bop (DivF, e1, e2) -> 
    (match go e1 with
    | (VFloat m) -> (
        match go e2 with
        | (VFloat n) -> (VFloat (m /. n))
        | _ ->  (failwith (""))
      )
      | _ ->  (failwith ("")) )
  | Bop (Mod, e1, e2) -> (
      match go e1, go e2 with
      | VInt m, VInt n when n <> 0 -> VInt (m mod n)
      | VInt _, VInt 0 -> failwith "Division by zero in modulo operation"
      | _ -> failwith "Modulo operation requires two numbers")
  | Bop (PowF, e1, e2) -> 
        (match go e1, go e2 with
        | VFloat m, VFloat n -> VFloat (m**n)
        | _ -> failwith "impossible")
  | Bop (Eq, e1, e2) -> (
    match go e1, go e2 with
    | VClos _, _ | _, VClos _ -> raise CompareFunVals
    | VInt m, VInt n -> VBool (m = n)
    | VFloat m, VFloat n -> VBool (m = n)
    | VBool m, VBool n -> VBool (m = n)
    | VUnit, VUnit -> VBool true
    | VList lst1, VList lst2 -> VBool (lst1 = lst2)
    | VPair (v1a, v1b), VPair (v2a, v2b) -> VBool (v1a = v2a && v1b = v2b)
    | VSome v1, VSome v2 -> VBool (v1 = v2)
    | VNone, VNone -> VBool true
    | _ -> VBool false)
  | Bop (Neq, e1, e2) -> (
      match go e1, go e2 with
      | VClos _, _ | _, VClos _ -> raise CompareFunVals
      | VInt m, VInt n -> VBool (m <> n)
      | VFloat m, VFloat n -> VBool (m <> n)
      | VBool m, VBool n -> VBool (m <> n)
      | VUnit, VUnit -> VBool false
      | VList lst1, VList lst2 -> VBool (lst1 <> lst2)
      | VPair (v1a, v1b), VPair (v2a, v2b) -> VBool (v1a <> v2a || v1b <> v2b)
      | VSome v1, VSome v2 -> VBool (v1 <> v2)
      | VNone, VNone -> VBool false
      | _ -> VBool true)
  | Bop (Lt, e1, e2) -> (
    match go e1, go e2 with
    | VInt m, VInt n -> VBool (m < n)                     
    | VFloat m, VFloat n -> VBool (m < n)                 
    | VBool m, VBool n -> VBool ((not m) && n)            
    | VList lst1, VList lst2 -> VBool (lst1 < lst2)       
    | VSome v1, VSome v2 -> VBool (v1 < v2)               
    | VNone, VSome _ -> VBool true                        
    | VNone, VNone -> VBool false                         
    | _ -> failwith "Lt requires comparable types"
    )
  | Bop (Lte, e1, e2) -> (
      match go e1, go e2 with
      | VInt m, VInt n -> VBool (m <= n)                    
      | VFloat m, VFloat n -> VBool (m <= n)                
      | VBool m, VBool n -> VBool ((not n) || m)            
      | VList lst1, VList lst2 -> VBool (lst1 <= lst2)      
      | VSome v1, VSome v2 -> VBool (v1 <= v2)              
      | VNone, VSome _ -> VBool true                        
      | VNone, VNone -> VBool true                          
      | _ -> failwith "Lte requires comparable types"
  )
  | Bop (Gt, e1, e2) -> (
    match go e1, go e2 with
    | VInt m, VInt n -> VBool (m > n)
    | VFloat m, VFloat n -> VBool (m > n)
    | VBool m, VBool n -> VBool (m && not n)  
    | VPair (v1a, v1b), VPair (v2a, v2b) -> VBool ((v1a, v1b) > (v2a, v2b)) 
    | VSome v1, VSome v2 -> VBool (v1 > v2)
    | VNone, VSome _ -> VBool false
    | VNone, VNone -> VBool false
    | VList lst1, VList lst2 -> VBool (lst1 > lst2) 
    | _ -> failwith "Gt requires comparable types"
  )
  | Bop (Gte, e1, e2) -> (
    match go e1, go e2 with
    | VInt m, VInt n -> VBool (m >= n)                    
    | VFloat m, VFloat n -> VBool (m >= n)                
    | VBool m, VBool n -> VBool (m || not n)            
    | VList lst1, VList lst2 -> VBool (lst1 >= lst2)      
    | VSome v1, VSome v2 -> VBool (v1 >= v2)              
    | VSome _, VNone -> VBool true                        
    | VNone, VNone -> VBool true
    | VUnit, VUnit -> VBool true  
    | _ -> failwith "Gte requires comparable types"
)
  | Bop (And, e1, e2) -> (
      match go e1 with
      | VBool false -> VBool false
      | VBool true -> go e2
      | _ -> failwith ("Logical 'and' requires boolean operands")
      )
  | Bop (Or, e1, e2) -> (
        match go e1 with
        | VBool true -> VBool true
        | VBool false -> go e2
        | _ -> failwith ("Logical 'or' requires boolean operands")
  )
  | ESome e ->
    let v = eval_expr  env e in
    VSome v
  | OptMatch { matched; some_name; some_case; none_case } ->
    (match eval_expr env matched with
    | VSome v -> eval_expr (Env.add some_name v env) some_case
    | VNone -> eval_expr env none_case
    | _ -> failwith "Expected an option")
  | If (e1, e2, e3) -> (
        match go e1 with
        | VBool true -> go e2
        | VBool false -> go e3
        | _ -> failwith ("Condition in if-expression must be a boolean")
      )
  | Bop (Comma, e1, e2) -> 
      let v1 = go e1 in
      let v2 = go e2 in
      VPair (v1, v2)
  | Bop (Cons, e1, e2) -> 
      let v1 = go e1 in
      let v2 = go e2 in
      (match v2 with
      | VList lst -> VList (v1 :: lst)
      | _ -> failwith "Expected a list on the right-hand side of Cons")
  | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } -> (
      match go matched with
      | VList (vh :: vt) ->
          let env = Env.add hd_name vh env in
          let env = Env.add tl_name (VList vt) env in
          eval_expr env cons_case 
      | VList [] -> eval_expr env nil_case 
      | _ -> failwith "Expected a list"
  )
  | PairMatch { matched; fst_name; snd_name; case } -> (
      match go matched with
      | VPair (v1, v2) ->
          let env = Env.add fst_name v1 env in
          let env = Env.add snd_name v2 env in
          eval_expr env case 
      | _ -> failwith "Expected a pair"
  ) 
  | Bop (Concat, e1, e2) ->
    let v1 = go e1 in
    let v2 = go e2 in
    (match (v1, v2) with
    | (VList lst1, VList lst2) -> VList (lst1 @ lst2)
    | _ -> failwith "Both operands of Concat must be lists")     
  | Assert e1 ->
      (match go e1 with
      | (VBool true) -> VUnit
      | (VBool false) -> raise AssertFail
      | _ -> raise AssertFail)
  | Let { is_rec = false; name; value; body } ->
      let v1 = go value in
      let new_env = Env.add name v1 env in
      eval_expr new_env body 
  | Let { is_rec = true; name = f; value = e1; body = e2 } ->
        let closure = 
          (match eval_expr env e1  with
          | VClos { name = None; arg; body = closure_body; env = closure_env } ->
              VClos { name = Some f; arg; body = closure_body; env = closure_env }
          | VClos { name = Some _; _ } ->
            raise RecWithoutArg
          | _ -> failwith ("Expected a closure in recursive let binding"))
        in
        let updated_env = Env.add f closure env in
        eval_expr updated_env  e2 
  | Annot (e, _) ->
      eval_expr env e 
  in
  go expr

let type_check =
  let rec go ctxt = function
  | [] -> Some (Forall ([], TUnit))
  | {is_rec;name;value} :: ls ->
    match type_of ctxt (Let {is_rec;name;value; body = Var name}) with
    | Some ty -> (
      match ls with
      | [] -> Some ty
      | _ ->
        let ctxt = Env.add name ty ctxt in
        go ctxt ls
    )
    | None -> None
  in go Env.empty

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
