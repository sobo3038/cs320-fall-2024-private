
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
  let rec go e =
    match e with
    | Unit -> VUnit
    | True -> VBool true
    | False -> VBool false
    | Int n -> VInt n
    | Float f -> VFloat f
    | ENone -> VNone
    | Nil -> VList []
    | Var x -> Env.find x env
    | Fun (x, _, b) -> VClos {name=None; arg=x; body=b; env}
    | App (e1,e2) ->
      (match go e1 with
       | VClos {env=v_env; name=v_name; arg=v_arg; body=v_body} ->
         let v_env = match v_name with None -> v_env | Some nm -> Env.add nm (VClos {env=v_env; name=Some nm; arg=v_arg; body=v_body}) v_env in
         eval_expr (Env.add v_arg (go e2) v_env) v_body
       | _ -> failwith "impossible")
    | Bop (Add,a,b) -> (match go a,go b with VInt m,VInt n->VInt(m+n)|_->failwith"impossible")
    | Bop (AddF,a,b)->(match go a,go b with VFloat m,VFloat n->VFloat(m+.n)|_->failwith"impossible")
    | Bop (Sub,a,b)->(match go a,go b with VInt m,VInt n->VInt(m-n)|_->failwith"impossible")
    | Bop (SubF,a,b)->(match go a,go b with VFloat m,VFloat n->VFloat(m-.n)|_->failwith"impossible")
    | Bop (Mul,a,b)->(match go a,go b with VInt m,VInt n->VInt(m*n)|_->failwith"impossible")
    | Bop (MulF,a,b)->(match go a,go b with VFloat m,VFloat n->VFloat(m*.n)|_->failwith"impossible")
    | Bop (Div,a,b)->
      (match go a with
       | VInt m -> (match go b with VInt 0->raise DivByZero|VInt n->VInt(m/n)|_->failwith"")
       | _->failwith"")
    | Bop (DivF,a,b)->
      (match go a with
       | VFloat m->(match go b with VFloat n->VFloat(m/.n)|_->failwith"")
       | _->failwith"")
    | Bop (Mod,a,b)->
      (match go a,go b with VInt m,VInt n when n<>0->VInt(m mod n)|VInt _,VInt 0->failwith"Division by zero in modulo operation"|_->failwith"Modulo operation requires two numbers")
    | Bop (PowF,a,b)->
      (match go a,go b with VFloat m,VFloat n->VFloat(m**n)|_->failwith"impossible")
    | Bop (Eq,a,b)->
      (match go a,go b with
       | VClos _,_ | _,VClos _->raise CompareFunVals
       | VInt m,VInt n->VBool(m=n)
       | VFloat x,VFloat y->VBool(x=y)
       | VBool p,VBool q->VBool(p=q)
       | VUnit,VUnit->VBool true
       | VList l1,VList l2->VBool(l1=l2)
       | VPair(x1,y1),VPair(x2,y2)->VBool(x1=x2&&y1=y2)
       | VSome u,VSome v->VBool(u=v)
       | VNone,VNone->VBool true
       | _->VBool false)
    | Bop (Neq,a,b)->
      (match go a,go b with
       | VClos _,_|_,VClos _->raise CompareFunVals
       | VInt m,VInt n->VBool(m<>n)
       | VFloat x,VFloat y->VBool(x<>y)
       | VBool p,VBool q->VBool(p<>q)
       | VUnit,VUnit->VBool false
       | VList u,VList v->VBool(u<>v)
       | VPair(a1,b1),VPair(a2,b2)->VBool(a1<>a2||b1<>b2)
       | VSome w1,VSome w2->VBool(w1<>w2)
       | VNone,VNone->VBool false
       | _->VBool true)
    | Bop (Lt,a,b)->
      (match go a,go b with
       | VInt m,VInt n->VBool(m<n)
       | VFloat m,VFloat n->VBool(m<n)
       | VBool x,VBool y->VBool((not x)&&y)
       | VList l1,VList l2->VBool(l1<l2)
       | VSome c1,VSome c2->VBool(c1<c2)
       | VNone,VSome _->VBool true
       | VNone,VNone->VBool false
       | _->failwith"Lt requires comparable types")
    | Bop (Lte,a,b)->
      (match go a,go b with
       | VInt m,VInt n->VBool(m<=n)
       | VFloat m,VFloat n->VBool(m<=n)
       | VBool p,VBool q->VBool((not q)||p)
       | VList l1,VList l2->VBool(l1<=l2)
       | VSome w1,VSome w2->VBool(w1<=w2)
       | VNone,VSome _->VBool true
       | VNone,VNone->VBool true
       | _->failwith"Lte requires comparable types")
    | Bop (Gt,a,b)->
      (match go a, go b with
       | VInt m,VInt n->VBool(m>n)
       | VFloat m,VFloat n->VBool(m>n)
       | VBool p,VBool q->VBool(p&&not q)
       | VPair(x1,y1),VPair(x2,y2)->VBool((x1,y1)>(x2,y2))
       | VSome c1,VSome c2->VBool(c1>c2)
       | VNone,VSome _->VBool false
       | VNone,VNone->VBool false
       | VList la,VList lb->VBool(la>lb)
       | _->failwith"Gt requires comparable types")
    | Bop (Gte,a,b)->
      (match go a,go b with
       | VInt m,VInt n->VBool(m>=n)
       | VFloat m,VFloat n->VBool(m>=n)
       | VBool p,VBool q->VBool(p||not q)
       | VList l1,VList l2->VBool(l1>=l2)
       | VSome v1,VSome v2->VBool(v1>=v2)
       | VSome _,VNone->VBool true
       | VNone,VNone->VBool true
       | VUnit,VUnit->VBool true
       | _->failwith"Gte requires comparable types")
    | Bop (And,a,b)->
      (match go a with VBool false->VBool false|VBool true->go b|_->failwith"Logical 'and' requires boolean operands")
    | Bop (Or,a,b)->
      (match go a with VBool true->VBool true|VBool false->go b|_->failwith"Logical 'or' requires boolean operands")
    | ESome e ->
      VSome (eval_expr env e)
    | OptMatch{matched;some_name;some_case;none_case} ->
      (match eval_expr env matched with
       | VSome v->eval_expr(Env.add some_name v env)some_case
       | VNone->eval_expr env none_case
       | _->failwith"Expected an option")
    | If(c,t,f)->
      (match go c with VBool true->go t|VBool false->go f|_->failwith"Condition in if-expression must be a boolean")
    | Bop (Comma,a,b)->
      let va=go a in
      let vb=go b in
      VPair(va,vb)
    | Bop (Cons,a,b)->
      let hd=go a in
      let tl=go b in
      (match tl with VList lst->VList(hd::lst)|_->failwith"Expected a list on the right-hand side of Cons")
    | ListMatch{matched;hd_name;tl_name;cons_case;nil_case} ->
      (match go matched with
       | VList(h::t)->
         eval_expr (Env.add tl_name (VList t)(Env.add hd_name h env)) cons_case
       | VList []->eval_expr env nil_case
       | _->failwith"Expected a list")
    | PairMatch{matched;fst_name;snd_name;case} ->
      (match go matched with
       | VPair(x,y)->
         eval_expr (Env.add snd_name y (Env.add fst_name x env)) case
       | _->failwith"Expected a pair")
    | Bop (Concat,a,b)->
      (match go a,go b with
       | VList l1,VList l2->VList(l1@l2)
       | _->failwith"Both operands of Concat must be lists")
    | Assert e1->
      (match go e1 with VBool true->VUnit|VBool false->raise AssertFail|_->raise AssertFail)
    | Let{is_rec=false;name;value;body} ->
      eval_expr (Env.add name (go value) env) body
    | Let{is_rec=true;name=f;value=v;body} ->
      let c=eval_expr env v in
      (match c with
       | VClos{name=None;arg;body=cb;env=ce} ->
         eval_expr(Env.add f (VClos{name=Some f;arg;body=cb;env=ce}) env) body
       | VClos{name=Some _;_}->raise RecWithoutArg
       |_->failwith"Expected a closure in recursive let binding")
    | Annot(e, _) ->
      go e
  in go expr












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