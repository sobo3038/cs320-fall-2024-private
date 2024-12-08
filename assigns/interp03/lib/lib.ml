open Utils
include My_parser
exception AssertFail
exception DivByZero
exception RecWithoutArg
exception CompareFunVals


let rec unify ty constraints =
  let rec free_vars ty =
    match ty with
    | TVar x -> [x]
    | TFun (t1, t2) | TPair (t1, t2) -> free_vars t1 @ free_vars t2
    | TList t | TOption t -> free_vars t
    | _ -> []
  in
  let rec occurs x ty =
    match ty with
    | TVar y -> x = y
    | TFun (t1, t2) | TPair (t1, t2) -> occurs x t1 || occurs x t2
    | TList t | TOption t -> occurs x t
    | _ -> false
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
    let rec dedup acc = function
      | [] -> List.rev acc
      | [x] -> List.rev (x :: acc)
      | x :: (y :: _ as rest) -> if cmp x y = 0 then dedup acc rest else dedup (x :: acc) rest
    in
    dedup [] sorted
  in
  match constraints with
  | [] -> Some (Forall (sort_uniq compare (free_vars ty), ty))
  | (t1, t2) :: rest when t1 = t2 -> unify ty rest
  | (TVar x, t) :: rest | (t, TVar x) :: rest ->
      if occurs x t then None
      else
        let subst = [(x, t)] in
        let updated_ty = apply_subst subst ty in
        let updated_constraints = apply_subst_to_constraints subst rest in
        unify updated_ty updated_constraints
  | (TFun (t1a, t1b), TFun (t2a, t2b)) :: rest ->
      unify ty ((t1a, t2a) :: (t1b, t2b) :: rest)
  | (TPair (t1a, t1b), TPair (t2a, t2b)) :: rest ->
      unify ty ((t1a, t2a) :: (t1b, t2b) :: rest)
  | (TList t1, TList t2) :: rest | (TOption t1, TOption t2) :: rest ->
      unify ty ((t1, t2) :: rest)
  | _ -> None
 
 
 










  let type_of (env : stc_env) (e : expr) : ty_scheme option =
    let rec free_vars ty =
      match ty with
      | TVar x -> [x]
      | TFun (a,b)|TPair(a,b)-> free_vars a @ free_vars b
      | TList t|TOption t->free_vars t
      | _->[]
    in
    let rec apply_subst s t =
      match t with
      | TVar x -> (try List.assoc x s with Not_found->t)
      | TFun(x,y)->TFun(apply_subst s x,apply_subst s y)
      | TPair(x,y)->TPair(apply_subst s x,apply_subst s y)
      | TList x->TList(apply_subst s x)
      | TOption x->TOption(apply_subst s x)
      | _->t
    in
    let instantiate (vars,ty) =
      let s = List.map (fun v->(v,TVar(gensym()))) vars in
      apply_subst s ty
    in
    let free_vars_in_env env =
      List.fold_left (fun acc (_,Forall(_,tt))->free_vars tt@acc) [] (Env.to_list env)
    in
    let rec infer en ex =
      match ex with
      | Unit->(TUnit,[])
      | True|False->(TBool,[])
      | Int _->(TInt,[])
      | Float _->(TFloat,[])
      | Var v->
        (match Env.find_opt v en with
         | Some(Forall(vars,ty))->(instantiate(vars,ty),[])
         | None->failwith("Unbound variable: "^v))
      | ENone->(TOption(TVar(gensym())),[])
      | ESome ee->
        let t,c=infer en ee in (TOption t,c)
      | Nil->(TList(TVar(gensym())),[])
      | OptMatch{matched;some_name;some_case;none_case} ->
        let tm,cm=infer en matched in
        let fe=TVar(gensym()) in
        let en_s=Env.add some_name (Forall([],fe)) en in
        let tsc,ccs=infer en_s some_case in
        let tnc,ccn=infer en none_case in
        (tsc,(tm,TOption fe)::(tsc,tnc)::cm@ccs@ccn)
      | Bop(op,e1,e2)->
        let t1,c1=infer en e1 in
        let t2,c2=infer en e2 in
        (match op with
         | Add|Sub|Mul|Div|Mod->(TInt,(t1,TInt)::(t2,TInt)::c1@c2)
         | AddF|SubF|MulF|DivF|PowF->(TFloat,(t1,TFloat)::(t2,TFloat)::c1@c2)
         | And|Or->(TBool,(t1,TBool)::(t2,TBool)::c1@c2)
         | Eq|Neq->
           let fr=TVar(gensym()) in (TBool,(t1,fr)::(t2,fr)::c1@c2)
         | Lt|Lte|Gt|Gte->
           let fr=TVar(gensym()) in (TBool,(t1,fr)::(t2,fr)::c1@c2)
         | Cons->
           let t1,c1=infer en e1 in
           let t2,c2=infer en e2 in
           (TList t1,(t2,TList t1)::c1@c2)
         | Concat->
           let t1,c1=infer en e1 in
           let t2,c2=infer en e2 in
           let fr=TVar(gensym()) in
           (TList fr,(t1,TList fr)::(t2,TList fr)::c1@c2)
         | Comma->
           let t1,c1=infer en e1 in
           let t2,c2=infer en e2 in
           (TPair(t1,t2),c1@c2))
      | If(e1,e2,e3)->
        let t1,c1=infer en e1 in
        let t2,c2=infer en e2 in
        let t3,c3=infer en e3 in
        (t2,(t1,TBool)::(t2,t3)::c1@c2@c3)
      | Fun(x,Some ty,b)->
        let en=Env.add x (Forall([],ty)) en in
        let tb,cb=infer en b in (TFun(ty,tb),cb)
      | Fun(arg,None,b) ->
        let fa=TVar(gensym()) in
        let en=Env.add arg (Forall([],fa)) en in
        let tb,cb=infer en b in (TFun(fa,tb),cb)
      | App(e1,e2) ->
        let tf,cf=infer en e1 in
        let ta,ca=infer en e2 in
        let fr=TVar(gensym()) in
        (fr,(tf,TFun(ta,fr))::cf@ca)
      | Let{is_rec=false;name;value;body} ->
        let tv,cv=infer en value in
        let en=Env.add name (Forall([],tv)) en in
        let tb,cb=infer en body in (tb,cv@cb)
      | Let{is_rec=true;name;value;body} ->
        let fr=TVar(gensym()) in
        let en_f=Env.add name (Forall([],fr)) en in
        let tv,cv=infer en_f value in
        let efv=free_vars_in_env en in
        let gt=Forall(List.filter(fun v->not(List.mem v efv))(free_vars tv),tv) in
        let en=Env.add name gt en in
        let tb,cb=infer en body in (tb,cv@cb)
      | Assert False->(TVar(gensym()),[])
      | Assert e->
        let t,c=infer en e in (TUnit,(t,TBool)::c)
      | Annot(e,ty)->
        let t,c=infer en e in (ty,(t,ty)::c)
      | PairMatch{matched;fst_name;snd_name;case} ->
        let tm,cm=infer en matched in
        let f1=TVar(gensym()) in
        let f2=TVar(gensym()) in
        let en_ex=Env.add fst_name (Forall([],f1))(Env.add snd_name (Forall([],f2)) en) in
        let tc,cc=infer en_ex case in (tc,(tm,TPair(f1,f2))::cm@cc)
      | ListMatch{matched;hd_name;tl_name;cons_case;nil_case} ->
        let tm,cm=infer en matched in
        let fe=TVar(gensym()) in
        let en_h=Env.add hd_name (Forall([],fe)) en in
        let en_t=Env.add tl_name (Forall([],TList fe)) en_h in
        let tcons,ccons=infer en_t cons_case in
        let tnil,cnil=infer en nil_case in
        (tnil,(tm,TList fe)::(tcons,tnil)::cm@ccons@cnil)
    in
    try
      let (ty,cstr)=infer env e in
      let u=unify ty cstr in
      match u with Some r->Some r|None->None
    with _->None
  







    






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
      | App (e1, e2) ->
        (match go e1 with
         | VClos {env=v_env; name=v_name; arg=v_arg; body=v_body} ->
           let v_env = match v_name with None -> v_env | Some nm -> Env.add nm (VClos {env=v_env;name=Some nm;arg=v_arg;body=v_body}) v_env in
           eval_expr (Env.add v_arg (go e2) v_env) v_body
         | _ -> failwith "impossible")
      | Bop (Add, a, b) ->
        (match go a, go b with VInt m, VInt n -> VInt (m+n) | _ -> failwith "impossible")
      | Bop (AddF, a, b) ->
        (match go a, go b with VFloat m, VFloat n -> VFloat (m+.n) | _ -> failwith "impossible")
      | Bop (Sub, a, b) ->
        (match go a, go b with VInt m, VInt n -> VInt (m-n) | _ -> failwith "impossible")
      | Bop (SubF, a, b) ->
        (match go a, go b with VFloat m, VFloat n -> VFloat (m-.n) | _ -> failwith "impossible")
      | Bop (Mul, a, b) ->
        (match go a, go b with VInt m, VInt n -> VInt (m*n) | _ -> failwith "impossible")
      | Bop (MulF, a, b) ->
        (match go a, go b with VFloat m, VFloat n -> VFloat (m*.n) | _ -> failwith "impossible")
      | Bop (Div, a, b) ->
        (match go a with
         | VInt m -> (match go b with VInt 0 -> raise DivByZero | VInt n -> VInt (m / n) | _ -> failwith "")
         | _ -> failwith "")
      | Bop (DivF, a, b) ->
        (match go a with
         | VFloat m -> (match go b with VFloat n -> VFloat (m /. n) | _ -> failwith "")
         | _ -> failwith "")
      | Bop (Mod, a, b) ->
        (match go a, go b with VInt m,VInt n when n<>0->VInt(m mod n)|VInt _,VInt 0->failwith"Division by zero in modulo operation"|_->failwith"Modulo operation requires two numbers")
      | Bop (PowF, a, b) ->
        (match go a, go b with VFloat m,VFloat n->VFloat(m**n)|_->failwith"impossible")
      | Bop (Eq, a, b) ->
        (match go a, go b with
         | VClos _, _ | _, VClos _ -> raise CompareFunVals
         | VInt m, VInt n -> VBool(m=n)
         | VFloat x,VFloat y->VBool(x=y)
         | VBool p,VBool q->VBool(p=q)
         | VUnit,VUnit->VBool true
         | VList l1,VList l2->VBool(l1=l2)
         | VPair(x1,y1),VPair(x2,y2)->VBool(x1=x2&&y1=y2)
         | VSome u,VSome v->VBool(u=v)
         | VNone,VNone->VBool true
         | _->VBool false)
      | Bop (Neq, a, b) ->
        (match go a,go b with
         | VClos _, _ | _, VClos _->raise CompareFunVals
         | VInt m,VInt n->VBool(m<>n)
         | VFloat x,VFloat y->VBool(x<>y)
         | VBool p,VBool q->VBool(p<>q)
         | VUnit,VUnit->VBool false
         | VList u,VList v->VBool(u<>v)
         | VPair(a1,b1),VPair(a2,b2)->VBool(a1<>a2||b1<>b2)
         | VSome w1,VSome w2->VBool(w1<>w2)
         | VNone,VNone->VBool false
         | _->VBool true)
      | Bop (Lt, a, b) ->
        (match go a, go b with
         | VInt m,VInt n->VBool(m<n)
         | VFloat m,VFloat n->VBool(m<n)
         | VBool x,VBool y->VBool((not x)&&y)
         | VList l1,VList l2->VBool(l1<l2)
         | VSome c1,VSome c2->VBool(c1<c2)
         | VNone,VSome _->VBool true
         | VNone,VNone->VBool false
         | _->failwith"Lt requires comparable types")
      | Bop (Lte, a, b) ->
        (match go a,go b with
         | VInt m,VInt n->VBool(m<=n)
         | VFloat m,VFloat n->VBool(m<=n)
         | VBool p,VBool q->VBool((not q)||p)
         | VList l1,VList l2->VBool(l1<=l2)
         | VSome w1,VSome w2->VBool(w1<=w2)
         | VNone,VSome _->VBool true
         | VNone,VNone->VBool true
         | _->failwith"Lte requires comparable types")
      | Bop (Gt, a, b) ->
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
      | Bop (Gte, a, b) ->
        (match go a, go b with
         | VInt m,VInt n->VBool(m>=n)
         | VFloat m,VFloat n->VBool(m>=n)
         | VBool p,VBool q->VBool(p||not q)
         | VList l1,VList l2->VBool(l1>=l2)
         | VSome v1,VSome v2->VBool(v1>=v2)
         | VSome _,VNone->VBool true
         | VNone,VNone->VBool true
         | VUnit,VUnit->VBool true
         | _->failwith"Gte requires comparable types")
      | Bop (And, a, b) ->
        (match go a with VBool false->VBool false|VBool true->go b|_->failwith"Logical 'and' requires boolean operands")
      | Bop (Or, a, b) ->
        (match go a with VBool true->VBool true|VBool false->go b|_->failwith"Logical 'or' requires boolean operands")
      | ESome e ->
        VSome (eval_expr env e)
      | OptMatch{matched;some_name;some_case;none_case} ->
        (match eval_expr env matched with
         | VSome v->eval_expr(Env.add some_name v env)some_case
         | VNone->eval_expr env none_case
         | _->failwith"Expected an option")
      | If(c,t,f) ->
        (match go c with VBool true->go t|VBool false->go f|_->failwith"Condition in if-expression must be a boolean")
      | Bop (Comma, a, b)->
        let va=go a and vb=go b in VPair(va,vb)
      | Bop (Cons,a,b)->
        let hd=go a and tl=go b in (match tl with VList l->VList(hd::l)|_->failwith"Expected a list on the right-hand side of Cons")
      | ListMatch{matched;hd_name;tl_name;cons_case;nil_case} ->
        (match go matched with
         | VList(h::t)->eval_expr(Env.add tl_name (VList t)(Env.add hd_name h env)) cons_case
         | VList []->eval_expr env nil_case
         | _->failwith"Expected a list")
      | PairMatch{matched;fst_name;snd_name;case} ->
        (match go matched with
         | VPair(x,y)->eval_expr(Env.add snd_name y (Env.add fst_name x env))case
         | _->failwith"Expected a pair")
      | Bop (Concat,a,b)->
        (match go a,go b with
         | VList l1,VList l2->VList(l1@l2)
         | _->failwith"Both operands of Concat must be lists")
      | Assert e1 ->
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
        eval_expr env e
    in go expr
  














let type_check prog =
 let rec go env = function
   | [] -> Some (Forall ([], TUnit))
   | { is_rec; name; value } :: rest ->
       (match type_of env (Let { is_rec; name; value; body = Var name }) with
       | Some ty -> go (Env.add name ty env) rest
       | None -> None)
 in
 go Env.empty prog


let eval prog =
 let rec nest = function
   | [] -> Unit
   | [{ is_rec; name; value }] -> Let { is_rec; name; value; body = Var name }
   | { is_rec; name; value } :: rest -> Let { is_rec; name; value; body = nest rest }
 in
 eval_expr Env.empty (nest prog)


let interp input =
 match parse input with
 | Some prog -> (match type_check prog with Some ty -> Ok (eval prog, ty) | None -> Error TypeError)
 | None -> Error ParseError



