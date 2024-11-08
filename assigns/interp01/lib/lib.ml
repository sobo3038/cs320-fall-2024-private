open Utils

let parse (input: string) : prog option =
  My_parser.parse input


  let rec subst (v: value) (x: string) (e: expr) : expr =
    match e with
    | Num n -> Num n
    | Var y -> if x = y then
                 (match v with
                  | VNum n -> Num n
                  | VBool b -> if b then True else False
                  | VUnit -> Unit
                  | VFun (param, body) -> Fun (param, body))
               else Var y
    | Unit -> Unit
    | True -> True
    | False -> False
    | If (e1, e2, e3) -> If (subst v x e1, subst v x e2, subst v x e3)
    | Let (y, e1, e2) ->
        if x = y then
          Let (y, subst v x e1, e2)
        else
          Let (y, subst v x e1, subst v x e2)
    | Fun (param, body) ->
        if x = param then
          Fun (param, body)
        else
          let z = Stdlib320.gensym() in
          Fun (z, subst v x (subst (VFun (z, Var z)) param body))
    | App (e1, e2) -> App (subst v x e1, subst v x e2)
    | Bop (op, e1, e2) -> Bop (op, subst v x e1, subst v x e2)
  

  let rec eval (e: expr) : (value, error) result =
    match e with
    | Num n -> Ok (VNum n)
    | True -> Ok (VBool true)
    | False -> Ok (VBool false)
    | Unit -> Ok VUnit
    | Var x -> Error (UnknownVar x)
    | If (e1, e2, e3) ->
        (match eval e1 with
         | Ok (VBool true) -> eval e2
         | Ok (VBool false) -> eval e3
         | _ -> Error InvalidIfCond)
    | Let (x, e1, e2) ->
        (match eval e1 with
         | Ok v1 -> eval (subst v1 x e2)
         | Error e -> Error e)
    | Fun (param, body) -> Ok (VFun (param, body))
    | App (e1, e2) ->
        (match eval e1 with
         | Ok (VFun (param, body)) ->
             (match eval e2 with
              | Ok v2 -> eval (subst v2 param body)
              | Error e -> Error e)
         | Ok _ -> Error InvalidApp
         | Error e -> Error e)
    | Bop (op, e1, e2) -> eval_bop op e1 e2
  
  and eval_bop op e1 e2 =
    match op with
    | And ->
        (match eval e1 with
         | Ok (VBool false) -> Ok (VBool false)  
         | Ok (VBool true) -> eval e2
         | _ -> Error (InvalidArgs op))
    | Or ->
        (match eval e1 with
         | Ok (VBool true) -> Ok (VBool true)    
         | Ok (VBool false) -> eval e2
         | _ -> Error (InvalidArgs op))
    | _ ->
        match eval e1, eval e2 with
        | Ok (VNum n1), Ok (VNum n2) ->
            (match op with
             | Add -> Ok (VNum (n1 + n2))
             | Sub -> Ok (VNum (n1 - n2))
             | Mul -> Ok (VNum (n1 * n2))
             | Div -> if n2 = 0 then Error DivByZero else Ok (VNum (n1 / n2))
             | Mod -> if n2 = 0 then Error DivByZero else Ok (VNum (n1 mod n2))
             | Lt -> Ok (VBool (n1 < n2))
             | Lte -> Ok (VBool (n1 <= n2))
             | Gt -> Ok (VBool (n1 > n2))
             | Gte -> Ok (VBool (n1 >= n2))
             | Eq -> Ok (VBool (n1 = n2))
             | Neq -> Ok (VBool (n1 <> n2))
             | _ -> Error (InvalidArgs op))
        | Ok (VBool b1), Ok (VBool b2) ->
            (match op with
             | Eq -> Ok (VBool (b1 = b2))
             | Neq -> Ok (VBool (b1 <> b2))
             | _ -> Error (InvalidArgs op))
        | _ -> Error (InvalidArgs op)
  

let interp (input: string) : (value, error) result =
  match parse input with
  | Some prog -> eval prog
  | None -> Error ParseFail
