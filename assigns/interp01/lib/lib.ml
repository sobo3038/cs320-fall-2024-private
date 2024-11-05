open Utils

(* Directly call My_parser.parse without opening the module *)
let parse s = My_parser.parse s

(* Helper function to convert a value into an expression for substitution *)
let value_to_expr = function
  | VNum n -> Num n
  | VBool b -> if b then True else False
  | VUnit -> Unit
  | VFun (x, e) -> Fun (x, e)

(* Substitution function: substitutes a value for a variable in an expression *)
let rec subst v x e =
  match e with
  | Var y -> if y = x then v else Var y
  | Fun (y, e') ->
      if y = x then Fun (y, e')
      else
        let y' = x ^ "'"
        and e'_subst = subst v y e' in
        Fun (y', subst (Var y') y e'_subst)
  | App (e1, e2) -> App (subst v x e1, subst v x e2)
  | Let (y, e1, e2) ->
      if y = x then Let (y, subst v x e1, e2)
      else Let (y, subst v x e1, subst v x e2)
  | If (e1, e2, e3) -> If (subst v x e1, subst v x e2, subst v x e3)
  | Bop (op, e1, e2) -> Bop (op, subst v x e1, subst v x e2)
  | Num _ | True | False | Unit -> e

(* Evaluation function: interprets expressions based on big-step operational semantics *)
let rec eval = function
  | Num n -> Ok (VNum n)
  | True -> Ok (VBool true)
  | False -> Ok (VBool false)
  | Unit -> Ok VUnit
  | Var x -> Error (UnknownVar x)
  | Fun (x, e) -> Ok (VFun (x, e))
  | If (e1, e2, e3) ->
      (match eval e1 with
       | Ok (VBool true) -> eval e2
       | Ok (VBool false) -> eval e3
       | _ -> Error InvalidIfCond)
  | Let (x, e1, e2) ->
      (match eval e1 with
       | Ok v -> eval (subst (value_to_expr v) x e2)
       | Error e -> Error e)
  | App (e1, e2) ->
      (match eval e1, eval e2 with
       | Ok (VFun (x, e)), Ok v -> eval (subst (value_to_expr v) x e)
       | Ok _, _ -> Error InvalidApp
       | Error e, _ -> Error e)
  | Bop (op, e1, e2) ->
      let bin_op op v1 v2 = 
        match op, v1, v2 with
        | Add, VNum n1, VNum n2 -> Ok (VNum (n1 + n2))
        | Sub, VNum n1, VNum n2 -> Ok (VNum (n1 - n2))
        | Mul, VNum n1, VNum n2 -> Ok (VNum (n1 * n2))
        | Div, VNum n1, VNum n2 -> if n2 = 0 then Error DivByZero else Ok (VNum (n1 / n2))
        | Mod, VNum n1, VNum n2 -> if n2 = 0 then Error DivByZero else Ok (VNum (n1 mod n2))
        | Lt, VNum n1, VNum n2 -> Ok (VBool (n1 < n2))
        | Lte, VNum n1, VNum n2 -> Ok (VBool (n1 <= n2))
        | Gt, VNum n1, VNum n2 -> Ok (VBool (n1 > n2))
        | Gte, VNum n1, VNum n2 -> Ok (VBool (n1 >= n2))
        | Eq, v1, v2 -> Ok (VBool (v1 = v2))
        | Neq, v1, v2 -> Ok (VBool (v1 <> v2))
        | And, VBool b1, VBool b2 -> Ok (VBool (b1 && b2))
        | Or, VBool b1, VBool b2 -> Ok (VBool (b1 || b2))
        | _ -> Error (InvalidArgs op)
      in
      (match eval e1, eval e2 with
       | Ok v1, Ok v2 -> bin_op op v1 v2
       | Error e, _ -> Error e
       | Ok _, Error e -> Error e)

(* Interpreter function: combines parsing and evaluation, handling parsing errors *)
let interp s =
  match parse s with
  | Some prog -> eval prog
  | None -> Error ParseFail
