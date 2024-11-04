open Utils
open Parser.My_parser

let parse_input s = parse s 

(* Custom gensym function without mutable state *)
let gensym prefix counter =
  let unique_id = counter in
  (prefix ^ string_of_int unique_id, counter + 1)

(* Helper function to convert values to expressions for substitution *)
let value_to_expr = function
  | VNum n -> Num n
  | VBool b -> if b then True else False
  | VUnit -> Unit
  | VFun (x, e) -> Fun (x, e)

(* Substitution function: substitutes a value for a variable in an expression *)
let rec subst v x e counter =
  match e with
  | Var y -> if y = x then (v, counter) else (Var y, counter)
  | Fun (y, e') ->
      if y = x then (Fun (y, e'), counter)
      else
        let (y', new_counter) = gensym y counter in
        let (e'_subst, final_counter) = subst (Var y') y e' new_counter in
        (Fun (y', e'_subst), final_counter)
  | App (e1, e2) ->
      let (e1_subst, counter1) = subst v x e1 counter in
      let (e2_subst, counter2) = subst v x e2 counter1 in
      (App (e1_subst, e2_subst), counter2)
  | Let (y, e1, e2) ->
      if y = x then
        let (e1_subst, counter1) = subst v x e1 counter in
        (Let (y, e1_subst, e2), counter1)
      else
        let (y', new_counter) = gensym y counter in
        let (e1_subst, counter1) = subst v x e1 new_counter in
        let (e2_subst, final_counter) = subst v x e2 counter1 in
        (Let (y', e1_subst, e2_subst), final_counter)
  | If (e1, e2, e3) ->
      let (e1_subst, counter1) = subst v x e1 counter in
      let (e2_subst, counter2) = subst v x e2 counter1 in
      let (e3_subst, final_counter) = subst v x e3 counter2 in
      (If (e1_subst, e2_subst, e3_subst), final_counter)
  | Bop (op, e1, e2) ->
      let (e1_subst, counter1) = subst v x e1 counter in
      let (e2_subst, final_counter) = subst v x e2 counter1 in
      (Bop (op, e1_subst, e2_subst), final_counter)
  | Num _ | True | False | Unit -> (e, counter)

(* Evaluation function: interprets expressions based on big-step operational semantics *)
let rec eval expr =
  match expr with
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
       | Ok v -> 
           let (e2_subst, _) = subst (value_to_expr v) x e2 0 in
           eval e2_subst
       | Error e -> Error e)
  | App (e1, e2) ->
      (match eval e1, eval e2 with
       | Ok (VFun (x, e)), Ok v -> 
           let (e_subst, _) = subst (value_to_expr v) x e 0 in
           eval e_subst
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
       | Ok _, Error e -> Error e)  (* New case added here *)

(* Interpreter function: combines parsing and evaluation, handling parsing errors *)
let interp s =
  match parse_input s with
  | Some prog -> eval prog
  | None -> Error ParseFail
