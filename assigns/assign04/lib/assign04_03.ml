open Assign04_02

type value = 
  | VNum of int
  | VBool of bool

let rec eval e =
  match e with
  | True -> VBool true
  | False -> VBool false
  | Num n -> VNum n
  | Or (e1, e2) ->
      let v1 = eval e1 in
      let v2 = eval e2 in
      (match v1, v2 with
       | VBool b1, VBool b2 -> VBool (b1 || b2)
       | _ -> failwith "Error")
  | Add (e1, e2) ->
      let v1 = eval e1 in
      let v2 = eval e2 in
      (match v1, v2 with
       | VNum n1, VNum n2 -> VNum (n1 + n2)
       | _ -> failwith "Error")
  | IfThenElse (e1, e2, e3) ->
      let v1 = eval e1 in
      (match v1 with
       | VBool true -> eval e2
       | VBool false -> eval e3
       | _ -> failwith "Error")


(*Sources:
https://ocaml.org/docs/basic-data-types
https://ocaml.org/manual/5.2/patterns.html lots of patterns 
 *)