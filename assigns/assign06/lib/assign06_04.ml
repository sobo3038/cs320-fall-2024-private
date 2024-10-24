open Utils

let rec eval (e : expr) : value =
  match e with
  | Num n -> VNum n
  | Add (e1, e2) ->
      let v1 = eval e1 in
      let v2 = eval e2 in
      (match v1, v2 with
       | VNum n1, VNum n2 -> VNum (n1 + n2)
       | _ -> VNum 0) 
  | Lt (e1, e2) ->
      let v1 = eval e1 in
      let v2 = eval e2 in
      (match v1, v2 with
       | VNum n1, VNum n2 -> VBool (n1 < n2)
       | _ -> VBool false) 
  | Ite (e1, e2, e3) ->
      let v1 = eval e1 in
      (match v1 with
       | VBool true -> eval e2
       | VBool false -> eval e3
       | _ -> eval e3) 

(*source syntax: https://cs3110.github.io/textbook/chapters/data/algebraic_data_types.html# for adt
   https://ocaml.org/manual/5.2/typedecl.html#type-annotations
   besides this, same as always:recursion, pattern matching, used the textbook and the ocaml manual*)