open Utils

let rec type_of (e : Utils.expr) : ty option =
  match e with
  | Num _ -> Some TInt
  | Add (e1, e2) ->
      let t1 = type_of e1 in
      let t2 = type_of e2 in
      (match t1, t2 with
       | Some TInt, Some TInt -> Some TInt
       | _ -> None)
  | Lt (e1, e2) ->
      let t1 = type_of e1 in
      let t2 = type_of e2 in
      (match t1, t2 with
       | Some TInt, Some TInt -> Some TBool
       | _ -> None)
  | Ite (e1, e2, e3) ->
      let t1 = type_of e1 in
      let t2 = type_of e2 in
      let t3 = type_of e3 in
      (match t1, t2, t3 with
       | Some TBool, Some ty2, Some ty3 when ty2 = ty3 -> Some ty2
       | _ -> None)


(*syntax source: https://cs3110.github.io/textbook/chapters/interp/typecheck.html this for type checking          
besides this, same as always:recursion, pattern matching, option, adts, used the textbook and the ocaml manual*)
