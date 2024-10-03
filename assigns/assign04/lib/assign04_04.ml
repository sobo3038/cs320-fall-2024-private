type ident = string

type expr' = 
  | True
  | False
  | Num of int
  | Var of ident
  | Let of ident * expr' * expr'
  | Add of expr' * expr'
  | Or of expr' * expr'
  | IfThenElse of expr' * expr' * expr'

type ty' = 
  | Int
  | Bool

type context = (ident * ty') list

let rec type_of' gamma e =
  match e with
  | True -> Some Bool
  | False -> Some Bool
  | Num _ -> Some Int
  | Var x -> List.assoc_opt x gamma
  | Add (e1, e2) ->
      (match type_of' gamma e1, type_of' gamma e2 with
       | Some Int, Some Int -> Some Int
       | _ -> None)
  | Or (e1, e2) ->
      (match type_of' gamma e1, type_of' gamma e2 with
       | Some Bool, Some Bool -> Some Bool
       | _ -> None)
  | IfThenElse (e1, e2, e3) ->
      (match type_of' gamma e1, type_of' gamma e2, type_of' gamma e3 with
       | Some Bool, Some t2, Some t3 when t2 = t3 -> Some t2
       | _ -> None)
  | Let (x, e1, e2) ->
      (match type_of' gamma e1 with
       | Some t1 -> type_of' ((x, t1) :: gamma) e2
       | None -> None)


(*Sources:
  Some https://cs3110.github.io/textbook/chapters/data/options.html 
  and https://ocaml.org/manual/5.2/coreexamples.html#s:optional-arguments
  https://ocaml.org/manual/5.2/api/List.html List.assoc_opt
  https://ocaml.org/manual/5.2/patterns.html#s:pattern-matching-arrays
   *)