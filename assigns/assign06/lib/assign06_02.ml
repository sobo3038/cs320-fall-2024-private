open Utils

let parse (toks : tok list) : expr option =
  let rec parse_aux stack = function
    | [] -> 
        (match stack with
         | [x] -> Some x
         | _ -> None)
    | TNum n :: rest ->
        parse_aux (Num n :: stack) rest
    | TAdd :: rest ->
        (match stack with
         | e2 :: e1 :: rest_stack -> parse_aux (Add (e1, e2) :: rest_stack) rest
         | _ -> None)
    | TLt :: rest ->
        (match stack with
         | e2 :: e1 :: rest_stack -> parse_aux (Lt (e1, e2) :: rest_stack) rest
         | _ -> None)
    | TIte :: rest ->
        (match stack with
         | e3 :: e2 :: e1 :: rest_stack -> parse_aux (Ite (e1, e2, e3) :: rest_stack) rest
         | _ -> None)
  in
  parse_aux [] toks