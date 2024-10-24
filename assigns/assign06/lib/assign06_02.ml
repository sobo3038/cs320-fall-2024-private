open Utils

let parse (toks : tok list) : expr option =
  let rec process_stack stack tokens =
    match tokens, stack with
    | [], [x] -> Some x
    | [], _ -> None
    | TNum n :: rest, _ -> process_stack (Num n :: stack) rest
    | TAdd :: rest, e2 :: e1 :: rest_stack ->
        process_stack (Add (e1, e2) :: rest_stack) rest
    | TAdd :: _, _ -> None
    | TLt :: rest, e2 :: e1 :: rest_stack ->
        process_stack (Lt (e1, e2) :: rest_stack) rest
    | TLt :: _, _ -> None
    | TIte :: rest, e3 :: e2 :: e1 :: rest_stack ->
        process_stack (Ite (e1, e2, e3) :: rest_stack) rest
    | TIte :: _, _ -> None
  in
  process_stack [] toks

(*syntax source: used the same as always: recursion, pattern matching
https://ocaml.org/docs/options  syntax for options in te pattern matching 
https://ocaml.org/manual/5.2/modules.html
parsing helphttps://cs3110.github.io/textbook/chapters/interp/parsing.html *)
