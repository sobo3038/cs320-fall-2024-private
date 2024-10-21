open Utils
let lex (s: string) : tok list option =
  let words = split s in
  let rec lex_aux acc = function
    | [] -> Some (List.rev acc)
    | word :: rest ->
        match tok_of_string_opt word with
        | Some tok -> lex_aux (tok :: acc) rest
        | None -> None
  in
  lex_aux [] words
