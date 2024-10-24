open Utils

let lex (s: string) : tok list option =
  let wordlist = split s in

  let rec processtokens tokenssofar remaining_words =
    match remaining_words with
    | [] -> Some tokenssofar
    | current_word :: next_words ->
        match tok_of_string_opt current_word with
        | Some token -> processtokens (tokenssofar @ [token]) next_words
        | None -> None
  in

  processtokens [] wordlist


(*syntax sources: https://ocaml.org/docs/options for options syntax
https://ocaml.org/manual/5.2/expr.html just needed basic general syntax examples *)