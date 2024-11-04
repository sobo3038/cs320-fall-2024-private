(* lib/parser/my_parser.ml *)

let parse s =
  try Some (Par.prog Lex.read (Lexing.from_string s))
  with _ -> None

(* Export the parse function *)
let parse_input = parse
