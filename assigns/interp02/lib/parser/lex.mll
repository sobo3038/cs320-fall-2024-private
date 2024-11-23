{
open Par
}

let whitespace = [' ' '\t' '\n' '\r']+
let num = '-'? ['0'-'9']+
let var = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*

rule read =
  parse
  | whitespace { read lexbuf } (* Ignore whitespace *)

  (* Keywords *)
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "let" { LET }
  | "in" { IN }
  | "fun" { FUN }
  | "rec" { REC }
  | "true" { TRUE }
  | "false" { FALSE }
  | "()" { UNIT }
  | "assert" { ASSERT }

  (* Types *)
  | "int" { INT }
  | "bool" { BOOL }
  | "unit" { UNIT }

  (* Operators and symbols *)
  | "->" { ARROW }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | ":" { COLON }
  | "=" { EQ }
  | "<>" { NEQ }
  | "<=" { LTE }
  | "<" { LT }
  | ">=" { GTE }
  | ">" { GT }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { TIMES }
  | "/" { DIV }
  | "mod" { MOD }
  | "&&" { AND }
  | "||" { OR }

  (* Numbers and variables *)
  | num { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  | var { VAR (Lexing.lexeme lexbuf) }

  (* End of file *)
  | eof { EOF }

  (* Default error case *)
  | _ { failwith ("Unexpected character: " ^ Lexing.lexeme lexbuf) }
