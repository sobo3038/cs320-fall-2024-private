{
open Par
}

let whitespace = [' ' '\t' '\n' '\r']+
let num = '-'? ['0'-'9']+
let var = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*

rule read =
  parse
  | num { NUM (int_of_string (Lexing.lexeme lexbuf)) }

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

  (* Add type keywords here *)
  | "int" { INT }
  | "bool" { BOOL }
  | "unit" { UNIT }

  (* Symbols and operators *)
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

  (* Variables *)
  | var { VAR (Lexing.lexeme lexbuf) }

  (* Whitespace *)
  | whitespace { read lexbuf }

  (* End of file *)
  | eof { EOF }
