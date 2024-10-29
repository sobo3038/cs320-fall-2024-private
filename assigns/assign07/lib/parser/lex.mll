{
open Par
}

let whitespace = [' ' '\t' '\n' '\r']+
let num = '-'? ['0'-'9']+
let var = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*

rule read =
  parse
  | num { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "let" { LET }
  | "in" { IN }
  | "fun" { FUN }
  | "->" { ARROW }
  | "mod" { MOD }
  | "true" { TRUE }
  | "false" { FALSE }
  | "()" { UNIT }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { TIMES }
  | "/" { DIV }
  | "<=" { LTE }
  | "<" { LT }
  | ">=" { GTE }
  | ">" { GT }
  | "=" { EQ }
  | "<>" { NEQ }
  | "&&" { AND }
  | "||" { OR }
  | var { VAR (Lexing.lexeme lexbuf) }
  | whitespace { read lexbuf }
  | eof { EOF }
  | _ { failwith ("Unknown token: " ^ (Lexing.lexeme lexbuf)) }
