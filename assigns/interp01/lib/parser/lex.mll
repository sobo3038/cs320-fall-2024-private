{
open Par
}

let whitespace = [' ' '\t' '\n' '\r']+
let num = '-'? ['0'-'9']+
let var = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*

rule read =
  parse
  | num { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  
  (* own code for operators, keywords/terms, etc. *)
  (* keywords *)
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "let" { LET }
  | "in" { IN }
  | "fun" { FUN }
  | "rec" { REC } (* NEW: Add "rec" keyword *)
  (* bool *)
  | "true" { TRUE }
  | "false" { FALSE }
  (* unit *)
  | "()" { UNIT }
  (* symbols *)
  | "->" { ARROW }
  | "(" { LPAREN }
  | ")" { RPAREN }
  (* operators *)
  | "mod" { MOD }
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
  (* logical operators *)
  | "&&" { AND }
  | "||" { OR }

  (* given *)
  | var { VAR (Lexing.lexeme lexbuf) }
  | whitespace { read lexbuf }
  | eof { EOF }
