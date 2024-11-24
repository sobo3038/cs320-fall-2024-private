{
open Par
}

let whitespace = [' ' '\t' '\n' '\r']+
let num = '-'? ['0'-'9']+
let var = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*

rule read = parse
| "let"    { LET }
| "rec"    { REC }
| "in"     { IN }
| "if"     { IF }
| "then"   { THEN }
| "else"   { ELSE }
| "fun"    { FUN }
| "true"   { TRUE }
| "false"  { FALSE }
| "assert" { ASSERT }
| "()"     {UNIT}
| '+'      { ADD }
| '-'      { SUB }
| '*'      { MUL }
| '/'      { DIV }
| "mod"    { MOD }
| '('      { LPAREN }
| ')'      { RPAREN }
| "->"     { ARROW }
| '<'      { LT }
| "<="     { LTE }
| '>'      { GT }
| ">="     { GTE }
| '='      { EQ }
| "<>"     { NEQ }
| "&&"     { AND }
| "||"     { OR }
| ":"      { COLON }
| "int"    { INTTY }
| "bool"   { BOOLTY }
| "unit"   {UNITTY}
| num { NUM (int_of_string (Lexing.lexeme lexbuf)) }
| var { VAR (Lexing.lexeme lexbuf) }
| whitespace { read lexbuf }
| eof { EOF }