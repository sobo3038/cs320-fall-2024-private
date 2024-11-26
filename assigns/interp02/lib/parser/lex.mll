{
open Par
}

let whitespace = [' ' '\t' '\n' '\r']+
let num = '-'? ['0'-'9']+
let var = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*

(*keywords/symbols*)
rule read = parse
(*let binding*)
| "let"    { LET }
| "rec"    { REC }
| "in"     { IN }

(*conditionals*)
| "if"     { IF }
| "then"   { THEN }
| "else"   { ELSE }

(*func def and bool*)
| "fun"    { FUN }
| "true"   { TRUE }
| "false"  { FALSE }
| "assert" { ASSERT }
| "()"     {UNIT}

(*math*)
| '+'      { ADD }
| '-'      { SUB }
| '*'      { MUL }
| '/'      { DIV }
| "mod"    { MOD }

(*paren/arrow*)
| '('      { LPAREN }
| ')'      { RPAREN }
| "->"     { ARROW }

(*comparison/logic*)
| '<'      { LT }
| "<="     { LTE }
| '>'      { GT }
| ">="     { GTE }
| '='      { EQ }
| "<>"     { NEQ }
| "&&"     { AND }
| "||"     { OR }

(*type*)
| ":"      { COLON }
| "int"    { INTTY }
| "bool"   { BOOLTY }
| "unit"   {UNITTY}

| num { NUM (int_of_string (Lexing.lexeme lexbuf)) }
| var { VAR (Lexing.lexeme lexbuf) }
| whitespace { read lexbuf }
| eof { EOF }