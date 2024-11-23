{
open Par
}




let whitespace = [' ' '\t' '\n' '\r']+
let num = '-'? ['0'-'9']+
let var = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*


rule read =
 parse
 | whitespace { read lexbuf }
 | "let"      { LET }
 | "in"       { IN }
 | "rec"      { REC }
 | "if"       { IF }
 | "then"     { THEN }
 | "else"     { ELSE }
 | "fun"      { FUN }
 | "assert"   { ASSERT }
 | "true"     { TRUE }
 | "false"    { FALSE }
 | "()"       { UNIT }
 | "int"      { INT }
 | "bool"     { BOOL }
 | "unit"     { UNIT }
 | "+"        { PLUS }
 | "-"        { MINUS }
 | "*"        { TIMES }
 | "/"        { DIV }
 | "mod"      { MOD }
 | "<"        { LT }
 | "<="       { LTE }
 | ">"        { GT }
 | ">="       { GTE }
 | "="        { EQ }
 | "<>"       { NEQ }
 | "&&"       { AND }
 | "||"       { OR }
 | "->"       { ARROW }
 | "("        { LPAREN }
 | ")"        { RPAREN }
 | ":"        { COLON }
 | num        { NUM (int_of_string (Lexing.lexeme lexbuf)) }
 | var        { VAR (Lexing.lexeme lexbuf) }
 | eof        { EOF }
 | eof { EOF }
 | _          { failwith ("Unexpected character: " ^ Lexing.lexeme lexbuf) }





