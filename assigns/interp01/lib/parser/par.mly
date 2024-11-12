%{
open Utils
%}

%token <int> NUM
%token <string> VAR
%token EOF

(* Own code added tokens *)
%token IF THEN ELSE
%token LET IN
%token FUN ARROW
%token REC          (* Define REC token *)
%token MOD
%token TRUE FALSE UNIT
%token LPAREN RPAREN
%token PLUS MINUS TIMES DIV
%token LT LTE GT GTE EQ NEQ
%token AND OR

%start <Utils.expr> prog  (* Change start rule type to expr *)

%%

prog:
    expr EOF { $1 }

expr:
    IF expr THEN expr ELSE expr { If ($2, $4, $6) }
  | LET VAR EQ expr IN expr     { Let ($2, $4, $6) }
  | LET REC VAR EQ expr IN expr { LetRec ($3, $5, $7) }  (* LetRec now part of expr *)
  | FUN VAR ARROW expr          { Fun ($2, $4) }
  | expr_or                     { $1 }

expr_or: (* or *)
    expr_or OR expr_and         { Bop (Or, $1, $3) }
  | expr_and                    { $1 }

expr_and: (* and *)
    expr_and AND expr_rel       { Bop (And, $1, $3) }
  | expr_rel                    { $1 }

expr_rel: (* relational expression *)
    expr_rel relop expr_add     { Bop ($2, $1, $3) }
  | expr_add                    { $1 }

relop:
    LT  { Lt }
  | LTE { Lte }
  | GT  { Gt }
  | GTE { Gte }
  | EQ  { Eq }
  | NEQ { Neq }

expr_add: 
    expr_add PLUS expr_mul      { Bop (Add, $1, $3) }
  | expr_add MINUS expr_mul     { Bop (Sub, $1, $3) }
  | expr_mul                    { $1 }

expr_mul:
    expr_mul TIMES expr_app     { Bop (Mul, $1, $3) }
  | expr_mul DIV expr_app       { Bop (Div, $1, $3) }
  | expr_mul MOD expr_app       { Bop (Mod, $1, $3) }
  | expr_app                    { $1 }

expr_app:
    expr_app expr_atomic        { App ($1, $2) }
  | expr_atomic                 { $1 }

expr_atomic:
    UNIT                        { Unit }
  | TRUE                        { True }
  | FALSE                       { False }
  | NUM                         { Num $1 }
  | VAR                         { Var $1 }
  | LPAREN expr RPAREN          { $2 }
