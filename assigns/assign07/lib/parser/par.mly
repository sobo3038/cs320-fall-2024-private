%{
open Utils
%}

%token <int> NUM
%token <string> VAR
%token EOF
%token IF THEN ELSE LET IN FUN ARROW MOD TRUE FALSE UNIT LPAREN RPAREN
%token PLUS MINUS TIMES DIV LT LTE GT GTE EQ NEQ AND OR

%start <Utils.prog> prog

%%

prog:
    expr EOF { $1 }

expr:
    IF expr THEN expr ELSE expr { If ($2, $4, $6) }
  | LET VAR EQ expr IN expr     { Let ($2, $4, $6) }
  | FUN VAR ARROW expr          { Fun ($2, $4) }
  | expr_or                     { $1 }

expr_or:
    expr_or OR expr_and         { Bop (Or, $1, $3) }
  | expr_and                    { $1 }

expr_and:
    expr_and AND expr_rel       { Bop (And, $1, $3) }
  | expr_rel                    { $1 }

expr_rel:
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
