%{
open Utils
%}

%token <int> NUM
%token <string> VAR
%token EOF

(* own code added tokens *)
%token IF THEN ELSE
%token LET IN
%token FUN ARROW
%token REC          (* NEW: Define REC token *)
%token MOD
%token TRUE FALSE UNIT
%token LPAREN RPAREN
%token PLUS MINUS TIMES DIV
%token LT LTE GT GTE EQ NEQ
%token AND OR

%start <Utils.prog> prog

%%

prog:
    expr EOF { $1 }

expr:
    IF expr THEN expr ELSE expr { If ($2, $4, $6) }      (* if *)
  | LET VAR EQ expr IN expr     { Let ($2, $4, $6) }     (* let *)
  | LET REC VAR EQ expr IN expr { LetRec ($3, $5, $7) }  (* NEW: let rec *)
  | FUN VAR ARROW expr          { Fun ($2, $4) }         (* fun *)
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
    LT  { Lt }         (* less than *)
  | LTE { Lte }        (* less than or equal *)
  | GT  { Gt }         (* greater than *)
  | GTE { Gte }        (* greater than or equal *)
  | EQ  { Eq }         (* equal *)
  | NEQ { Neq }        (* not equal *)

expr_add: 
    expr_add PLUS expr_mul      { Bop (Add, $1, $3) }       (* add *)
  | expr_add MINUS expr_mul     { Bop (Sub, $1, $3) }       (* subtraction *)
  | expr_mul                    { $1 }

expr_mul:
    expr_mul TIMES expr_app     { Bop (Mul, $1, $3) }       (* multiplication *) 
  | expr_mul DIV expr_app       { Bop (Div, $1, $3) }       (* division *)
  | expr_mul MOD expr_app       { Bop (Mod, $1, $3) }       (* modulus *)
  | expr_app                    { $1 }

expr_app: (* function application expressions *)
    expr_app expr_atomic        { App ($1, $2) }
  | expr_atomic                 { $1 }

expr_atomic: (* atomic expression *)
    UNIT                        { Unit }
  | TRUE                        { True }
  | FALSE                       { False }
  | NUM                         { Num $1 }
  | VAR                         { Var $1 }
  | LPAREN expr RPAREN          { $2 }
