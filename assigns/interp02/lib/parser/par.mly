%{
open Utils
%}

%token EOF

%token <int> NUM
%token <string> VAR
%token LET IN REC EQ COLON
%token IF THEN ELSE
%token FUN ARROW
%token ASSERT
%token MOD
%token TRUE FALSE UNIT
%token LPAREN RPAREN
%token PLUS MINUS TIMES DIV
%token LT LTE GT GTE NEQ
%token AND OR
%token INT BOOL

%start <Utils.prog> prog

%left OR
%left AND
%left EQ NEQ
%left LT LTE GT GTE
%left PLUS MINUS
%left TIMES DIV MOD

%%

prog:
    toplet_list EOF { $1 }

toplet_list:
    toplet toplet_list { $1 :: $2 }
  | /* empty */ { [] }

toplet:
    LET VAR args_opt COLON ty EQ expr { { is_rec = false; name = $2; args = $3; ty = $5; value = $7 } }
  | LET REC VAR args_opt COLON ty EQ expr { { is_rec = true; name = $3; args = $4; ty = $6; value = $8 } }

args_opt:
    LPAREN VAR COLON ty RPAREN args_opt { ($2, $4) :: $6 }
  | /* empty */ { [] }

ty:
    INT { IntTy }
  | BOOL { BoolTy }
  | UNIT { UnitTy }
  | ty ARROW ty { FunTy ($1, $3) }
  | LPAREN ty RPAREN { $2 }

expr:
    LET VAR COLON ty EQ expr IN expr { SLet { is_rec = false; name = $2; args = []; ty = $4; value = $6; body = $8 } }
  | LET REC VAR args_opt COLON ty EQ expr IN expr { SLet { is_rec = true; name = $3; args = $4; ty = $6; value = $8; body = $10 } }
  | IF expr THEN expr ELSE expr { SIf ($2, $4, $6) }
  | ASSERT expr { SAssert ($2) }
  | FUN VAR COLON ty ARROW expr { SFun { arg = ($2, $4); args = []; body = $6 } }
  | expr_or { $1 }

expr_or:
    expr_or OR expr_and { SBop (Or, $1, $3) }
  | expr_and { $1 }

expr_and:
    expr_and AND expr_cmp { SBop (And, $1, $3) }
  | expr_cmp { $1 }

expr_cmp:
    expr_cmp relop expr_add { SBop ($2, $1, $3) }
  | expr_add { $1 }

relop:
    LT { Lt }
  | LTE { Lte }
  | GT { Gt }
  | GTE { Gte }
  | EQ { Eq }
  | NEQ { Neq }

expr_add:
    expr_add PLUS expr_mul { SBop (Add, $1, $3) }
  | expr_add MINUS expr_mul { SBop (Sub, $1, $3) }
  | expr_mul { $1 }

expr_mul:
    expr_mul TIMES expr_atomic { SBop (Mul, $1, $3) }
  | expr_mul DIV expr_atomic { SBop (Div, $1, $3) }
  | expr_mul MOD expr_atomic { SBop (Mod, $1, $3) }
  | expr_atomic { $1 }

expr_atomic:
    UNIT { SUnit }
  | TRUE { STrue }
  | FALSE { SFalse }
  | NUM { SNum $1 }
  | VAR { SVar $1 }
  | LPAREN expr RPAREN { $2 }
