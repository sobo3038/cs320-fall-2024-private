%{
open Utils
%}

%token <int> NUM
%token <string> VAR
%token EOF
%token LET
%token IN
%token REC
%token EQ
%token COLON
%token IF
%token THEN
%token ELSE
%token FUN
%token ARROW
%token ASSERT
%token PLUS
%token MINUS
%token TIMES
%token DIV
%token MOD
%token TRUE 
%token FALSE
%token LPAREN
%token RPAREN
%token LT
%token LTE
%token GT
%token GTE
%token NEQ
%token AND
%token OR
%token INT
%token BOOL
%token UNIT
%right OR
%right AND
%left LT LTE GT GTE EQ NEQ
%left PLUS MINUS
%left TIMES DIV MOD

%start <Utils.prog> prog

%%

prog:
  declarations EOF { $1 }

declarations:
  | decl decl_list { $1 :: $2 }
  | /* empty */ { [] }

decl_list:
  | decl decl_list { $1 :: $2 }
  | /* empty */ { [] }

decl:
  | LET VAR parameters_opt COLON typ EQ expr
    { { is_rec = false; name = $2; args = $3; ty = $5; value = $7 } }
  | LET REC VAR parameters_opt COLON typ EQ expr
    { { is_rec = true; name = $3; args = $4; ty = $6; value = $8 } }

parameters_opt:
  | LPAREN VAR COLON typ RPAREN parameters_opt { ($2, $4) :: $6 }
  | /* empty */ { [] }

typ:
  | INT { IntTy }
  | BOOL { BoolTy }
  | UNIT { UnitTy }
  | typ ARROW typ { FunTy($1, $3) }
  | LPAREN typ RPAREN { $2 }

expr:
  | LET VAR parameters_opt COLON typ EQ expr IN expr
    { SLet { is_rec = false; name = $2; args = $3; ty = $5; value = $7; body = $9 } }
  | LET REC VAR parameters_opt COLON typ EQ expr IN expr
    { SLet { is_rec = true; name = $3; args = $4; ty = $6; value = $8; body = $10 } }
  | IF expr THEN expr ELSE expr
    { SIf($2, $4, $6) }
  | ASSERT expr
    { SAssert($2) }
  | FUN parameter ARROW expr
    { SFun { arg = $2; args = []; body = $4 } }
  | binary_expr { $1 }

binary_expr:
  | binary_expr OR logical_expr { SBop(Or, $1, $3) }
  | logical_expr { $1 }

logical_expr:
  | logical_expr AND comparison_expr { SBop(And, $1, $3) }
  | comparison_expr { $1 }

comparison_expr:
  | comparison_expr relational_op additive_expr { SBop($2, $1, $3) }
  | additive_expr { $1 }

relational_op:
  | LT { Lt }
  | LTE { Lte }
  | GT { Gt }
  | GTE { Gte }
  | EQ { Eq }
  | NEQ { Neq }

additive_expr:
  | additive_expr PLUS multiplicative_expr { SBop(Add, $1, $3) }
  | additive_expr MINUS multiplicative_expr { SBop(Sub, $1, $3) }
  | multiplicative_expr { $1 }

multiplicative_expr:
  | multiplicative_expr TIMES primary_expr { SBop(Mul, $1, $3) }
  | multiplicative_expr DIV primary_expr { SBop(Div, $1, $3) }
  | multiplicative_expr MOD primary_expr { SBop(Mod, $1, $3) }
  | primary_expr { $1 }

primary_expr:
  | UNIT { SUnit }
  | TRUE { STrue }
  | FALSE { SFalse }
  | NUM { SNum($1) }
  | VAR { SVar($1) }
  | LPAREN expr RPAREN { $2 }

parameter:
  | LPAREN VAR COLON typ RPAREN { ($2, $4) }
