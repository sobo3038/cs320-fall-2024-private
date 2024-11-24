%{
open Utils
%}

%token <int> NUM
%token <string> VAR
%token EOF
%token LET
%token REC
%token IN
%token EQ
%token COLON
%token IF
%token THEN
%token ELSE
%token FUN
%token ARROW
%token ASSERT
%token ADD
%token SUB
%token MUL
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
%token EQEQ
%token NEQ
%token AND
%token OR
%token INTTY
%token BOOLTY
%token UNITTY
%token UNIT
%right OR
%right AND
%left LT LTE GT GTE EQEQ NEQ
%left ADD SUB
%left MUL DIV MOD

%start <Utils.prog> prog

%%

prog:
  | declarations EOF { $1 }

declarations:
  | declaration declarations { $1 :: $2 }
  | /* empty */ { [] }

declaration:
  | LET VAR parameters_opt COLON type_spec EQ expression
    { { is_rec = false; name = $2; args = $3; ty = $5; value = $7 } }
  | LET REC VAR parameters_opt COLON type_spec EQ expression
    { { is_rec = true; name = $3; args = $4; ty = $6; value = $8 } }

parameters_opt:
  | LPAREN VAR COLON type_spec RPAREN parameters_opt { ($2, $4) :: $6 }
  | /* empty */ { [] }

type_spec:
  | INTTY { IntTy }
  | BOOLTY { BoolTy }
  | UNITTY { UnitTy }
  | type_spec ARROW type_spec { FunTy($1, $3) }
  | LPAREN type_spec RPAREN { $2 }

expression:
  | LET VAR parameters_opt COLON type_spec EQ expression IN expression
    { SLet { is_rec = false; name = $2; args = $3; ty = $5; value = $7; body = $9 } }
  | LET REC VAR parameters_opt COLON type_spec EQ expression IN expression
    { SLet { is_rec = true; name = $3; args = $4; ty = $6; value = $8; body = $10 } }
  | IF expression THEN expression ELSE expression
    { SIf($2, $4, $6) }
  | ASSERT expression
    { SAssert($2) }
  | FUN single_arg parameters ARROW expression
    { SFun { arg = $2; args = $3; body = $5 } }
  | binary_expression { $1 }

single_arg:
  | LPAREN VAR COLON type_spec RPAREN { ($2, $4) }

parameters:
  | single_arg parameters { $1 :: $2 }
  | /* empty */ { [] }

binary_expression:
  | binary_expression OR logical_expression { SBop(Or, $1, $3) }
  | logical_expression { $1 }

logical_expression:
  | logical_expression AND comparison_expression { SBop(And, $1, $3) }
  | comparison_expression { $1 }

comparison_expression:
  | comparison_expression comparison_operator additive_expression
    { SBop($2, $1, $3) }
  | additive_expression { $1 }

comparison_operator:
  | LT { Lt }
  | LTE { Lte }
  | GT { Gt }
  | GTE { Gte }
  | EQEQ { Eq }
  | NEQ { Neq }

additive_expression:
  | additive_expression ADD multiplicative_expression { SBop(Add, $1, $3) }
  | additive_expression SUB multiplicative_expression { SBop(Sub, $1, $3) }
  | multiplicative_expression { $1 }

multiplicative_expression:
  | multiplicative_expression MUL primary_expression { SBop(Mul, $1, $3) }
  | multiplicative_expression DIV primary_expression { SBop(Div, $1, $3) }
  | multiplicative_expression MOD primary_expression { SBop(Mod, $1, $3) }
  | primary_expression { $1 }

primary_expression:
  | UNIT { SUnit }
  | TRUE { STrue }
  | FALSE { SFalse }
  | NUM { SNum($1) }
  | VAR { SVar($1) }
  | LPAREN expression RPAREN { $2 }
