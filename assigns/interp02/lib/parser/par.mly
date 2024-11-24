%{
open Utils
%}

%token <int> NUM
%token <string> VAR
%token EOF

%token INTTY "int"
%token BOOLTY "bool"
%token UNITTY "unit"

%token ASSERT "assert"
%token FUN "fun"
%token LET "let"
%token REC "rec"

%token ADD "+"
%token MUL "*"
%token SUB "-"
%token DIV "/"
%token MOD "mod"

%token LT "<"
%token LTE "<="
%token GT ">"
%token GTE ">="
%token NEQ "<>"
%token ARROW "->"
%token LPAREN "("
%token RPAREN ")"
%token EQ "="
%token AND "&&"
%token OR "||"
%token COLON ":"
%token UNIT "()"

%token IN "in"
%token IF "if"
%token THEN "then"
%token ELSE "else"

%token TRUE "true"
%token FALSE "false"

%right OR
%right AND
%left LT LTE GT GTE EQ NEQ
%left ADD SUB
%left MUL DIV MOD

%start <Utils.prog> prog

%%

prog:
  | binding_list EOF { $1 }

binding_list:
  | single_binding binding_list { $1 :: $2 }
  | single_binding { [$1] }

single_binding:
  | "let" VAR parameters COLON type_annotation EQ expression
      { { is_rec = false; name = $2; args = $3; ty = $5; value = $7 } }
  | "let" "rec" VAR parameter parameters COLON type_annotation EQ expression
      { { is_rec = true; name = $3; args = $4 :: $5; ty = $7; value = $9 } }

parameters:
  | parameter parameters { $1 :: $2 }
  | { [] }

parameter:
  | LPAREN VAR COLON type_annotation RPAREN { ($2, $4) }

type_annotation:
  | INTTY { IntTy }
  | BOOLTY { BoolTy }
  | UNITTY { UnitTy }
  | type_annotation ARROW type_annotation { FunTy($1, $3) }
  | LPAREN type_annotation RPAREN { $2 }

expression:
  | "let" VAR parameters COLON type_annotation EQ expression IN expression
      { SLet { is_rec = false; name = $2; args = $3; ty = $5; value = $7; body = $9 } }
  | "let" "rec" VAR parameter parameters COLON type_annotation EQ expression IN expression
      { SLet { is_rec = true; name = $3; args = $4 :: $5; ty = $7; value = $9; body = $11 } }
  | "if" expression THEN expression ELSE expression
      { SIf($2, $4, $6) }
  | "fun" parameter parameters ARROW expression
      { SFun { arg = $2; args = $3; body = $5 } }
  | binary_expression { $1 }

%inline binary_op:
  | ADD { Add }
  | SUB { Sub }
  | MUL { Mul }
  | DIV { Div }
  | MOD { Mod }
  | LT { Lt }
  | LTE { Lte }
  | GT { Gt }
  | GTE { Gte }
  | EQ { Eq }
  | NEQ { Neq }
  | AND { And }
  | OR { Or }

binary_expression:
  | binary_expression binary_op binary_expression { SBop($2, $1, $3) }
  | "assert" unary_expression { SAssert $2 }
  | unary_expression application_arguments { List.fold_left (fun acc arg -> SApp(acc, arg)) $1 $2 }

application_arguments:
  | unary_expression application_arguments { $1 :: $2 }
  | { [] }

unary_expression:
  | UNIT { SUnit }
  | TRUE { STrue }
  | FALSE { SFalse }
  | NUM { SNum $1 }
  | VAR { SVar $1 }
  | LPAREN expression RPAREN { $2 }
