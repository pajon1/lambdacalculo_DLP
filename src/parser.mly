%{
  open Lambda;;
%}

%token LAMBDA
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE
%token SUCC
%token PRED
%token ISZERO
%token LET
%token LETREC
%token IN
%token CONCAT
%token BOOL
%token NAT
%token STRING
%token QUIT
%token HEAD
%token TAIL
%token ISNIL

%token CONS
%token NIL
%token LIST
%token LBRACKET
%token RBRACKET

%token LPAREN
%token RPAREN
%token DOT
%token EQ
%token COLON
%token ARROW
%token COMMA
%token LCBRACKET
%token RCBRACKET

%token AS
%token CASE
%token OF
%token LT
%token GT
%token BAR
%token EQGT
%token SEMICOLON

%token EOF

%token <int> INTV
%token <string> IDV
%token <string> STRINGV

%start s
%type <Lambda.command> s

%%

s :
    IDV EQ term EOF
      { Bind ($1, $3) }
  | IDV EQ ty EOF
      { BindType ($1, $3) }
  | term EOF
      { Eval $1 }
  | QUIT EOF
      { Quit }

term :
    appTerm
      { $1 }
  | IF term THEN term ELSE term
      { TmIf ($2, $4, $6) }
  | LAMBDA IDV COLON ty DOT term
      { TmAbs ($2, $4, $6) }
  | LET IDV EQ term IN term
      { TmLetIn ($2, $4, $6) }
  | LETREC IDV COLON ty EQ term IN term
      { TmLetIn ($2, TmFix (TmAbs ($2, $4, $6)), $8) }
  | CASE term OF case_list
      { TmCase ($2, $4) }

appTerm :
    appTerm atomicTerm
      { TmApp ($1, $2) }
  | SUCC atomicTerm
      { TmSucc $2 }
  | PRED atomicTerm
      { TmPred $2 }
  | ISZERO atomicTerm
      { TmIsZero $2 }
  | CONCAT atomicTerm atomicTerm
      { TmConcat ($2, $3) }
  | HEAD LBRACKET ty RBRACKET atomicTerm
      { TmHead ($3, $5) }
  | TAIL LBRACKET ty RBRACKET atomicTerm
      { TmTail ($3, $5) }
  | ISNIL LBRACKET ty RBRACKET atomicTerm
      { TmIsNil ($3, $5) }
  | proj
      { $1 }
  | atomicTerm
      { $1 }

proj :
    atomicTerm DOT INTV
      { TmProj ($1, $3) }
  | proj DOT INTV
      { TmProj ($1, $3) }
  | atomicTerm DOT IDV
      { TmRProj ($1, $3)}
  | proj DOT IDV
      { TmRProj ($1, $3) }

atomicTerm :
    LPAREN term RPAREN
      { $2 }
  | TRUE
      { TmTrue }
  | FALSE
      { TmFalse }
  | IDV
      { TmVar $1 }
  | INTV
      { let rec f = function
            0 -> TmZero
          | n -> TmSucc (f (n-1))
        in f $1 }
  | STRINGV
      { TmString $1 }
  | LCBRACKET tuple RCBRACKET
      { TmTuple($2) }
  | listExpr
      { $1 }
  | LCBRACKET record RCBRACKET
      { TmRecord($2) }
  | LT IDV EQ term GT AS ty
      { TmTag ($2, $4, $7) }

tuple:
    term
      { [$1] }
  | term COMMA tuple
      { $1 :: $3 }

listExpr :
    CONS LBRACKET ty RBRACKET atomicTerm atomicTerm
        { TmCons ($3, $5, $6) }
  | NIL LBRACKET ty RBRACKET
        { TmNil $3 }

case_list :
    case_branch
      { [$1] }
  | case_branch BAR case_list
      { $1 :: $3 }

case_branch :
    LT IDV EQ IDV GT EQGT term
      { ($2, $4, $7) }

ty :
    atomicTy
      { $1 }
  | atomicTy ARROW ty
      { TyArr ($1, $3) }

atomicTy :
    LPAREN ty RPAREN
      { $2 }
  | BOOL
      { TyBool }
  | NAT
      { TyNat }
  | STRING
      { TyString }
  | LIST LBRACKET ty RBRACKET
      { TyList $3 }
  | LT field_types GT
      { TyVariant $2 }
  | IDV
      { TyVar $1 }
  | LCBRACKET RCBRACKET
      { TyRecord [] }
  | LCBRACKET ty_record_type_fields RCBRACKET
      { TyRecord $2 }

record:
    IDV COLON term 
    	{[($1,$3)]}
  | IDV COLON term COMMA record
  	{ [($1, $3)] @ $5 }

ty_record_type_fields:
    IDV COLON ty
      { [($1,$3)] }
  | IDV COLON ty COMMA ty_record_type_fields
      { ($1,$3)::$5 }

field_types :
    field_type
      { [$1] }
  | field_type COMMA field_types
      { $1 :: $3 }

field_type :
    IDV COLON ty
      { ($1, $3) }

