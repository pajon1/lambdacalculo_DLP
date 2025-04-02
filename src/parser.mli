type token =
  | LAMBDA
  | TRUE
  | FALSE
  | IF
  | THEN
  | ELSE
  | SUCC
  | PRED
  | ISZERO
  | LET
  | LETREC
  | IN
  | CONCAT
  | BOOL
  | NAT
  | STRING
  | QUIT
  | HEAD
  | TAIL
  | ISNIL
  | CONS
  | NIL
  | LIST
  | LBRACKET
  | RBRACKET
  | LPAREN
  | RPAREN
  | DOT
  | EQ
  | COLON
  | ARROW
  | COMMA
  | LCBRACKET
  | RCBRACKET
  | AS
  | CASE
  | OF
  | LT
  | GT
  | BAR
  | EQGT
  | SEMICOLON
  | EOF
  | INTV of (int)
  | IDV of (string)
  | STRINGV of (string)

val s :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Lambda.command
