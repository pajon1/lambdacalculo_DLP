{
  open Parser;;
  exception Lexical_error;;
}

rule token = parse
    [' ' '\t' '\n' '\r']  { token lexbuf }
  | "lambda"    { LAMBDA }
  | "L"         { LAMBDA }
  | "true"      { TRUE }
  | "false"     { FALSE }
  | "if"        { IF }
  | "then"      { THEN }
  | "else"      { ELSE }
  | "succ"      { SUCC }
  | "pred"      { PRED }
  | "iszero"    { ISZERO }
  | "let"       { LET }
  | "letrec"    { LETREC }
  | "in"        { IN }
  | "concat"    { CONCAT }
  | "Bool"      { BOOL }
  | "Nat"       { NAT }
  | "String"    { STRING }
  | "head"      { HEAD }
  | "tail"      { TAIL }
  | "List"      { LIST }
  | "isnil"     { ISNIL }
  | "quit"      { QUIT }
  | "as"        { AS }
  | "case"      { CASE }
  | "of"        { OF }
  | "cons"      { CONS }
  | "nil"       { NIL }
  | "=>"        { EQGT }
  | '<'         { LT }
  | '>'         { GT }
  | '|'         { BAR }
  | '['         { LBRACKET }
  | ']'         { RBRACKET }
  | '('         { LPAREN }
  | ')'         { RPAREN }
  | '{'         { LCBRACKET }
  | '}'         { RCBRACKET }
  | '.'         { DOT }
  | ';'         { SEMICOLON }
  | '='         { EQ }
  | ':'         { COLON }
  | "->"        { ARROW }
  | ','         { COMMA }
  | ['0'-'9']+  { INTV (int_of_string (Lexing.lexeme lexbuf)) }
  | ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '_' '0'-'9']*
                { IDV (Lexing.lexeme lexbuf) }
  | '"'[^ '"' '\n']*'"'
      { let s = Lexing.lexeme lexbuf in
        STRINGV (String.sub s 1 (String.length s - 2)) }
  | eof         { EOF }
  | _           { raise Lexical_error }
