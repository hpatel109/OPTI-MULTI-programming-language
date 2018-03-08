type token =
  | SEMI
  | LPAREN
  | RPAREN
  | LBRACE
  | RBRACE
  | COMMA
  | RBRAC
  | LBRAC
  | COLON
  | DOT
  | PLUS
  | MINUS
  | STAR
  | DIVIDE
  | ASSIGN
  | PUSH
  | POP
  | PEEK
  | NOT
  | EQ
  | NEQ
  | LT
  | LEQ
  | GT
  | GEQ
  | OR
  | AND
  | MOD
  | RETURN
  | TRANS
  | DFA
  | STACK
  | INT_LITERAL of (int)
  | STRING_LITERAL of (string)
  | TYPE of (string)
  | ID of (string)
  | FLOAT_LITERAL of (float)
  | EOF
  | EOS
  | MAIN
  | STRING
  | INT
  | VOID
  | FLOAT

val program :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ast.program
