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

open Parsing;;
let _ = parse_error;;
# 1 "parser.mly"
 open Ast 
# 52 "parser.ml"
let yytransl_const = [|
  257 (* SEMI *);
  258 (* LPAREN *);
  259 (* RPAREN *);
  260 (* LBRACE *);
  261 (* RBRACE *);
  262 (* COMMA *);
  263 (* RBRAC *);
  264 (* LBRAC *);
  265 (* COLON *);
  266 (* DOT *);
  267 (* PLUS *);
  268 (* MINUS *);
  269 (* STAR *);
  270 (* DIVIDE *);
  271 (* ASSIGN *);
  272 (* PUSH *);
  273 (* POP *);
  274 (* PEEK *);
  275 (* NOT *);
  276 (* EQ *);
  277 (* NEQ *);
  278 (* LT *);
  279 (* LEQ *);
  280 (* GT *);
  281 (* GEQ *);
  282 (* OR *);
  283 (* AND *);
  284 (* MOD *);
  285 (* RETURN *);
  286 (* TRANS *);
  287 (* DFA *);
  288 (* STACK *);
    0 (* EOF *);
  294 (* EOS *);
  295 (* MAIN *);
  296 (* STRING *);
  297 (* INT *);
  298 (* VOID *);
  299 (* FLOAT *);
    0|]

let yytransl_block = [|
  289 (* INT_LITERAL *);
  290 (* STRING_LITERAL *);
  291 (* TYPE *);
  292 (* ID *);
  293 (* FLOAT_LITERAL *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\003\000\003\000\003\000\003\000\004\000\004\000\
\002\000\006\000\006\000\008\000\008\000\008\000\007\000\007\000\
\010\000\011\000\011\000\012\000\012\000\012\000\012\000\012\000\
\012\000\012\000\005\000\005\000\013\000\013\000\014\000\014\000\
\015\000\015\000\015\000\009\000\009\000\009\000\009\000\009\000\
\009\000\009\000\009\000\009\000\009\000\009\000\009\000\009\000\
\009\000\009\000\009\000\009\000\009\000\009\000\009\000\009\000\
\009\000\009\000\009\000\009\000\000\000"

let yylen = "\002\000\
\000\000\002\000\001\000\001\000\001\000\001\000\001\000\004\000\
\010\000\000\000\002\000\003\000\005\000\006\000\000\000\002\000\
\004\000\000\000\002\000\003\000\004\000\004\000\001\000\004\000\
\002\000\002\000\000\000\001\000\001\000\003\000\002\000\005\000\
\000\000\003\000\001\000\001\000\001\000\001\000\001\000\001\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\002\000\002\000\003\000\
\005\000\006\000\005\000\004\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\004\000\003\000\006\000\005\000\061\000\
\000\000\007\000\000\000\000\000\002\000\000\000\000\000\000\000\
\008\000\000\000\000\000\000\000\000\000\000\000\029\000\000\000\
\031\000\000\000\000\000\000\000\000\000\030\000\000\000\000\000\
\000\000\000\000\000\000\032\000\000\000\000\000\000\000\000\000\
\000\000\011\000\000\000\012\000\000\000\000\000\009\000\016\000\
\000\000\000\000\000\000\000\000\036\000\037\000\000\000\038\000\
\040\000\000\000\000\000\000\000\023\000\000\000\000\000\000\000\
\000\000\000\000\054\000\000\000\000\000\000\000\013\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\026\000\000\000\000\000\000\000\
\025\000\017\000\019\000\014\000\056\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\043\000\044\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\051\000\020\000\
\000\000\000\000\000\000\000\000\060\000\000\000\000\000\000\000\
\024\000\022\000\021\000\034\000\000\000\057\000\059\000\058\000"

let yydgoto = "\002\000\
\008\000\009\000\033\000\011\000\021\000\034\000\040\000\035\000\
\062\000\041\000\063\000\064\000\022\000\023\000\095\000"

let yysindex = "\016\000\
\018\255\000\000\253\254\000\000\000\000\000\000\000\000\000\000\
\018\255\000\000\247\254\059\255\000\000\243\254\001\255\042\255\
\000\000\244\255\029\255\016\255\050\255\048\255\000\000\059\255\
\000\000\060\255\244\255\041\255\056\000\000\000\030\255\046\255\
\033\255\034\255\056\000\000\000\059\255\000\255\074\255\077\255\
\034\255\000\000\066\255\000\000\093\255\043\255\000\000\000\000\
\058\255\093\255\093\255\093\255\000\000\000\000\006\255\000\000\
\000\000\153\255\055\255\011\255\000\000\171\255\091\255\043\255\
\102\255\177\000\000\000\006\001\093\255\250\254\000\000\093\255\
\093\255\093\255\093\255\093\255\093\255\093\255\093\255\093\255\
\093\255\093\255\093\255\093\255\000\000\189\255\093\255\085\255\
\000\000\000\000\000\000\000\000\000\000\226\000\103\255\105\255\
\109\255\112\255\246\254\246\254\000\000\000\000\035\255\035\255\
\035\255\035\255\035\255\035\255\244\000\006\001\000\000\000\000\
\207\255\108\255\225\255\093\255\000\000\093\255\113\255\117\255\
\000\000\000\000\000\000\000\000\203\000\000\000\000\000\000\000"

let yyrindex = "\000\000\
\115\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\115\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\121\255\000\000\000\000\000\000\129\255\000\000\000\000\
\000\000\000\000\000\000\000\000\004\255\000\000\000\000\000\000\
\000\000\130\255\004\255\000\000\000\000\000\000\000\000\000\000\
\130\255\000\000\000\000\000\000\000\000\132\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\135\255\000\000\
\000\000\000\000\000\000\243\255\000\000\000\000\000\000\132\255\
\000\000\000\000\000\000\046\000\136\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\139\255\000\000\000\000\
\000\000\000\000\015\000\042\000\000\000\000\000\054\000\081\000\
\089\000\117\000\125\000\152\000\107\255\156\000\000\000\000\000\
\000\000\000\000\000\000\136\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\135\000\000\000\116\000\000\000\000\000\110\000\109\000\212\255\
\211\255\000\000\087\000\000\000\000\000\141\000\036\000"

let yytablesize = 546
let yytable = "\058\000\
\044\000\061\000\074\000\075\000\066\000\067\000\068\000\069\000\
\010\000\096\000\097\000\098\000\069\000\086\000\045\000\070\000\
\001\000\084\000\012\000\061\000\070\000\014\000\016\000\094\000\
\017\000\087\000\099\000\100\000\101\000\102\000\103\000\104\000\
\105\000\106\000\107\000\108\000\109\000\110\000\111\000\010\000\
\088\000\113\000\115\000\018\000\050\000\072\000\073\000\074\000\
\075\000\003\000\024\000\025\000\026\000\027\000\051\000\085\000\
\050\000\004\000\005\000\006\000\007\000\052\000\084\000\029\000\
\031\000\036\000\051\000\037\000\038\000\039\000\094\000\059\000\
\125\000\052\000\032\000\053\000\054\000\046\000\060\000\056\000\
\057\000\047\000\004\000\005\000\006\000\007\000\050\000\053\000\
\054\000\049\000\055\000\056\000\057\000\065\000\050\000\090\000\
\051\000\114\000\004\000\005\000\006\000\007\000\092\000\052\000\
\051\000\117\000\118\000\053\000\122\000\053\000\119\000\052\000\
\053\000\120\000\001\000\126\000\010\000\053\000\054\000\127\000\
\055\000\056\000\057\000\027\000\010\000\053\000\054\000\015\000\
\055\000\056\000\057\000\028\000\053\000\020\000\015\000\039\000\
\018\000\039\000\033\000\028\000\039\000\035\000\020\000\013\000\
\042\000\039\000\039\000\039\000\039\000\048\000\091\000\124\000\
\043\000\071\000\039\000\039\000\039\000\039\000\039\000\039\000\
\039\000\039\000\039\000\072\000\073\000\074\000\075\000\030\000\
\000\000\000\000\000\000\089\000\076\000\077\000\078\000\079\000\
\080\000\081\000\082\000\083\000\084\000\072\000\073\000\074\000\
\075\000\000\000\000\000\000\000\000\000\112\000\076\000\077\000\
\078\000\079\000\080\000\081\000\082\000\083\000\084\000\072\000\
\073\000\074\000\075\000\000\000\000\000\000\000\000\000\121\000\
\076\000\077\000\078\000\079\000\080\000\081\000\082\000\083\000\
\084\000\072\000\073\000\074\000\075\000\000\000\000\000\000\000\
\000\000\123\000\076\000\077\000\078\000\079\000\080\000\081\000\
\082\000\083\000\084\000\072\000\073\000\074\000\075\000\000\000\
\000\000\000\000\000\000\039\000\076\000\077\000\078\000\079\000\
\080\000\081\000\082\000\083\000\084\000\039\000\039\000\039\000\
\039\000\000\000\000\000\000\000\000\000\000\000\039\000\039\000\
\039\000\039\000\039\000\039\000\039\000\039\000\039\000\041\000\
\000\000\041\000\000\000\019\000\041\000\000\000\000\000\000\000\
\000\000\041\000\041\000\004\000\005\000\006\000\007\000\000\000\
\000\000\000\000\041\000\041\000\041\000\041\000\041\000\041\000\
\041\000\041\000\042\000\000\000\042\000\000\000\055\000\042\000\
\055\000\000\000\000\000\055\000\042\000\042\000\045\000\000\000\
\045\000\000\000\000\000\045\000\000\000\042\000\042\000\042\000\
\042\000\042\000\042\000\042\000\042\000\000\000\000\000\055\000\
\055\000\045\000\045\000\045\000\045\000\045\000\045\000\045\000\
\045\000\046\000\000\000\046\000\000\000\000\000\046\000\032\000\
\000\000\047\000\000\000\047\000\000\000\000\000\047\000\004\000\
\005\000\006\000\007\000\000\000\046\000\046\000\046\000\046\000\
\046\000\046\000\046\000\046\000\047\000\047\000\047\000\047\000\
\047\000\047\000\047\000\047\000\000\000\048\000\000\000\048\000\
\000\000\000\000\048\000\000\000\000\000\049\000\000\000\049\000\
\000\000\000\000\049\000\000\000\000\000\000\000\000\000\000\000\
\048\000\048\000\048\000\048\000\048\000\048\000\048\000\048\000\
\049\000\049\000\049\000\049\000\049\000\049\000\049\000\049\000\
\050\000\000\000\050\000\000\000\052\000\050\000\052\000\000\000\
\000\000\052\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\050\000\050\000\050\000\050\000\050\000\
\050\000\050\000\050\000\093\000\000\000\052\000\052\000\000\000\
\000\000\000\000\000\000\072\000\073\000\074\000\075\000\000\000\
\000\000\000\000\000\000\000\000\076\000\077\000\078\000\079\000\
\080\000\081\000\082\000\083\000\084\000\128\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\072\000\073\000\074\000\
\075\000\000\000\000\000\000\000\000\000\000\000\076\000\077\000\
\078\000\079\000\080\000\081\000\082\000\083\000\084\000\116\000\
\000\000\000\000\000\000\000\000\072\000\073\000\074\000\075\000\
\000\000\000\000\000\000\000\000\000\000\076\000\077\000\078\000\
\079\000\080\000\081\000\082\000\083\000\084\000\072\000\073\000\
\074\000\075\000\000\000\000\000\000\000\000\000\000\000\076\000\
\077\000\078\000\079\000\080\000\081\000\000\000\083\000\084\000\
\072\000\073\000\074\000\075\000\000\000\000\000\000\000\000\000\
\000\000\076\000\077\000\078\000\079\000\080\000\081\000\000\000\
\000\000\084\000"

let yycheck = "\045\000\
\001\001\046\000\013\001\014\001\050\000\051\000\052\000\002\001\
\005\001\016\001\017\001\018\001\002\001\059\000\015\001\010\001\
\001\000\028\001\022\001\064\000\010\001\031\001\036\001\069\000\
\024\001\015\001\072\000\073\000\074\000\075\000\076\000\077\000\
\078\000\079\000\080\000\081\000\082\000\083\000\084\000\036\001\
\030\001\087\000\088\000\002\001\002\001\011\001\012\001\013\001\
\014\001\032\001\022\001\036\001\003\001\006\001\012\001\001\001\
\002\001\040\001\041\001\042\001\043\001\019\001\028\001\004\001\
\024\001\036\001\012\001\022\001\036\001\036\001\116\000\029\001\
\118\000\019\001\032\001\033\001\034\001\004\001\036\001\037\001\
\038\001\005\001\040\001\041\001\042\001\043\001\002\001\033\001\
\034\001\024\001\036\001\037\001\038\001\036\001\002\001\005\001\
\012\001\013\001\040\001\041\001\042\001\043\001\001\001\019\001\
\012\001\003\001\002\001\001\001\001\001\003\001\002\001\019\001\
\006\001\002\001\000\000\003\001\001\000\033\001\034\001\003\001\
\036\001\037\001\038\001\003\001\009\000\033\001\034\001\012\000\
\036\001\037\001\038\001\003\001\026\001\018\000\005\001\001\001\
\005\001\003\001\003\001\024\000\006\001\003\001\027\000\009\000\
\035\000\011\001\012\001\013\001\014\001\041\000\064\000\116\000\
\037\000\001\001\020\001\021\001\022\001\023\001\024\001\025\001\
\026\001\027\001\028\001\011\001\012\001\013\001\014\001\027\000\
\255\255\255\255\255\255\001\001\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\028\001\011\001\012\001\013\001\
\014\001\255\255\255\255\255\255\255\255\001\001\020\001\021\001\
\022\001\023\001\024\001\025\001\026\001\027\001\028\001\011\001\
\012\001\013\001\014\001\255\255\255\255\255\255\255\255\001\001\
\020\001\021\001\022\001\023\001\024\001\025\001\026\001\027\001\
\028\001\011\001\012\001\013\001\014\001\255\255\255\255\255\255\
\255\255\001\001\020\001\021\001\022\001\023\001\024\001\025\001\
\026\001\027\001\028\001\011\001\012\001\013\001\014\001\255\255\
\255\255\255\255\255\255\001\001\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\028\001\011\001\012\001\013\001\
\014\001\255\255\255\255\255\255\255\255\255\255\020\001\021\001\
\022\001\023\001\024\001\025\001\026\001\027\001\028\001\001\001\
\255\255\003\001\255\255\032\001\006\001\255\255\255\255\255\255\
\255\255\011\001\012\001\040\001\041\001\042\001\043\001\255\255\
\255\255\255\255\020\001\021\001\022\001\023\001\024\001\025\001\
\026\001\027\001\001\001\255\255\003\001\255\255\001\001\006\001\
\003\001\255\255\255\255\006\001\011\001\012\001\001\001\255\255\
\003\001\255\255\255\255\006\001\255\255\020\001\021\001\022\001\
\023\001\024\001\025\001\026\001\027\001\255\255\255\255\026\001\
\027\001\020\001\021\001\022\001\023\001\024\001\025\001\026\001\
\027\001\001\001\255\255\003\001\255\255\255\255\006\001\032\001\
\255\255\001\001\255\255\003\001\255\255\255\255\006\001\040\001\
\041\001\042\001\043\001\255\255\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\255\255\001\001\255\255\003\001\
\255\255\255\255\006\001\255\255\255\255\001\001\255\255\003\001\
\255\255\255\255\006\001\255\255\255\255\255\255\255\255\255\255\
\020\001\021\001\022\001\023\001\024\001\025\001\026\001\027\001\
\020\001\021\001\022\001\023\001\024\001\025\001\026\001\027\001\
\001\001\255\255\003\001\255\255\001\001\006\001\003\001\255\255\
\255\255\006\001\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\020\001\021\001\022\001\023\001\024\001\
\025\001\026\001\027\001\003\001\255\255\026\001\027\001\255\255\
\255\255\255\255\255\255\011\001\012\001\013\001\014\001\255\255\
\255\255\255\255\255\255\255\255\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\028\001\003\001\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\011\001\012\001\013\001\
\014\001\255\255\255\255\255\255\255\255\255\255\020\001\021\001\
\022\001\023\001\024\001\025\001\026\001\027\001\028\001\006\001\
\255\255\255\255\255\255\255\255\011\001\012\001\013\001\014\001\
\255\255\255\255\255\255\255\255\255\255\020\001\021\001\022\001\
\023\001\024\001\025\001\026\001\027\001\028\001\011\001\012\001\
\013\001\014\001\255\255\255\255\255\255\255\255\255\255\020\001\
\021\001\022\001\023\001\024\001\025\001\255\255\027\001\028\001\
\011\001\012\001\013\001\014\001\255\255\255\255\255\255\255\255\
\255\255\020\001\021\001\022\001\023\001\024\001\025\001\255\255\
\255\255\028\001"

let yynames_const = "\
  SEMI\000\
  LPAREN\000\
  RPAREN\000\
  LBRACE\000\
  RBRACE\000\
  COMMA\000\
  RBRAC\000\
  LBRAC\000\
  COLON\000\
  DOT\000\
  PLUS\000\
  MINUS\000\
  STAR\000\
  DIVIDE\000\
  ASSIGN\000\
  PUSH\000\
  POP\000\
  PEEK\000\
  NOT\000\
  EQ\000\
  NEQ\000\
  LT\000\
  LEQ\000\
  GT\000\
  GEQ\000\
  OR\000\
  AND\000\
  MOD\000\
  RETURN\000\
  TRANS\000\
  DFA\000\
  STACK\000\
  EOF\000\
  EOS\000\
  MAIN\000\
  STRING\000\
  INT\000\
  VOID\000\
  FLOAT\000\
  "

let yynames_block = "\
  INT_LITERAL\000\
  STRING_LITERAL\000\
  TYPE\000\
  ID\000\
  FLOAT_LITERAL\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    Obj.repr(
# 32 "parser.mly"
  ([])
# 384 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'dfa_decl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.program) in
    Obj.repr(
# 33 "parser.mly"
                     ( _1 :: _2 )
# 392 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    Obj.repr(
# 36 "parser.mly"
                           (Int)
# 398 "parser.ml"
               : 'var_type))
; (fun __caml_parser_env ->
    Obj.repr(
# 37 "parser.mly"
                           (String)
# 404 "parser.ml"
               : 'var_type))
; (fun __caml_parser_env ->
    Obj.repr(
# 38 "parser.mly"
                           (Float)
# 410 "parser.ml"
               : 'var_type))
; (fun __caml_parser_env ->
    Obj.repr(
# 39 "parser.mly"
                           (Void)
# 416 "parser.ml"
               : 'var_type))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'var_type) in
    Obj.repr(
# 42 "parser.mly"
             (Datatype(_1))
# 423 "parser.ml"
               : 'ret_type))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'var_type) in
    Obj.repr(
# 43 "parser.mly"
                         (Stacktype(Datatype(_3)))
# 430 "parser.ml"
               : 'ret_type))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 9 : 'ret_type) in
    let _3 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 5 : 'formals_opt) in
    let _8 = (Parsing.peek_val __caml_parser_env 2 : 'vdecl_list) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'node_list) in
    Obj.repr(
# 47 "parser.mly"
    ( { return = _1;
    dfa_name = Ident(_3);
    formals = _5;
    var_body = _8; 
    node_body = _9})
# 445 "parser.ml"
               : 'dfa_decl))
; (fun __caml_parser_env ->
    Obj.repr(
# 54 "parser.mly"
    ([])
# 451 "parser.ml"
               : 'vdecl_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'vdecl) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'vdecl_list) in
    Obj.repr(
# 55 "parser.mly"
                       ( _1 :: _2 )
# 459 "parser.ml"
               : 'vdecl_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'var_type) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 58 "parser.mly"
                       ( VarDecl(Datatype(_1), Ident(_2)) )
# 467 "parser.ml"
               : 'vdecl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'var_type) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 59 "parser.mly"
                                   ( VarAssignDecl(Datatype(_1), Ident(_2), ExprVal(_4)))
# 476 "parser.ml"
               : 'vdecl))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'var_type) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 60 "parser.mly"
                                   ( VarDecl(Stacktype(Datatype(_3)), Ident(_5)) )
# 484 "parser.ml"
               : 'vdecl))
; (fun __caml_parser_env ->
    Obj.repr(
# 63 "parser.mly"
    ([])
# 490 "parser.ml"
               : 'node_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'node) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'node_list) in
    Obj.repr(
# 64 "parser.mly"
                     ( _1 :: _2 )
# 498 "parser.ml"
               : 'node_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'stmt_list) in
    Obj.repr(
# 67 "parser.mly"
                             ( Node(Ident(_1), _3) )
# 506 "parser.ml"
               : 'node))
; (fun __caml_parser_env ->
    Obj.repr(
# 70 "parser.mly"
 ([])
# 512 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt_list) in
    Obj.repr(
# 71 "parser.mly"
                  ( _1 :: _2 )
# 520 "parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 75 "parser.mly"
                   (Return(_2))
# 527 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 76 "parser.mly"
                      (Transition(Ident(_1),_3))
# 535 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    Obj.repr(
# 77 "parser.mly"
                      (Transition(Ident(_1),IntLit(1)))
# 542 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'vdecl) in
    Obj.repr(
# 78 "parser.mly"
         (Declaration(_1))
# 549 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 79 "parser.mly"
                        ( Assign(Ident(_1), _3) )
# 557 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 80 "parser.mly"
             (Expr(_1))
# 564 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 81 "parser.mly"
                (Return(IntLit(1)))
# 570 "parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 84 "parser.mly"
    ([])
# 576 "parser.ml"
               : 'formals_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'formal_list) in
    Obj.repr(
# 85 "parser.mly"
                  ( List.rev _1)
# 583 "parser.ml"
               : 'formals_opt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'param) in
    Obj.repr(
# 88 "parser.mly"
          ( [_1] )
# 590 "parser.ml"
               : 'formal_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formal_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'param) in
    Obj.repr(
# 89 "parser.mly"
                              ( _3 :: _1)
# 598 "parser.ml"
               : 'formal_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'var_type) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 92 "parser.mly"
                  ( Formal(Datatype(_1),Ident(_2)) )
# 606 "parser.ml"
               : 'param))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'var_type) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 93 "parser.mly"
                                ( Formal(Stacktype(Datatype(_3)), Ident(_5)) )
# 614 "parser.ml"
               : 'param))
; (fun __caml_parser_env ->
    Obj.repr(
# 96 "parser.mly"
    ([])
# 620 "parser.ml"
               : 'expr_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr_list) in
    Obj.repr(
# 97 "parser.mly"
                           ( _1 :: _3 )
# 628 "parser.ml"
               : 'expr_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 98 "parser.mly"
           ( [_1] )
# 635 "parser.ml"
               : 'expr_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 101 "parser.mly"
                   ( IntLit(_1)   )
# 642 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 102 "parser.mly"
                   ( StringLit(_1) )
# 649 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 103 "parser.mly"
                   ( FloatLit(_1) )
# 656 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 104 "parser.mly"
                     ( Variable(Ident(_1))  )
# 663 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 105 "parser.mly"
                     ( EosLit )
# 669 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 106 "parser.mly"
                     ( Binop(_1, Add,   _3) )
# 677 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 107 "parser.mly"
                     ( Binop(_1, Sub,   _3) )
# 685 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 108 "parser.mly"
                     ( Binop(_1, Mult,  _3) )
# 693 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 109 "parser.mly"
                     ( Binop(_1, Div,   _3) )
# 701 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 110 "parser.mly"
                     ( Binop(_1, Equal, _3) )
# 709 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 111 "parser.mly"
                     ( Binop(_1, Neq,   _3) )
# 717 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 112 "parser.mly"
                     ( Binop(_1, Lt,  _3) )
# 725 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 113 "parser.mly"
                     ( Binop(_1, Leq,   _3) )
# 733 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 114 "parser.mly"
                     ( Binop(_1, Gt,_3))
# 741 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 115 "parser.mly"
                     ( Binop(_1, Geq,   _3) )
# 749 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 116 "parser.mly"
                     ( Binop(_1, Mod,   _3) )
# 757 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 117 "parser.mly"
                     ( Binop(_1, And,   _3) )
# 765 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 118 "parser.mly"
                     ( Binop(_1, Or ,   _3) )
# 773 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 119 "parser.mly"
                            ( Unop(Neg, _2) )
# 780 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 120 "parser.mly"
                            ( Unop(Not, _2) )
# 787 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 121 "parser.mly"
                       ( _2 )
# 794 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    Obj.repr(
# 122 "parser.mly"
                                            ( Pop(Ident(_1)) )
# 801 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 123 "parser.mly"
                                            ( Push(Ident(_1), _5) )
# 809 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : string) in
    Obj.repr(
# 124 "parser.mly"
                                            ( Peek(Ident(_1)) )
# 816 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr_list) in
    Obj.repr(
# 125 "parser.mly"
                               (Call(Ident(_1), _3) (*call a sub dfa*))
# 824 "parser.ml"
               : 'expr))
(* Entry program *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let program (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ast.program)
