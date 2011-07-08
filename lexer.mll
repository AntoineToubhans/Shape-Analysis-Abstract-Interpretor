(* =========================================================== *)
(* Lexer file: lexer.mll                                       *)
(*  - Code C                                                   *)
(*  - SL graph input + Pred                                    *)
(* =========================================================== *)
(*                                        Created: AT 07/08/11 *)
(*                                  Last modified: AT 07/08/11 *)


{
open Parser
exception Eof
exception Non_supported 
}

let blank = [' ' '\t' '\n']

let decdigit = ['0'-'9']
let intnum = decdigit+

let letter = ['a'- 'z' 'A'-'Z']
let ident = (letter|'_')(letter|decdigit|'_')* 

rule initial = parse
    "/*"        { let _ = comment lexbuf in initial lexbuf }
  | "//"        { line lexbuf }
  | "#"         { line lexbuf }
  | blank       { initial lexbuf }
  | intnum as x	{ CST_INT (int_of_string x) }
  | "!quit!"	{ EOF }
  | "=="	{ EQ_EQ }
  | "!="	{ BANG_EQ }
  | "="		{ EQ }
  | "->"	{ ARROW }
  | '*'		{ STAR }
  | '{'		{ LBRACE }
  | '}'		{ RBRACE }
  | '['		{ LBRACKET }
  | ']'		{ RBRACKET }
  | '('		{ LPAREN }
  | ')'		{ RPAREN }
  | ';'		{ SEMICOLON }
  | '.'		{ DOT }
  | '&'         { ADDR }
  | "struct"	{ STRUCT }
  | "int"       { INT }
  | "if"        { IF }
  | "else"      { ELSE }
  | "while"     { WHILE }
  | "malloc"    { MALLOC }
  | "NULL"      { NULL }
  | eof	        { EOF }
  | ident as s  { ID s }
  | _           { raise Non_supported }


and line = parse
    "\n"        { initial lexbuf }
  | _           { line lexbuf }

(* TO DO *)
and comment = parse
    "*/"        { () }
  | "<*"        { let _ = graph lexbuf in comment lexbuf }
  | _           { comment lexbuf }

and graph = parse
    "*>"        { () }
  | _           { graph lexbuf }

  

