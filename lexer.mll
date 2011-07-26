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
    "/*"        { comment lexbuf }
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
  | ','         { COMMA }
  | '.'		{ DOT }
  | '&'         { ADDR }
  | "struct"	{ STRUCT }
  | "int"       { INT }
  | "void"      { VOID }
  | "main"      { MAIN }
  | "if"        { IF }
  | "else"      { ELSE }
  | "while"     { WHILE }
  | "malloc"    { MALLOC }
  | "NULL"      { NULL }
  | "canonicalize"
                { SPEC_CANON }
  | "forget_inductive_length"
                { SPEC_FORGET_IND_LENGTH }
  | "SPEC_"     { comment lexbuf }
  | eof	        { EOF }
  | ident as s  { ID s } 
  | _           { raise Non_supported }


and line = parse
    "\n"        { initial lexbuf }
  | _           { line lexbuf }

and comment = parse
    "*/"        { initial lexbuf }
  | "_SPEC"     { initial lexbuf }
  | _           { comment lexbuf }



  

