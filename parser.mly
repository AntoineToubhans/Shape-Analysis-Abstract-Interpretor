/* =========================================================== */
/* Lexer file: lexer.mll                                       */
/*  - Code C                                                   */
/*  - SL graph input + Pred                                    */
/* =========================================================== */
/*                                        Created: AT 07/08/11 */
/*                                  Last modified: AT 07/08/11 */

%{

  open Offset
  open Utils
  open Domain_sig
  open Neq_pred_domain
  open SL_graph_domain
  open Inductive_def
  open SL_domain
  open Simple_C_syntax
  open SL_Functor_domain
  open Functor_domain

%}

%token <int> CST_INT
%token <string> ID

%token EQ_EQ BANG_EQ
%token EQ
%token LBRACE RBRACE LBRACKET RBRACKET LPAREN RPARENT
%token SEMICOLON
%token DOT ARROW
%token STAR ADDR
%token STRUCT INT
%token IF ELSE WHILE
%token MALLOC NULL
%token EOF

%start main

%type <sc_command> main command
%type <sc_block> block
%type <sc_type> sc_type
%type <sc_cond> cond
%type <sc_exp> expr
%type <sc_vvalue> vvalue
%type <sc_hvalue> hvalue
%type <sc_var_decl> var_decl
%type <sc_struct_decl> struct_decl

%%

main:
                            { Seq [] }
  | block                   { Seq $1 }           

block: 
                            { [] }
  | command block           { $1::$2 }

command:
  hvalue EQ expr SEMICOLON  { Assignment ($1, $3) }
  | var_decl                { VarDeclaration $1 }
  | struct_decl             { StructDeclaration $1 }
  | IF LPAREN cond RPAREN LBRACE block RBRACE ELSE LBRACE block RBRACE 
                            { If ($3, $6, $10) }
  | IF LPAREN cond RPAREN LBRACE block RBRACE 
                            { If ($3, $6, []) }
  | WHILE LPAREN cond RPAREN LBRACE block RBRACE
                            { While ($3, $6) }

sc_type:
  INT                       { ScInt }
  | sc_type STAR            { PointerTo $1 }
  | STRUCT ID               { Struct $2 }

cond:
  expr EQ_EQ expr           { Eq ($1, $3) }
  | expr BANG_EQ expr       { Neq ($1, $3) }

expr:
  hvalue                    { HValue $1 }
  | vvalue                  { VValue $1 }

vvalue:
  MALLOC LPAREN CST_INT RPAREN  
                            { Malloc $3 }
  | ADDR hvalue             { Adress $2 }
  | CST_INT                 { $1 }
  | NULL                    { Null }

hvalue:
  LPAREN hvalue RPAREN      { $2 }
  
