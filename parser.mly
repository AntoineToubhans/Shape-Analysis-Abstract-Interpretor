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
  open Functor_SL2DIS
  open Functor_DIS2DOM

  let count = ref 0
  let genId () = count:= 1 + !count; !count

%}

%token <int> CST_INT
%token <string> ID

%token EQ_EQ BANG_EQ
%token EQ
%token LBRACE RBRACE LBRACKET RBRACKET LPAREN RPAREN
%token SEMICOLON COMMA
%token DOT ARROW
%token STAR ADDR
%token STRUCT INT
%token IF ELSE WHILE
%token MALLOC NULL
%token VOID MAIN
%token SPEC_CANON SPEC_FORGET_IND_LENGTH
%token EOF 

%left LBRACKET
%left STAR ADDR
%left DOT ARROW

%start main file

%type <Simple_C_syntax.sc_command> file main command 
%type <sc_block> block
%type <sc_type> p_type
%type <sc_cond> cond
%type <sc_exp> expr
%type <sc_vvalue> vvalue
%type <sc_hvalue> hvalue
%type <sc_var_decl> var_decl
%type <sc_struct_decl> struct_decl
%type <(string * sc_type) list > struct_decl_inside 

%%

file:
  VOID MAIN LPAREN RPAREN LBRACE main RBRACE
                            { $6 }

main:
  block                     { Seq $1 }           

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
  | SPEC_CANON SEMICOLON
                            { Spec(Canonicalize) }
  | SPEC_FORGET_IND_LENGTH SEMICOLON
                            { Spec(Forget_inductive_length) }

p_type:
  INT                       { ScInt }
  | p_type STAR             { PointerTo $1 }
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
  | ADDR hvalue             { Address $2 }
  | CST_INT                 { IntConst $1 }
  | NULL                    { Null }

hvalue:
  LPAREN hvalue RPAREN      { $2 }
  | ID                      { Var $1 }
  | hvalue LBRACKET CST_INT RBRACKET
                            { ArrayAccess ($3, $1) }
  | hvalue DOT ID           { FieldAccess ($3, $1) }
  | STAR hvalue             { Deref $2 }
  | hvalue ARROW ID         { FieldAccess ($3, Deref $1) }

var_decl:
  p_type ID EQ expr SEMICOLON        
                            { { var_name=$2; 
				var_type=$1;
				var_uniqueId=genId ();},
			      Some $4 }
  | p_type ID SEMICOLON     { { var_name=$2; 
				var_type=$1;
				var_uniqueId=genId ();},
			      None }

struct_decl:
  STRUCT ID LBRACE struct_decl_inside RBRACE SEMICOLON 
                             { $2, $4 }

struct_decl_inside:
                             { [] }
  | p_type ID SEMICOLON struct_decl_inside
                             { ($2, $1)::$4 }


%%
				  
