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
%token EOF
