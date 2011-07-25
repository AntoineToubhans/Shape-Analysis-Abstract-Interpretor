open Domain_sig
open Inductive_def
open SL_domain
open Functor_SL2DIS
open Functor_DIS2DOM
open Xml_gen

(* =========================================================== *)
(* Main file A Toubhans internship project                     *)
(* =========================================================== *)
(*                                        Created: AT 07/08/11 *)
(*                                  Last modified: AT 07/25/11 *)

  
(* Parsing arguments *)
let f_name = ref "" 
and debug = ref false 
and kind_ind = ref "" 
  
let _ =   
  Arg.parse
    [ "-debug", Arg.Set debug, "\tDebug mode" ;
      "-a", Arg.Set_string kind_ind, "\tKind of the inductive among the following:\n\t* SL (Singly-linked List)\n\t* TL (Topped List)\n\t* DL (Doubly-linked List)" ]
    (fun s -> f_name := s)  
    "Shape Analyzer by A.Toubhans"

(* Parsing of the source file *)
let c: Simple_C_syntax.sc_command =
  if String.compare !f_name "" = 0 then failwith "no program file given";
  if (!f_name).[(String.length !f_name) - 1] != 'c' then failwith "bad file type"; 
  let file = open_in !f_name in
  let lexbuf = Lexing.from_channel file in
    try Parser.file Lexer.initial lexbuf
    with
      | e -> 
	  Printf.printf "Exception during parsing: %s\n"
	    (Printexc.to_string e);
          failwith "Stopped"

module O = 
struct
  let debug = !debug
  let c_file = !f_name      
  module XML = XML_GEN(struct
		       let c_file = !f_name
		     end)
end
  
module SL = MAKE_DOMAIN(MAKE_DIS_DOMAIN(MAKE_SL_DOMAIN(SList)(O))(O))(O)
module TL = MAKE_DOMAIN(MAKE_DIS_DOMAIN(MAKE_SL_DOMAIN(TList)(O))(O))(O)
module DL = MAKE_DOMAIN(MAKE_DIS_DOMAIN(MAKE_SL_DOMAIN(DLList)(O))(O))(O)

let _  =
  O.XML.print_header ();
  if String.compare !kind_ind "SL" = 0 then
    ignore (SL.eval_sc_command SL.init c)
  else if String.compare !kind_ind "TL" = 0 then
    ignore (TL.eval_sc_command TL.init c)
  else if String.compare !kind_ind "DL" = 0 then
    ignore (DL.eval_sc_command DL.init c)
  else
    begin
      Printf.printf "Kind of inductive not available: %s\n" !kind_ind;
      failwith "Stopped"
    end;
  O.XML.print_footer ();
  Unix.system (Printf.sprintf "firefox %s&" O.XML.xml_file);
  Printf.printf "finished...\n" 
	


