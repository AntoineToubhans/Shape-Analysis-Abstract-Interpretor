open Domain_sig
open Inductive_def
open SL_domain
open Functor_SLSL2SL
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
and list_ind = ref []
  
let _ =   
  Arg.parse
    (Arg.align
       [ "-debug", Arg.Set debug, " Debug mode" ;
	 "-SL", Arg.Unit (fun () -> list_ind:="SL"::(!list_ind)), "Singly linked list";
	 "-TL", Arg.Unit (fun () -> list_ind:="TL"::(!list_ind)), "Topped singly linked list";
	 "-DL", Arg.Unit (fun () -> list_ind:="DL"::(!list_ind)), "Doubly linked list";
	 "-TDL", Arg.Unit (fun () -> list_ind:="TDL"::(!list_ind)), "Topped doubly linked list" ])
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

module O = struct
  let debug = !debug
  let c_file = !f_name      
  module XML = XML_GEN(struct
			 let c_file = !f_name
		       end)
end

let rec build_SL: string Utils.bTree -> (module SL_DOMAIN) = function
  | Utils.Empty -> 
      Printf.printf "No inductive given!\n";
      failwith "Stopped"
  | Utils.Leaf ind ->
      let module I = 
	( val (Hashtbl.find selector ind): INDUCTIVE_DEF ) in
	( module MAKE_SL_DOMAIN(I)(O): SL_DOMAIN )
  | Utils.Node (a, b) -> 
      let module S = 
	( val ( build_SL a ): SL_DOMAIN ) in
      let module T = 
	( val ( build_SL b ): SL_DOMAIN ) in
	( module MAKE_PROD_SL_DOMAIN(S)(T)(O): SL_DOMAIN )
	

module SL = ( val ( build_SL ( Utils.list2bTree !list_ind ) ): SL_DOMAIN) 
module DIS = MAKE_DIS_DOMAIN(SL)(O)
module DOM = MAKE_DOMAIN(DIS)(O)


let _  =
  O.XML.print_header ();
(*  O.XML.printf (Simple_C_syntax.sc_command2str c); *)
  ignore (DOM.eval_sc_command DOM.init c);
  O.XML.print_footer ();
(*  ignore (Unix.system (Printf.sprintf "firefox %s&" O.XML.xml_file)); *)
  Printf.printf "finished...\n" 
	


