open Domain_sig
open Inductive_def
open SL_domain
open Functor_SL2DIS
open Functor_DIS2DOM

(* =========================================================== *)
(* Main file A Toubhans internship project                     *)
(* =========================================================== *)
(*                                        Created: AT 07/08/11 *)
(*                                  Last modified: AT 07/08/11 *)

module O1 = 
  struct
    let debug = true
  end

module O2 = 
  struct
    let debug = false
  end

module SL1 = MAKE_DOMAIN(MAKE_DIS_DOMAIN(MAKE_SL_DOMAIN(SList)(O1))(O1))(O1)
module SL2 = MAKE_DOMAIN(MAKE_DIS_DOMAIN(MAKE_SL_DOMAIN(SList)(O2))(O2))(O2)

let main () =
  
  (* Parsing arguments *)
  let f_name = ref "" 
  and debug = ref false 
  and kind_ind = ref "" in
    
    Arg.parse
      [ "-debug", Arg.Set debug, "\tDebug mode" ;
        "-a", Arg.Set_string kind_ind, "\tKind of the inductive among the following:\n\t* SL (Singly-linked List)\n\t* TL (Topped List)\n\t* DL (Doubly-linked List)" ]
      (fun s -> f_name := s)  
      "Shape Analyzer by A.Toubhans";

    (* Parsing of the source file *)
    let c: Simple_C_syntax.sc_command =
      if String.compare !f_name "" = 0 then failwith "no program file given";
      let file = open_in !f_name in
      let lexbuf = Lexing.from_channel file in
	try Parser.file Lexer.initial lexbuf
      with
	| e -> 
	    Printf.printf "Exception during parsing: %s\n"
	      (Printexc.to_string e);
            failwith "Stopped" in
(*      Printf.printf "%s\n" (Simple_C_syntax.sc_command2str c); *)
      if String.compare !kind_ind "SL" = 0 && !debug then
	let _ = SL1.eval_sc_command SL1.init c in ();
      if String.compare !kind_ind "SL" = 0 && not !debug then
	let _ = SL2.eval_sc_command SL2.init c in ();
	  
	  Printf.printf "finished...\n" 
	

let _ = main ()
