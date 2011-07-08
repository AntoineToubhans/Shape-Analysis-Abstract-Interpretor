(* =========================================================== *)
(* Main file A Toubhans internship project                     *)
(* =========================================================== *)
(*                                        Created: AT 07/08/11 *)
(*                                  Last modified: AT 07/08/11 *)

let main () =
  
  (* Parsing arguments *)
  let f_name = ref "" 
  and debug = ref false in
    
    Arg.parse
      [ "-debug", Arg.Set debug, "Debug mode" ]
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
      Printf.printf "%s\nfinished...\n" (Simple_C_syntax.sc_command2str c)

let _ = main ()
