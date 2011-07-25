(* =========================================================== *)
(* XML Generator                                               *)
(* =========================================================== *)
(*                                        Created: AT 07/25/11 *)
(*                                  Last modified: AT 07/25/11 *)

open Domain_sig
open Utils

module type XML_GEN_ARGS = 
  sig
    val c_file: string
  end

module XML_GEN = 
  functor (A: XML_GEN_ARGS) ->
    (struct

       let c_file = A.c_file

       let xml_file =   
	 String.create ((String.length c_file) + 3)
      
       let _ = 
	 let n = String.length c_file in
	   String.blit c_file 0 xml_file 0 (n-1);
	   xml_file.[n-1] <- 'h';
	   xml_file.[n] <- 't';
	   xml_file.[n+1] <- 'm';
	   xml_file.[n+2] <- 'l'

       let channel = open_out xml_file

       let fprintf = 
	 fun x -> Printf.fprintf channel x

       let printf s = 
	 Printf.fprintf channel "%s" s

       let print_h1 s = 
	 Printf.fprintf channel "<h1>%s</h1>\n" s

       let print_h2 s = 
	 Printf.fprintf channel "<h2>%s</h2>\n" s

       let print_h3 s = 
	 Printf.fprintf channel "<h3>%s</h3>\n" s

       let print_bold s = 
	 Printf.fprintf channel "<b>%s</b><br/>\n" s

       let print_center s = 
	 Printf.fprintf channel "<center>%s</center>\n" s

       let print_hr s = Printf.fprintf channel "<hr />\n"

       let print_header () = 
	 printf "<html>\n<head>\n";
	 printf "<title>Shape Analyze Results</title>\n";
	 (* CSS *)
	 printf "<style type=\"text/css\">\n.box{\nbackground-color: #FFFFCC;";
	 printf "\nborder: 1px solid #888888;";
	 printf "\nmargin: 10px;";
	 printf "\npadding: 10px;";
	 printf "\n-moz-border-radius : 5px 5px 5px 5px;";
	 printf "\n-webkit-border-radius : 5px 5px 5px 5px;";
	 printf "\n}\n.fl{\nfloat: left;";
	 printf "\n}\n</style>\n";
	 printf "</head>\n<body>\n";
	 print_h1 
	   (Printf.sprintf "Shape Analysis results: %s" c_file)

       let print_footer () =  
	 printf "\n</body>\n</html>"

     end: XML_GEN) 
