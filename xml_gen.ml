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

       let printf x = Printf.fprintf channel x

       let print_h1 x =
	 printf ("<h1 class=\"cl\">" ^^ x ^^ "</h1>\n") 

       let print_h2 x =
	 printf ("<h2 class=\"cl\">" ^^ x ^^ "</h2>\n") 

       let print_h3 x =
	 printf ("<h3 class=\"cl\">" ^^ x ^^ "</h3>\n") 

       let print_bold x = 
	 printf ("<b>" ^^ x ^^ "</b>") 

       let print_italic x = 
	 printf ("<i>" ^^ x ^^ "</i>") 

       let print_center x = 
	 printf ("<center>" ^^ x ^^ "</center>\n") 

       let print_hr () = printf "<hr class=\"cl\"/>\n"

       type css_class = 
	   { name: string;
	     properties: string list;
	     values: string list; }

       let print_css_class (c:css_class) =
	 printf "%s{\n" c.name;
	 List.iter2
	   (fun pp v -> 
	      printf "%s: %s;\n" pp v)
	   c.properties c.values;
	 printf "}\n"

       let box_SL: css_class = 
	  { name = ".box_SL";
	    properties = 
	      ["background-color"; 
	       "border";
	       "margin"; 
	       "padding"; 
	       "-moz-border-radius"; 
	       "-webkit-border-radius"];
	    values = 
	      ["#FFFFCC";
	       "1px solid #888888";
	       "10px";
	       "10px";
	       "5px 5px 5px 5px";
	       "5px 5px 5px 5px"]; }

       let box_E: css_class = 
	  { name = ".box_E";
	    properties = 
	      ["width"; 
	       "margin";];
	    values = 
	      ["80%";
	       "auto";]; }

       let box_D: css_class = 
	  { name = ".box_D";
	    properties = 
	      ["background-color"; 
	       "border";
	       "margin"; 
	       "padding"; 
	       "-moz-border-radius"; 
	       "-webkit-border-radius"];
	    values = 
	      ["#EEEEEE";
	       "1px solid #888888";
	       "10px";
	       "10px";
	       "5px 5px 5px 5px";
	       "5px 5px 5px 5px"]; }

       let box_D_hover: css_class = 
	  { name = "div.box_D:hover";
	    properties = 
	      ["background-color"; 
	       "border";
	       "margin"; 
	       "padding";];
	    values = 
	      ["#DDDDDD";
	       "2px solid #888888";
	       "10px";
	       "9px"]; }

       let float_left: css_class = 
	 { name = ".fl";
	   properties = ["float"];
	   values = ["left"]; }

       let clear_left: css_class = 
	 { name = ".cl";
	   properties = ["clear"];
	   values = ["left"]; }

       let print_CSS () =   
	 printf "<style type=\"text/css\">\n";
	 print_css_class box_E;
	 print_css_class box_SL;
	 print_css_class box_D;
	 print_css_class box_D_hover;
	 print_css_class float_left;	
	 print_css_class clear_left;
	 printf "</style>\n"

       let print_Script () = 
	 printf "<script type=\"text/javascript\">\n";
	 printf "function fold(obj){obj.lastChild.style.display='none';obj.onclick=function(){unfold(obj)};}\n";
	 printf "function unfold(obj){obj.lastChild.style.display='';obj.onclick=function(){fold(obj)};}\n";
	 printf "</script>\n"

       let print_header () = 
	 printf "<html>\n<head>\n";
	 printf "<title>Shape Analyze Results</title>\n";
	 print_CSS ();
	 print_Script ();
	 printf "</head>\n<body>\n";
	 print_h1 "Shape Analysis results: %s" c_file

       let print_footer () =  
	 printf "\n</body>\n</html>"

     end: XML_GEN) 
