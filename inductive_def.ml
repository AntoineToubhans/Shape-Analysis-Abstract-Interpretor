open Offset
open Utils
open Domain_sig

(* =========================================================== *)
(* Modules INDUCTIVE DEF                                       *)
(* =========================================================== *)
(*                                  Last modified: AT 06/21/11 *)


(* =========================================================== *)
(* Module Top_list                                             *)
(* =========================================================== *)
(*   a.tl(d) := { a==0 | emp }                                 *)
(*              { a!=0 | a@n->b * a@p-> c * a@t->d * b.tl(d) } *)
(* =========================================================== *)
module TList =  
  (struct
     let name = "Topped List"

     let number_of_parameters: int = 1
     let number_of_fresh: int = 2

     let domain_offset: offset array = 
       [|RecordField("next", Zero); RecordField("prev", Zero); RecordField("top", Zero)|]

     let def_points_to_fresh: offset list = 
       [RecordField("next", Zero); RecordField("prev", Zero)]

     let def_points_to_parameters: offset list = 
       [RecordField("top", Zero)]

     (* current node -> parameters -> fresh *)
     let new_parameters: int -> int list -> int list -> int list = fun i l p -> l

   end: INDUCTIVE_DEF)

(* =========================================================== *)
(* Module DDL: doubly linked list                              *)
(* =========================================================== *)
(* a.dll(e) := { a==0 | emp }                                  *)
(*             { a!=0 | a@n->b * a@p-> e * a@t-> c * b.dll(a) }*)
(* =========================================================== *)
module DLList =  
  (struct
     let name = "Doubly Linked List"

     let number_of_parameters: int = 1
     let number_of_fresh: int = 2

     let domain_offset: offset array = 
       [|RecordField("next", Zero); RecordField("prev", Zero); RecordField("top", Zero)|]

     let def_points_to_fresh: offset list = 
       [RecordField("next", Zero); RecordField("top", Zero)]

     let def_points_to_parameters: offset list = 
       [RecordField("prev", Zero)]

     (* current node -> parameters -> fresh *)
     let new_parameters: int -> int list -> int list -> int list = fun i l p -> [i]

   end: INDUCTIVE_DEF)
