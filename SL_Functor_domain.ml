open Offset
open Utils
open Domain_sig
open Neq_pred_domain
open SL_graph_domain
open Inductive_def
open SL_domain

(* =========================================================== *)
(* Module Domain Functor                                       *)
(* =========================================================== *)
(*                                        Created: AT 06/23/11 *)
(*                                  Last modified: AT 06/23/11 *)

let error(s: string) = failwith (Printf.sprintf "DOMAIN_ERROR: %s" s)

module MAKE_DOMAIN =
  functor (S: SL_DOMAIN) -> 
    (struct
  
       type t = 
	 | Disjunction of S.t list
	 | Top
	 
       let top: t = Top        
       let bottom: t = Disjunction []
    
       (* mut [o1, ..on] (a, o) (b, o') performs a@o:=b@o' knowing a@o MUST have [o1,..on] fields *)
       let mutation: offset list -> int -> offset -> int -> offset -> t -> t  = fun l i o1 j o2 t -> t
      
       let pp: t -> string = fun t -> ""

     end: DOMAIN) 
