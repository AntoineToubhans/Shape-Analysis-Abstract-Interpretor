open Offset
open Utils
open Domain_sig
open Neq_pred_domain
open SL_graph_domain
open Inductive_def
open SL_domain
open Simple_C_syntax

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

       let rec get_sc_hvalue: sc_hvalue -> int -> offset list -> S.t -> (S.t * int * offset) list = fun e i l t ->
	 if debug then print_debug "DOMAIN: [rec] get_sc_value %s\n" (sc_hvalue2str e);
	 try
	   match e with
	     | Var _ -> 
		 [(t, i, Zero)]
	     | ArrayAccess(k, e) ->
		 List.map (fun (t, j, o) -> (t, j , ArrayRange(k, o))) (get_sc_hvalue e i l t)
	     | FieldAccess(f, e) ->
		 List.map (fun (t, j, o) -> (t, j , RecordField(f, o))) (get_sc_hvalue e i l t)
	     | Deffer e ->
		 List.map (fun (t, j, o) -> let j, t = S.search j o t in (t, j, Zero)) (get_sc_hvalue e i l t)
	     | Malloc size ->	       
		 let j, t = S.malloc l t in [(t, j, Zero)]
	 with
	   | Split (b, j) ->
	       let t1, t2 = if b then S.case_inductive_forward j t else S.case_inductive_backward j t in 
		 List.append (get_sc_hvalue e i l t1) (get_sc_hvalue e i l t2)

       let mutation: offset list -> int -> int -> sc_assignment -> t -> t = fun l i j assign t -> t

       let filter: int -> int -> sc_cond -> t -> t = fun i j cond t -> t

       let pp: t -> string = fun t -> 
	 let s = 
	   match t with
	     | Disjunction l ->
		 let it = ref 0 in
		   List.fold_left 
		     (fun s t -> it:=!it+1;Printf.sprintf "%s**t%i:**\n%s" s !it (S.pp t))
		     (Printf.sprintf "Disjunction: t1 /\ ... /\ t%i\n" (List.length l))
		     l
	     | Top -> 
		 "Top\n"
	 in
	   Printf.sprintf 
	     "*****-------Print DOMAIN --------*****\n%s" s

     end: DOMAIN) 
