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
    struct
  
       type t = 
	 | Disjunction of S.t list
	 | D_Top
	 
       let top: t = D_Top        
       let bottom: t = Disjunction []

       let is_top: t -> bool = fun t ->
	 match t with
	   | D_Top -> true
	   | _ -> false

       let is_bottom: t -> bool  = fun t ->
	 match t with
	   | Disjunction l -> l==[]
	   | _ -> false

       let disjunction: t -> t -> t = fun t u ->
	 match t, u with
	   | D_Top, _ | _, D_Top -> D_Top
	   | Disjunction lt, Disjunction lu -> Disjunction (List.append lt lu)

       let catch_split b i t = 
	 if b then S.case_inductive_forward i t else S.case_inductive_backward i t

       let rec reduce_equalities: S.t -> t = fun t ->
	 if debug then print_debug "DOMAIN: [rec] reduce_equalities \n";
	 try
	   match S.reduce_equalities_one_step t with
	     | None -> Disjunction [t]
	     | Some t -> reduce_equalities t
	 with
	   | Bottom -> bottom
	   | Top -> top
	   | Split(b, i) ->
	       let t1, t2 = catch_split b i t in
		 disjunction (reduce_equalities t1) (reduce_equalities t1)	   

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
	       if debug then print_debug "DOMAIN: Split(%b, %i) caugth **\n" b j;
	       let t1, t2 = catch_split b j t in 
	       let t1 = reduce_equalities t1 and t2 = reduce_equalities t2 in
		 match t1, t2 with
		   | D_Top, _ | _, D_Top -> 
		       raise Top (* this should not happen *)
		   | Disjunction lt1, Disjunction lt2 ->
		       let ffold = fun res t ->
			 if S.is_bottom t then res else 
			   List.append res (get_sc_hvalue e i l t) in
			 List.fold_left ffold 
			   (List.fold_left ffold [] lt1) lt2

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
	     | D_Top -> 
		 "Top\n"
	 in
	   Printf.sprintf 
	     "*****-------Print DOMAIN --------*****\n%s" s

     end

module S = MAKE_SL_DOMAIN(DLList)

let g = S.G.empty
let p = S.P.empty
let p = S.P.add_neq 2 4 p

let g = S.G.add_edge 1 Zero 2 g
let g = S.G.add_inductive 2 {target=3; source_parameters=[0]; target_parameters=[5]; length=0} g
let g = S.G.add_inductive 3 {target=4; source_parameters=[5]; target_parameters=[6]; length=0} g
let g = S.G.add_edge 4 (RecordField ("prev", Zero)) 6 g

let t: S.t = S.mk g p

module D = MAKE_DOMAIN(S)

let x={var_name="x"; var_type=PointerTo(Struct "dll"); var_uniqueId=1;}

let l = D.get_sc_hvalue (Deffer(FieldAccess("next",Deffer(Var x)))) 1 [] t

let _ = 
  List.iter
    (fun (t, i , o)-> Printf.printf "%i%s:\n%s" i (pp_offset o) (S.pp t)) l


