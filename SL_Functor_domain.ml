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

       (* reduce_equalities i t ---> [i1;...;in], t1/\.../\tn *)
       let rec reduce_equalities: int list -> S.t -> int list list * t = fun l_pt t ->
 	 if debug then print_debug "DOMAIN: [rec] reduce_equalities \n";
	 try
	   match S.reduce_equalities_one_step t l_pt with
	     | _, None -> [l_pt], Disjunction [t]
	     | l_pt, Some t -> reduce_equalities l_pt t
	 with
	   | Bottom -> [], bottom
	   | Top -> [], top
	   | Split(b, i) ->
	       let t1, t2 = catch_split b i t in
	       let ll_pt1, lt1 = reduce_equalities l_pt t1 and ll_pt2, lt2 = reduce_equalities l_pt t2 in 
		 List.append ll_pt1 ll_pt2, disjunction lt1 lt2	   


       let rec get_sc_hvalue: sc_hvalue -> int -> S.t -> (S.t * int * offset) list = fun e i t ->
	 if debug then print_debug "DOMAIN: [rec] get_sc_hvalue %s\n" (sc_hvalue2str e);	 
	 match e with
	   | Var _ -> 
	       [(t, i, Zero)]
	   | ArrayAccess(k, e) ->
	       List.map (fun (t, j, o) -> (t, j , ArrayRange(k, o))) (get_sc_hvalue e i t)
	   | FieldAccess(f, e) ->
	       List.map (fun (t, j, o) -> (t, j , RecordField(f, o))) (get_sc_hvalue e i t)
	   | Deref e ->
	       let lrec = ref (get_sc_hvalue e i t) and lres = ref [] in
		 while !lrec != [] do
		   let t, j, o = List.hd !lrec in
		     lrec:= List.tl !lrec;
		     try
		       let j, t = S.search j o t in 
		       let lj, t = reduce_equalities [j] t in
			 match t with
			   | D_Top -> raise Top (* this should not happen *)
			   | Disjunction lt ->
			       List.iter2 (fun t j -> lres:= (t, List.hd j, Zero)::(!lres)) lt lj 
		     with
		       | Split (b, k) ->
			   if debug then print_debug "DOMAIN: Split(%b, %i) caugth **\n" b j;
			   let t1, t2 = catch_split b k t in 
			   let lj1, t1 = reduce_equalities [j] t1 and lj2, t2 = reduce_equalities [j] t2 in
			     match t1, t2 with
			       | D_Top, _ | _, D_Top -> 
				   raise Top (* this should not happen *)
			       | Disjunction lt1, Disjunction lt2 ->
				   lrec:= List.append 
				     (List.map2 (fun t j ->(t, List.hd j, o)) lt1 lj1) 
				     (List.append (List.map2 (fun t j->(t, List.hd j, o)) lt2 lj2) !lrec);
		 done; !lres
	
       let get_sc_vvalue: sc_vvalue -> int -> offset list -> S.t -> (S.t * int) list = fun e i l t ->
	 if debug then print_debug "DOMAIN: get_sc_vvalue %s\n" (sc_vvalue2str e);	 
	 match e with
	   | FloatConst _ | IntConst _ ->
	       let j, t = S.create_fresh_node t in [t, j]
	   | Null ->
	       [t, 0]
	   | Malloc _ ->	       
	       let j, t = S.malloc l t in [(t, j)] 
	   | Address e ->
	       List.map (fun (t, j, o)-> t, j) (get_sc_hvalue e i t) 
				    
       let mutation: offset list -> offset list -> int -> int -> sc_assignment -> t -> t = 
	 fun l_offset_mut l_offset_if_malloc i j (e1, e2) t -> 
	   if debug then print_debug "DOMAIN: mutation %s\n" (sc_assignment2str (e1, e2));	 
	   match e2 with
	     | HValue e2 ->
		 t
	     | VValue e2 ->
		 let l_t2 = get_sc_vvalue e2 j l_offset_if_malloc t in
		   t
		 

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

let l = D.get_sc_hvalue (Deref(FieldAccess("next",Deref(Var x)))) 1 t

let _ = 
  List.iter
    (fun (t, i , o)-> Printf.printf "%i%s:\n%s" i (pp_offset o) (S.pp t)) l


