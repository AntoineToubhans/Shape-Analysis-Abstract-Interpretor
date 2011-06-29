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

       let rec aux_search = fun t l_io acc_t acc_i -> 
	 match t with
	   | D_Top -> D_Top, []
	   | Disjunction [] -> acc_t, acc_i
	   | Disjunction l_t ->
	       let t = List.hd l_t and i, o = List.hd l_io in
		 try
		   let j, t = S.search i o t in 
		   let lj, t = reduce_equalities [j] t in
		   let lj = List.map List.hd lj in
		     aux_search 
		       (Disjunction (List.tl l_t)) 
		       (List.tl l_io) 
		       (disjunction t acc_t) 
		       (List.append lj acc_i)  
		 with
		   | Top -> D_Top, []
		   | Split (b, k) ->
		       if debug then print_debug "DOMAIN: Split(%b, %i) caugth **\n" b k;
		       let t1, t2 = catch_split b k t in 
		       let lj1, t1 = reduce_equalities [i] t1 and lj2, t2 = reduce_equalities [i] t2 in
		       let lj1 = List.map List.hd lj1 and lj2 = List.map List.hd lj2 in
			 aux_search
			   (disjunction t1 (disjunction t2 (Disjunction (List.tl l_t))))
			   (List.append 
			      (List.map (fun x-> x, o) lj1) 
			      (List.append (List.map (fun x-> x, o) lj2) (List.tl l_io)))
			   acc_t acc_i


       let search: t -> (int * offset) list -> t * int list = fun t l_io ->
	 if debug then print_debug "DOMAIN: search for [ %s] in t....\n"
	   (List.fold_left (fun s (i, o)-> Printf.sprintf "%s%i%s, " s i (pp_offset o)) "" l_io);
	 let t, l_i = aux_search t l_io bottom [] in
	   if debug then print_debug "DOMAIN: found [ %s]\n"
	     (List.fold_left (fun s i-> Printf.sprintf "%s%i, " s i) "" l_i);
	   t, l_i

       let rec aux_search2 = fun t l_io l_inv acc_t acc_i acc_inv -> 
	 match t with
	   | D_Top -> D_Top, [], []
	   | Disjunction [] -> acc_t, acc_i, acc_inv
	   | Disjunction l_t ->
	       let t = List.hd l_t and i, o = List.hd l_io and l_inv_t = List.hd l_inv in
		 try
		   let j, t = S.search i o t in 
		   let ljinv, t = reduce_equalities (j::l_inv_t) t in
		   let lj = List.map List.hd ljinv and ll_inv_t = List.map List.tl ljinv in
		     aux_search2 
		       (Disjunction (List.tl l_t)) 
		       (List.tl l_io) 
		       (List.tl l_inv) 
		       (disjunction t acc_t) 
		       (List.append lj acc_i)  
		       (List.append ll_inv_t acc_inv)
		 with
		   | Top -> D_Top, [], []
		   | Split (b, k) ->
		       if debug then print_debug "DOMAIN: Split(%b, %i) caugth **\n" b k;
		       let t1, t2 = catch_split b k t in 
		       let ljinv1, t1 = reduce_equalities (i::l_inv_t) t1 
		       and ljinv2, t2 = reduce_equalities (i::l_inv_t) t2 in
		       let lj1 = List.map List.hd ljinv1 
		       and lj2 = List.map List.hd ljinv2 
		       and ll_inv_t1 = List.map List.tl ljinv1 
		       and ll_inv_t2 = List.map List.tl ljinv2 in
			 aux_search2
			   (disjunction t1 (disjunction t2 (Disjunction (List.tl l_t))))
			   (List.append 
			      (List.map (fun x-> x, o) lj1) 
			      (List.append (List.map (fun x-> x, o) lj2) (List.tl l_io)))
			   (List.append ll_inv_t1
			      (List.append ll_inv_t2 (List.tl l_inv)))
			   acc_t acc_i acc_inv

       let search2: t -> (int * offset) list -> int list list -> t * int list * int list list = fun t l_io l_inv ->
	 if debug then print_debug "DOMAIN: search2 for [ %s] in t....\n"
	   (List.fold_left (fun s (i, o)-> Printf.sprintf "%s%i%s, " s i (pp_offset o)) "" l_io);
	 let t, l_i, l_inv = aux_search2 t l_io l_inv bottom [] [] in
	   if debug then print_debug "DOMAIN: (s2) found [ %s]\n"
	     (List.fold_left (fun s i-> Printf.sprintf "%s%i, " s i) "" l_i);
	   t, l_i, l_inv

       let rec get_sc_hvalue: sc_hvalue -> int -> t -> t * (int * offset) list = fun e i t ->
	 if debug then print_debug "DOMAIN: [rec] get_sc_hvalue %s\n" (sc_hvalue2str e);
	 match e with
	   | Var _ -> 
	       begin 
		 match t with
		   | D_Top -> t, []
		   | Disjunction l_t -> t, List.map (fun _-> i, Zero) l_t
	       end
	   | ArrayAccess(k, e) ->
	       let t, l_io = get_sc_hvalue e i t in
		 t, List.map (fun (j, o) -> j , ArrayRange(k, o)) l_io
	   | FieldAccess(f, e) ->
	       let t, l_io = get_sc_hvalue e i t in
		 t, List.map (fun (j, o) -> j , RecordField(f, o)) l_io
	   | Deref e ->
	       let t, l_io = get_sc_hvalue e i t in
	       let t, l_i = search t l_io in
		 t, List.map (fun j -> j, Zero) l_i	    

	
       let get_sc_vvalue: sc_vvalue -> int -> offset list -> t -> t * int list = fun e i l_o_malloc t ->
	 if debug then print_debug "DOMAIN: get_sc_vvalue %s\n" (sc_vvalue2str e);	 
	 match t, e with
	   | D_Top, _ -> 
	       D_Top, []
	   | Disjunction l_t, FloatConst _ | Disjunction l_t, IntConst _ ->
	       let l_i, l_t = List.split (List.map (fun t -> S.create_fresh_node t) l_t) in
		 Disjunction l_t, l_i
	   | Disjunction l_t, Null ->
	       t, List.map (fun _->0) l_t
	   | Disjunction l_t, Malloc _ ->
	       let l_i, l_t = List.split (List.map (fun t -> S.malloc l_o_malloc t) l_t) in
		 Disjunction l_t, l_i
	   | Disjunction l_t, Address e ->
	       let t, l_io = get_sc_hvalue e i t in
		 t, List.map (fun (j, o)-> j) l_io 
		
       let mutation: offset list -> offset list -> int -> int -> sc_assignment -> t -> t = 
	 fun l_offset_mut l_o_malloc i j (la, ra) t -> 
	   if debug then print_debug "DOMAIN: mutation %s\n" (sc_assignment2str (la, ra));	 
	   let t, in_mut = 
	     match ra with
	       | HValue e -> 
		   let t, l_io = get_sc_hvalue e j t in
		   let l_o = List.map (fun (x,y)->y) l_io in
		     List.fold_left
		       (fun (t, l) o -> 
			  let l_io = List.combine (List.map List.hd l) l_o in
			  let t, li, l = search2 t (List.map (fun (i,oo)->i, appendOffset o oo) l_io) l in
			    t, List.map2 (fun x y -> (List.hd y)::x::(List.tl y)) li l)
		       (t, (List.map (fun (i, o)->[i]) l_io)) l_offset_mut
	       | VValue e -> 
		   let t, l_i = get_sc_vvalue e j l_o_malloc t in
		     t, List.map (fun x->[x]) l_i in
	   let t, l_io = get_sc_hvalue la i t in
	     match t with
	       | D_Top -> D_Top 
	       | Disjunction l_t -> 
		   Disjunction 
		     (List.map2 
			(fun (t, (i, oo)) li ->
			   List.fold_left2
			     (fun t o j -> S.mutate i oo j t)
			     t l_offset_mut li) 
			(List.combine l_t l_io) in_mut)    
		
		   
       let filter: int -> int -> sc_cond -> t -> t = fun i j cond t -> t

       let pp: t -> string = fun t -> 
	 let s = 
	   match t with
	     | Disjunction l ->
		 let it = ref 0 in
		   List.fold_left 
		     (fun s t -> it:=!it+1;Printf.sprintf "%s**t%i:**\n%s" s !it (S.pp t))
		     (Printf.sprintf "Disjunction: t1 || ... || t%i\n" (List.length l))
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

let t: D.t = D.Disjunction [t]

let x={var_name="x"; var_type=PointerTo(Struct "dll"); var_uniqueId=1;}
let a: sc_assignment = Var x, HValue (FieldAccess("next",Deref(Var x)))

let fields = [RecordField("next", Zero);RecordField("prev", Zero);RecordField("top", Zero)]

let t = D.mutation [Zero] [] 1 1 a t

let _ = 
  Printf.printf "%s" (D.pp t)


