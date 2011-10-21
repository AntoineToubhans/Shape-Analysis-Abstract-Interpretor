open Offset
open Utils
open Domain_sig
open Neq_pred_domain
open SL_graph_domain
open Inductive_def
open SL_domain
open Simple_C_syntax

(* =========================================================== *)
(* Module DIS_Domain Functor                                   *)
(* =========================================================== *)
(*                                        Created: AT 06/23/11 *)
(*                                  Last modified: AT 07/26/11 *)

let error(s: string) = failwith (Printf.sprintf "DIS_DOMAIN_ERROR: %s" s)

module MAKE_DIS_DOMAIN =
  functor (S: SL_DOMAIN) -> functor (O: OPTION) -> 
    (struct

       let debug = O.debug

       let print_debug x = 
	 Utils.print_debug ("DIS_DOMAIN:\t" ^^ x) 

       type t = 
	 | Disjunction of S.t list
	 | D_Top

       let init: t = Disjunction [S.empty]
	 
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
	 if debug then print_debug "Split(%b, %s) caugth **\n" b (Node_ID.pp i);
	 if b then S.case_inductive_forward i t else S.case_inductive_backward i t

       (* reduce_equalities i t ---> [i1;...;in], t1/\.../\tn *)
       let rec reduce_equalities: Node_ID.t list -> S.t -> Node_ID.t list list * t = fun l_pt t ->
 	 if debug then print_debug "[rec] reduce_equalities \n";
	 try
	   match S.reduce_equalities_one_step t with
	     | None -> [l_pt], Disjunction [t]
	     | Some(i,j,t) -> 
		 reduce_equalities 
		   (List.map (Node_ID.fusion i j) l_pt) t
	 with
	   | Bottom -> if debug then print_debug "Bottom caugth **\n"; [], bottom
	   | Top -> if debug then print_debug "Top caugth **\n"; [], top
	   | Split(b, i) ->
	       let lt = catch_split b i t in
	       let l = List.map (reduce_equalities l_pt) lt in
		 List.fold_left
		   (fun (ll_pt_r,lt_r) (ll_pt,lt) -> List.append ll_pt ll_pt_r, disjunction lt lt_r)
		   ([], bottom) l

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
		   | Top -> if debug then print_debug "Top caugth **\n"; D_Top, []
		   | Split (b, k) ->
		       let lt = catch_split b k t in 
		       let l = List.map (reduce_equalities [i]) lt in
		       let t, l_io = 
			 List.fold_left
			   (fun (t_r, l_io_r) (lj, t) -> 
			      disjunction t t_r, 
			      List.append (List.map (fun x -> List.hd x, o) lj) l_io_r)
			   (Disjunction (List.tl l_t), List.tl l_io) l in
			 aux_search t l_io acc_t acc_i
			   

       let search: t -> (Node_ID.t * offset) list -> t * Node_ID.t list = fun t l_io ->
	 if debug then print_debug "search for [ %s] in t....\n"
	   (List.fold_left (fun s (i, o)-> Printf.sprintf "%s%s%s " s (Node_ID.pp i) (pp_offset o)) "" l_io);
	 let t, l_i = aux_search t l_io bottom [] in
	   if debug then print_debug "found [ %s]\n"
	     (List.fold_left (fun s i-> Printf.sprintf "%s%s " s (Node_ID.pp i)) "" l_i);
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
		   | Top -> if debug then print_debug "Top caugth **\n"; D_Top, [], []
		   | Split (b, k) ->
		       let lt = catch_split b k t in 
		       let l = List.map (reduce_equalities (i::l_inv_t)) lt in
		       let t, l_io, l_inv = 
			 List.fold_left
			   (fun (t_r, l_io_r, l_inv_r) (lj, t) -> 
			      disjunction t t_r, 
			      List.append (List.map (fun x -> List.hd x, o) lj) l_io_r,
			      List.append (List.map List.tl lj) l_inv_r)
			   (Disjunction (List.tl l_t), List.tl l_io, List.tl l_inv) l in
			 aux_search2 t l_io l_inv acc_t acc_i acc_inv

       let search2: t -> (Node_ID.t * offset) list -> Node_ID.t list list -> 
	 t * Node_ID.t list * Node_ID.t list list = fun t l_io l_inv ->
	   if debug then print_debug "search2 for [ %s] in t....\n"
	     (List.fold_left (fun s (i, o)-> Printf.sprintf "%s%s%s " s (Node_ID.pp i) (pp_offset o)) "" l_io);
	   let t, l_i, l_inv = aux_search2 t l_io l_inv bottom [] [] in
	     if debug then print_debug "(s2) found [ %s]\n"
	       (List.fold_left (fun s i-> Printf.sprintf "%s%s " s (Node_ID.pp i)) "" l_i);
	     t, l_i, l_inv
	       
       let union: t -> t -> t = fun t1 t2 ->
	 if debug then print_debug "computing [Union]\n";
	 match t1, t2 with
	   | D_Top, _ | _, D_Top -> D_Top
	   | Disjunction l_t1, Disjunction l_t2 -> 
	       let rec insert acc l_t t = 
		 match l_t with
		   | [] -> t::acc
		   | t1::l_t -> 
		       begin 
			 match S.union t t1 with
			   | Some t -> 
			       t::(List.append l_t acc)
			   | None -> 
			       insert (t1::acc) l_t t 
		       end in
(*		       if S.is_include t t1 then
			 t1::(List.append l_t acc)
		       else if S.is_include t1 t then
			 insert acc l_t t
		       else
			 insert (t1::acc) l_t t in *)
		 Disjunction
		   (List.fold_left (insert []) l_t1 l_t2)

       (* Widening from canonicalization:         *)
       (*  Widening(a, b):= Union(can(a), can(b)) *)
       let widening: t -> t -> t = fun t1 t2 ->
	 if debug then print_debug "computing [Widening]\n";
	 match t1, t2 with
	   | D_Top, _ | _, D_Top -> D_Top
	   | Disjunction l_t1, Disjunction l_t2 -> 
	       let rec insert acc l_t t = 
		 match l_t with
		   | [] -> t::acc
		   | t1::l_t -> 
		       begin 
			 match S.union t t1 with
			   | Some t -> 
			       t::(List.append l_t acc)
			   | None -> 
			       insert (t1::acc) l_t t 
		       end in
	       let l_t = 
		 List.fold_left (fun acc t -> insert [] acc (S.canonicalize t)) [] l_t1 in 
		 Disjunction
		   (List.fold_left (fun l_t t -> insert [] l_t (S.canonicalize t)) l_t l_t2) 
		 

       (* sound, but can be easely improved ... *)
       let is_include: t -> t -> bool = fun t1 t2 ->	 
	 if debug then print_debug "checking [inclusion]\n";
	 match t1, t2 with
	   | _, D_Top -> 
	       true
	   | D_Top, _ -> false
	   | Disjunction l_t1, Disjunction l_t2 -> 
	       List.for_all 
		 (fun t1 -> 
		    List.exists 
		      (fun t2 -> S.is_include t1 t2) l_t2) 
		 l_t1

       let var_alloc: offset list -> t -> t* Node_ID.t = fun l_o t -> 
	 if debug then print_debug "var_alloc [%s ]...\n" 
	   (List.fold_left (fun s o -> Printf.sprintf "%s %s" s (pp_offset o)) "" l_o);
	 match t with
	   | D_Top -> D_Top, Node_ID.Id 0
	   | Disjunction l_t ->
	       let i = List.fold_left (fun n tt -> max n (Node_ID.max (S.next tt))) 0 l_t in
	       let i = Node_ID.All i in
		 if debug then print_debug "[var_alloc] mem found: %s\n" (Node_ID.pp i);
		 let t = Disjunction (List.map (fun tt -> S.var_alloc i l_o tt) l_t) in
		   t, i

       let rec get_sc_hvalue: sc_hvalue -> Node_ID.t -> t -> t * Node_ID.t list * offset = fun e i t ->
	 if debug then print_debug "[rec] get_sc_hvalue %s\n" (sc_hvalue2str e);
	 let t, l_i, o = 
	   match e with
	     | Var _ -> 
		 begin 
		   match t with
		     | D_Top -> t, [], Zero
		     | Disjunction l_t -> t, List.map (fun _-> i) l_t, Zero
		 end
	     | ArrayAccess(k, e) ->
		 let t, l_i, o = get_sc_hvalue e i t in
		   t, l_i, ArrayRange(k, o)
	     | FieldAccess(f, e) ->
		 let t, l_i, o = get_sc_hvalue e i t in
		   t, l_i, RecordField(f, o)
	     | Deref e ->
		 let t, l_i, o = get_sc_hvalue e i t in
		 let t, l_i = search t (List.map (fun i->i, o) l_i) in
		   t, l_i, Zero in
	   if debug then print_debug "found sc_hvalue %s [ %s]%s\n" (sc_hvalue2str e)
	     (List.fold_left (fun s i->Printf.sprintf "%s%s " s (Node_ID.pp i)) "" l_i) (pp_offset o);
	   t, l_i, o
	
       let rec get_sc_hvalue2: sc_hvalue -> Node_ID.t -> t -> Node_ID.t list list -> 
	 t * Node_ID.t list * offset * Node_ID.t list list = fun e i t l_inv ->
	   if debug then print_debug "[rec] get_sc_hvalue2 %s\n" (sc_hvalue2str e);
	   let t, l_i, o, l_inv = 
	     match e with
	       | Var _ -> 
		   begin 
		     match t with
		       | D_Top -> t, [], Zero, []
		       | Disjunction l_t -> t, List.map (fun _-> i) l_t, Zero, l_inv
		   end
	       | ArrayAccess(k, e) ->
		   let t, l_i, o, l_inv = get_sc_hvalue2 e i t l_inv in
		     t, l_i, ArrayRange(k, o), l_inv
	       | FieldAccess(f, e) ->
		   let t, l_i, o, l_inv = get_sc_hvalue2 e i t l_inv in
		     t, l_i, RecordField(f, o), l_inv
	       | Deref e ->
		   let t, l_i, o, l_inv = get_sc_hvalue2 e i t l_inv in
		   let t, l_i, l_inv = search2 t (List.map (fun i->i, o) l_i) l_inv in
		     t, l_i, Zero, l_inv in
	     if debug then print_debug "found sc_hvalue2 %s [ %s]%s\n" (sc_hvalue2str e)
	       (List.fold_left (fun s i->Printf.sprintf "%s%s " s (Node_ID.pp i)) "" l_i) (pp_offset o);
	     t, l_i, o, l_inv
	
       let get_sc_vvalue: sc_vvalue -> Node_ID.t -> offset list -> t -> t * Node_ID.t list = fun e i l_o_malloc t ->
	 if debug then print_debug "get_sc_vvalue %s\n" (sc_vvalue2str e);
	 let t, l_i = 
	   match t, e with
	     | D_Top, _ -> 
		 D_Top, []
	     | Disjunction l_t, FloatConst _ | Disjunction l_t, IntConst _ ->
		 let l_i, l_t = List.split (List.map (fun t -> S.create_fresh_node t) l_t) in
		   Disjunction l_t, l_i
	     | Disjunction l_t, Null ->
		 t, List.map S.zero l_t
	     | Disjunction l_t, Malloc _ ->
		 let l_i, l_t = List.split (List.map (fun t -> S.malloc l_o_malloc t) l_t) in
		   Disjunction l_t, l_i
	     | Disjunction l_t, Address e ->
		 let t, l_i, o = get_sc_hvalue e i t in
		   if o==Zero then 
		     t, l_i  
		   else (* feature not suported: &x->n *)
		     top, [] in
	   if debug then print_debug "found sc_vvalue %s [ %s]\n" (sc_vvalue2str e)
	     (List.fold_left (fun s i->Printf.sprintf "%s%s " s (Node_ID.pp i)) "" l_i);
	   t, l_i
		
       let mutation: offset list -> offset list -> Node_ID.t -> Node_ID.t -> sc_assignment -> t -> t = 
	 fun l_offset_mut l_o_malloc i j (la, ra) t -> 
	   if debug then print_debug "mutation %s\n" (sc_assignment2str (la, ra));	 
	   (* first we take care of rigth hande side of the assignment 
	      and get the nodes which will be copied *)
	   let t, in_mut = 
	     match ra with
	       | HValue e -> 
		   let t, l_i, off = get_sc_hvalue e j t in
		   let t, l = 
		     List.fold_left
		       (fun (t, l) o -> 
			  let o = appendOffset o off in
			  let l_io = List.map (fun i->i,o) (List.map List.hd l) in
			  let t, li, l = search2 t l_io l in
			    t, List.map2 (fun x y -> (List.hd y)::x::(List.tl y)) li l)
		       (t, (List.map (fun i->[i]) l_i)) (List.rev l_offset_mut) in
		     t, List.map List.tl l
	       | VValue e -> 
		   let t, l_i = get_sc_vvalue e j l_o_malloc t in
		     t, List.map (fun x->[x]) l_i in
	   (* now we deal with left hand side of the assignment *)
	   let t, l_i, o, in_mut = get_sc_hvalue2 la i t in_mut in
	     (* we make appear the edges we wanna update *)
	   let l_offset_mut = List.map (fun oo-> appendOffset oo o) l_offset_mut in
	   let t, l = 
	     List.fold_left
	       (fun (t, l) o -> 
		  let l_io = List.map (fun i->i, o) (List.map List.hd l) in
		  let t, _, l = search2 t l_io l in t, l)
	       (t, List.map2 (fun x y->x::y) l_i in_mut) l_offset_mut in
	   let l_i = List.map List.hd l and in_mut = List.map List.tl l in
	     match t with 
	       | D_Top -> D_Top 
	       | Disjunction l_t -> 
		   Disjunction
		     (map3 
			(fun t i l -> 
			   List.fold_left2 
			     (fun t oo j -> S.mutate i oo j t)
			     t l_offset_mut l)
			l_t l_i in_mut)		
      
       let aux_filter: (Node_ID.t list * Node_ID.t list) list -> t -> t * t = fun l t -> 
	 if debug then print_debug "perform filtering...\n";
	 match t with
	   | D_Top -> top, top 
	   | Disjunction l_t ->
	       List.fold_left2 
		 (fun (t1, t2) tt (l_i, l_j) ->
		    let tt1 = 
		      List.fold_left2
			(fun tt1 i j -> S.request_eq i j tt1) tt l_i l_j
		    and lt2 = 
		      List.fold_left2
			(fun lt i j -> 
			   if i=j then lt else (S.request_neq i j tt)::lt) 
			[] l_i l_j in
		    let _, tt1 = reduce_equalities [] tt1 
		    and tt2 = Disjunction lt2 in
		      disjunction t1 tt1, disjunction t2 tt2)
		 (bottom, bottom) l_t l


       let filter: offset list -> Node_ID.t -> Node_ID.t -> sc_cond -> t -> t * t = fun l_o i j cond t -> 
	 if debug then print_debug "filter %s\n" (sc_cond2str cond);	 
	 let  b, e1, e2 = 
	   match cond with
	     | Eq(e1, e2) -> true, e1, e2
	     | Neq(e1, e2) -> false, e1, e2 in
	 let t1, t2 = 
	   match e1, e2, i, j with
	     | HValue e1, HValue e2, _, _ -> 
		 let t, l_i, oi = get_sc_hvalue e1 i t in
		 let t, l = List.fold_left
		   (fun (t, l) o -> 
		      let o = appendOffset o oi in
		      let l_io = List.map (fun i->i,o) (List.map List.hd l) in
		      let t, l_i, l = search2 t l_io l in
			t, List.map2 (fun x y -> (List.hd y)::x::(List.tl y)) l_i l)
		   (t, List.map (fun i->[i]) l_i) l_o in
		 let t, l_j, oj, l = get_sc_hvalue2 e2 j t (List.map List.tl l) in
		 let t, l = List.fold_left
		   (fun (t, l) o -> 
		      let o = appendOffset o oj in
		      let l_jo = List.map (fun i->i,o) (List.map List.hd l) in
		      let t, l_j, l = search2 t l_jo l in
			t, List.map2 (fun x y -> (List.hd y)::x::(List.tl y)) l_j l)
		   (t, List.map2 (fun j x ->j::x) l_j l) (List.rev l_o) in
		 let rec f n l acc = if n==0 then l, acc else f (n-1) (List.tl l) ((List.hd l)::acc)
		 and n = List.length l_o in 
		  aux_filter (List.map (fun l -> f n (List.tl l) []) l) t		   
	     | HValue e1, VValue e2, i, j | VValue e2, HValue e1, j, i ->
		 begin 
		   match e2 with
		     | IntConst _ | FloatConst _ -> 
			 (* I can't handle this, 
			    at least till I don't deal with cofibred domain *)
			 t, t
		     | Null -> 
			 let t, l_i, o = get_sc_hvalue e1 i t in
			 let t, l_i = search t (List.map (fun i->i, o) l_i) in
			 let l = match t with
			   | D_Top -> []
			   | Disjunction l_t ->
			       List.map2 (fun t i-> [S.zero t], [i]) l_t l_i in
			   aux_filter l t
		     | Address e2 ->
			 let t, l_i, oi = get_sc_hvalue e1 i t in
			   (* l_o MUST be [Zero] *)
			 let t, l_i = search t (List.map (fun i->i, oi) l_i) in
			 let t, l_j, oj, l = get_sc_hvalue2 e2 j t (List.map (fun i -> [i]) l_i) in
			   if Offset.equals oj Zero then
			     aux_filter (List.map2 (fun x y -> [x], y) l_j l) t
			   else (* can't handle this... *)
			     t, t
		     | _ -> 
			 error (Printf.sprintf "Inconsistent condition %s" (sc_cond2str cond))
		 end		    
	     | VValue e1, VValue e2, _, _ ->
		 begin
		   match e1, e2 with
		     | IntConst x, IntConst y ->
			 if x=y then t, bottom else bottom, t
		     | FloatConst x, FloatConst y -> 
			 if x=y then t, bottom else bottom, t
		     | Null, Null ->
			 t, bottom 
		     | Address e1, Address e2 -> 
			 begin
			   let t, l_i, oi = get_sc_hvalue e1 i t in
			   let t, l_j, oj, l = get_sc_hvalue2 e2 j t (List.map (fun i->[i]) l_i) in
			     if Offset.equals oi oj then
			       let l = List.map2 (fun li j -> li, [j]) l l_j in
				 aux_filter l t
			     else t, t (* can't handle this for now *)
			 end
		     | _ -> 
			 error (Printf.sprintf "Inconsistent condition %s" (sc_cond2str cond))
		 end in
	   if b then t1, t2 else t2, t1


       let pp: t -> unit = fun t -> 
	 match t with
	   | Disjunction [] ->
	       O.XML.printf "_|_ (Bottom)<br/>\n"
	   | Disjunction l ->
	       O.XML.print_h3 "Disjunction of %i cases" (List.length l);
	       O.XML.printf "<div class=\"box_E\">\n";
	       let it = ref 0 in
		 List.iter 
		   (fun t -> 
		      it:=!it+1; 
		      O.XML.printf "<div class=\"fl box_D\" onclick=\"unfold(this)\">\n";
		      O.XML.print_center "--- t%i ---" !it;
		      O.XML.printf "<div style=\"display:none;\">";
		      S.pp t;
		      O.XML.printf "</div></div>\n")
		   l;
		 O.XML.printf "</div>\n"
	   | D_Top ->  
	       O.XML.printf "Top<br/>\n"


       (**************** spec functions *********************)
       let forget_inductive_length: t -> t = fun t -> 
      	 if debug then print_debug "spec [FORGET INDUCTIVE LENGTH]\n";
	 match t with
	   | D_Top -> D_Top
	   | Disjunction l_t ->
	       Disjunction (List.map S.forget_inductive_length l_t)

       let canonicalize: t -> t = fun t ->
      	 if debug then print_debug "spec [CANONICALIZE]\n";
	 match t with
	   | D_Top -> D_Top
	   | Disjunction l_t ->
	       Disjunction (List.map S.canonicalize l_t)

    end: DIS_DOMAIN)
(*
module S = MAKE_SL_DOMAIN(DLList)

let g = S.G.empty
let p = S.P.empty

let g = S.G.add_edge 1 (RecordField("a", Zero)) 2 g
let g = S.G.add_inductive 2 {target=3; source_parameters=[0]; target_parameters=[0]; length=5} g

let t: S.t = S.mk g p 

module D = MAKE_DIS_DOMAIN(S)

let t: D.t = D.Disjunction [t]

let x={var_name="x"; var_type=PointerTo(Struct "dll"); var_uniqueId=1;}
let a: sc_assignment = Var x, HValue (FieldAccess("next",Deref(Var x)))
let a2: sc_assignment = Deref (Var x), HValue (Deref(FieldAccess("next",Deref(Var x))))

let fields = [RecordField("next", Zero);RecordField("prev", Zero);RecordField("top", Zero)]

let c = Eq(HValue(FieldAccess("a", Var x)), VValue Null)

let t1, t2 = D.filter [Zero] 1 0 c t 

let _ = 
  Printf.printf "%s" (D.pp t);
  Printf.printf "%s" (D.pp t1);
  Printf.printf "%s" (D.pp t2)


*)
