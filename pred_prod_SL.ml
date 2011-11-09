open Offset
open Utils
open Domain_sig
open Neq_pred_domain
open SL_graph_domain
open Inductive_def
open SL_domain
open Simple_C_syntax

(* =========================================================== *)
(* Module SL*SL -> SL_Domain Functor                           *)
(* =========================================================== *)
(*                                        Created: AT 11/02/11 *)
(*                                  Last modified: AT 11/09/11 *)
(* =========================================================== *)
(*                                        predicative product  *)

let error(s: string) = failwith (Printf.sprintf "PRED_PROD_SL_DOMAIN_ERROR: %s" s)

module MAKE_PRED_PROD_SL_DOMAIN =
  functor (L: SL_DOMAIN) -> 
    functor (R: SL_DOMAIN) -> 
      functor (O: OPTION) -> 
(struct

   let debug = O.debug
   let name = "PRED_PROD_SL_DOMAIN"

   let print_debug x = 
     Utils.print_debug ("%s:\t" ^^ x) name

   type b = { 
     left: Node_ID.t Node_IDMap.t;
     right: Node_ID.t Node_IDMap.t;
   }
       
   type t = 
       { left: L.t;
	 right: R.t; }

   let empty = 
     { left = L.empty; 
       right = R.empty; }

   let next: t -> Node_ID.t = fun t -> 
     Node_ID.P (L.next t.left, R.next t.right)
     
   let zero: t -> Node_ID.t = fun t ->
     Node_ID.P (L.zero t.left, R.zero t.right)

   let request_eq: Node_ID.t -> Node_ID.t -> t -> t = fun i j t -> 
     if debug then print_debug "request_eq %s %s t\n" (Node_ID.pp i) (Node_ID.pp j);
     let il = Node_ID.left i and ir = Node_ID.right i 
     and jl = Node_ID.left j and jr = Node_ID.right j in
     let left = 
       match il, jl with
	 | Some il, Some jl -> L.request_eq il jl t.left
	 | _ -> t.left
     and right = 
       match ir, jr with
	 | Some ir, Some jr -> R.request_eq ir jr t.right
	 | _ -> t.right in
       { left; right; }

   let request_neq: Node_ID.t -> Node_ID.t -> t -> t = fun i j t -> 
     if debug then print_debug "request_neq %s %s t\n" (Node_ID.pp i) (Node_ID.pp j);
     let il = Node_ID.left i and ir = Node_ID.right i 
     and jl = Node_ID.left j and jr = Node_ID.right j in
     let left = 
       match il, jl with
	 | Some il, Some jl -> L.request_neq il jl t.left
	 | _ -> t.left
     and right = 
       match ir, jr with
	 | Some ir, Some jr -> R.request_neq ir jr t.right
	 | _ -> t.right in
       { left; right; }

    let reduce_equalities_one_step: t -> (Node_ID.t * Node_ID.t * t) option = fun t -> 
      if debug then print_debug "reduce_equalities_one_step t...\n";
      let l_reos = 
	try L.reduce_equalities_one_step t.left
	with | Split (b, i) -> raise (Split (b, Node_ID.Left i)) in
	match l_reos with
	  | Some (i, j, left) -> 
	      Some
		(Node_ID.Left i,
		 Node_ID.Left j,
		 { left;  right = t.right; })		 
	  | None -> 
	      begin
		let r_reos = 
		  try R.reduce_equalities_one_step t.right 
		  with | Split (b, i) -> raise (Split (b, Node_ID.Right i)) in
		  match r_reos with
		    | Some (i, j, right) -> 
			Some
			  (Node_ID.Right i,
			   Node_ID.Right j,
			   { left = t.left; right; })
		    | None -> 
			None
	      end
		
    let is_bottom: t -> bool = fun t -> 
      let b = L.is_bottom t.left || R.is_bottom t.right in
	if debug && b then print_debug "is t bottom?.....Yes\n"; 
	if debug && not b then print_debug "is t bottom?.....No\n";
	b

    let create_fresh_node: t -> Node_ID.t * t = fun t -> 
      let i, left = L.create_fresh_node t.left 
      and j, right = R.create_fresh_node t.right in
	if debug then print_debug "create_fresh_node...[%s]\n" (Node_ID.pp (Node_ID.P (i, j))); 
	Node_ID.P (i, j), { left; right; }

    let malloc: offset list -> t -> Node_ID.t * t = fun ol t -> 
      if debug then print_debug "malloc [%s ]...\n" 
	(List.fold_left (fun s o -> Printf.sprintf "%s %s" s (pp_offset o)) "" ol);
      let i, left = L.malloc ol t.left 
      and j, right = R.malloc ol t.right in
	Node_ID.P (i, j), { left; right; }

    let var_alloc: Node_ID.t -> offset list -> t -> t = fun k ol t -> 
      if debug then print_debug "var_alloc [%s ] at %s\n" 
	(List.fold_left (fun s o -> Printf.sprintf "%s %s" s (pp_offset o)) "" ol)
	(Node_ID.pp k);
      let i, j = match k with
	  (* first case should never happen *)
	| Node_ID.P (i, j) -> i, j 
	| Node_ID.All i -> Node_ID.All i, Node_ID.All i
	| _ -> error (Printf.sprintf "bad variable allocation: %s" (Node_ID.pp k)) in 
	  let left = L.var_alloc i ol t.left 
	  and right = R.var_alloc j ol t.right in
	    { left; right; }

    let case_inductive_forward: Node_ID.t -> t -> t list = fun i t -> 
      if debug then print_debug "case_inductive_forward %s t\n" (Node_ID.pp i);
      let lefts = 
	match Node_ID.left i with
	  | Some i -> L.case_inductive_forward i t.left
	  | None -> [t.left]
      and rights = 
	match Node_ID.right i with
	  | Some i -> R.case_inductive_forward i t.right
	  | None -> [t.right] in
(*	if List.length lefts = 1 && List.length rights = 1 then
	  error (Printf.sprintf "can not break inductive: there's no mapping for %i in the product" i); *)
	List.flatten
	  (List.map
	     (fun left -> List.map (fun right -> { left; right; }) rights)
	     lefts)		
 
    let case_inductive_backward: Node_ID.t -> t -> t list = fun i t -> 
      if debug then print_debug "case_inductive_backward %s t\n" (Node_ID.pp i);
      let lefts = 
	match Node_ID.left i with
	  | Some i -> L.case_inductive_backward i t.left
	  | None -> [t.left]
      and rights = 
	match Node_ID.right i with
	  | Some i -> R.case_inductive_backward i t.right
	  | None -> [t.right] in
	List.flatten
	  (List.map
	     (fun left -> List.map (fun right -> { left; right; }) rights)
	     lefts)		

    let search: Node_ID.t -> offset -> t -> Node_ID.t * t = fun k o t -> 
      if debug then print_debug "search for %s%s\n" (Node_ID.pp k) (pp_offset o);
      let i = Node_ID.left k and j = Node_ID.right k in
      let oi, left = 
	try 
	  let i, left = L.search (get i) o t.left in
	    Some i, left
	with 
	  | Top | No_value -> None, t.left 
	  | Split (b, i) -> raise (Split (b, Node_ID.Left i))
      and oj, right = 
	try
	  let j, right = R.search (get j) o t.right in
	    Some j, right
	with 
	  | Top | No_value -> None, t.right 
	  | Split (b, j) -> raise (Split (b, Node_ID.Right j)) in
      let k = match oi, oj with
	| Some i, Some j -> Node_ID.P (i, j)
	| Some i, None -> Node_ID.Left i
	| None, Some j -> Node_ID.Right j
	| _ -> raise Top in
	if debug then print_debug "[search] found: %s\n" (Node_ID.pp k);
	k, { left; right; }

    let mutate: Node_ID.t -> offset -> Node_ID.t -> t -> t = fun i o j t ->  
      if debug then print_debug "mutate\n";
      let il = Node_ID.left i and ir = Node_ID.right i 
      and jl = Node_ID.left j and jr = Node_ID.right j in
      let left = 
	match il, jl with
	  | None, _ -> raise Top
	  | Some il, Some jl ->
	      L.mutate il o jl t.left
	  | Some il, None ->
	      (* lose presicion but still sound *)
	      let jl, left = L.create_fresh_node t.left in
		L.mutate il o jl left
      and right = 
	match ir, jr with
	  | None, _ -> raise Top
	  | Some ir, Some jr ->
	      R.mutate ir o jr t.right
	  | Some ir, None ->
	      (* lose presicion but still sound *)
	      let jr, right = R.create_fresh_node t.right in
		R.mutate ir o jr right in
	{ left; right; }

    let track_node: Node_ID.t -> t -> Path.t list -> Path.t list = fun k t l -> 
      if debug then print_debug "track node %s\n" (Node_ID.pp k);
      let i = Node_ID.left k and j = Node_ID.right k in
      let l = 
	match i with
	  | Some i -> L.track_node i t.left l
	  | None -> l in
	match j with
	  | Some j -> R.track_node j t.right l
	  | None -> l

    let reduce: t -> Node_ID.t option -> Path.t -> t * Node_ID.t option = fun t k p ->
      if debug then print_debug "reduce with %s\n" (Path.pp p);
      let i, j = match k with
	| None -> None, None
	| Some k -> Node_ID.left k, Node_ID.right k in
      let (left, i) = 
	try 
	  L.reduce t.left i p
	with
	  | Split (b, i) -> raise (Split (b, Node_ID.Left i))
      and (right, j) = 
	try
	  R.reduce t.right j p 
	with
	  | Split (b, j) -> raise (Split (b, Node_ID.Right j))
      in
	{ left; right; },	
      match i, j with
	| Some i, Some j -> Some (Node_ID.P (i, j))
	| Some i, None -> Some (Node_ID.Left i)
	| None, Some j -> Some (Node_ID.Right j)
	| None, None -> None

    let canonicalize: t -> t = fun t -> 
      if debug then print_debug "CANONICALIZATION\n";
      { left = L.canonicalize t.left;
	right = R.canonicalize t.right; }

    let equals: t -> t -> bool =  fun t1 t2 -> 
      if debug then print_debug "checking [equals]\n";
      L.equals t1.left t2.left && R.equals t1.right t2.right

    let is_include: t -> t -> bool = fun t1 t2 -> 
      if debug then print_debug "checking [is_include]\n";
      L.is_include t1.left t2.left && R.is_include t1.right t2.right

    let union: t -> t -> t option = fun t1 t2 ->
      if debug then print_debug "computing [Union]\n";
      match L.union t1.left t2.left with
	| None -> None
	| Some left -> 
	    begin
	      match R.union t1.right t2.right with
		| None -> None
		| Some right ->
		    Some { left; right; }
	    end

    let widening: t -> t -> t option = fun t1 t2 ->
      if debug then print_debug "computing [Widening]\n";
      match L.widening t1.left t2.left with
	| None -> None
	| Some left -> 
	    begin
	      match R.widening t1.right t2.right with
		| None -> None
		| Some right ->
		    Some { left; right; }
	    end

    let pp: t -> unit = fun t -> 
      O.XML.print_center "PRED_PROD_SL_DOMAIN";
      O.XML.printf "<div>\n<span class='dp_i'>\n";
      L.pp t.left;
      O.XML.printf "</span>\n<span class='dp_i'>";
      R.pp t.right;
      O.XML.printf "</span>\n</div>\n"	

    let forget_inductive_length: t -> t = fun t -> 
      { left = L.forget_inductive_length t.left;
	right = R.forget_inductive_length t.right; }
	   
 end: SL_DOMAIN)
