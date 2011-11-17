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
(*                                  Last modified: AT 11/10/11 *)
(* =========================================================== *)
(*                                        predicative product  *)

let error(s: string) = failwith (Printf.sprintf "PRED_PROD_SL_DOMAIN_ERROR: %s" s)

module Pred_Over_Product : functor (O: OPTION) -> 
sig
  type t
  val empty: t
  val add: Node_ID.t -> t -> (Node_ID.t * Node_ID.t) list * t
    (* Node_ID arg must be linear path     *)
    (* there is at most one tree path in t *)
    (* which corresponds                   *)
  val get: t -> Node_ID.t -> Node_ID.t option
  val pp: t -> unit 
  val shift: Nodes_Mapping.t -> t -> t
  val union: t -> t -> t
end = functor (O: OPTION) -> 
struct
  let debug = O.debug
  let print_debug x = Utils.print_debug ("Predicates over product:\t" ^^ x)
  type t = Node_IDSet.t
  let empty: t = Node_IDSet.empty
  let add: Node_ID.t -> t -> (Node_ID.t * Node_ID.t) list * t = fun p t -> 
    if debug then print_debug "adding %s\n" (Node_ID.pp p);
    let t, p, list_eq = 
      Node_IDSet.fold 
	(fun q (t, p, list_eq) -> 
	   let oeq, op = Node_ID.fusion_eq q p in
	   let list_eq = match oeq with 
	     | None -> list_eq
	     | Some eq -> eq::list_eq
	   and t, p = match op with
	     | None -> t, p
	     | Some p -> Node_IDSet.remove q t, p in
	     t, p, list_eq)
	t (t, p, []) in
      list_eq, Node_IDSet.add p t
  let get: t -> Node_ID.t -> Node_ID.t option = fun t p -> 
    if debug then print_debug "getting %s\n" (Node_ID.pp p);
    let t = ref t and b = ref true and q = ref p in
      while !b && not (Node_IDSet.is_empty !t) do
	q:= Node_IDSet.choose !t;
	t:= Node_IDSet.remove !q !t;
	b:= not (Node_ID.is_include p !q)
      done;
      if !b && debug then print_debug "got nothing.\n";
      if (not !b) && debug then print_debug "got %s\n" (Node_ID.pp !q);
      if !b then None else Some !q
  let pp: t -> unit = fun t ->
    O.XML.print_bold "Predicates:<br/>";
    Node_IDSet.iter
      (fun i -> O.XML.printf "Eq[ %s ]<br/>" (Node_ID.pp i)) t
  let shift: Nodes_Mapping.t -> t -> t = fun map t ->
    if debug then print_debug "shifting...\n";
    t
  let union: t -> t -> t = fun t1 t2 ->
    if debug then print_debug "computing [Union]\n";
    empty
end



module MAKE_PRED_PROD_SL_DOMAIN =
  functor (L: SL_DOMAIN) -> 
    functor (R: SL_DOMAIN) -> 
      functor (O: OPTION) -> 
(struct
   module P = Pred_Over_Product(O)

   let debug = O.debug
   let name = "PRED_PROD_SL_DOMAIN"

   let print_debug x = 
     Utils.print_debug ("%s:\t" ^^ x) name

   type t = 
       { left: L.t;
	 right: R.t; 
	 predicates: P.t; }

   let empty = 
     { left = L.empty; 
       right = R.empty; 
       predicates = P.empty; }       

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
       { left; right; predicates = t.predicates; }

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
       { left; right; predicates = t.predicates; }

   let add_pred: Node_ID.t -> t -> t = fun p t ->
     if debug then print_debug "adding product predicate: Eq[ %s ]...\n" (Node_ID.pp p);
     let list_eq, pred = P.add p t.predicates in
       List.fold_left
	 (fun t (p1, p2) -> request_eq p1 p2 t)
	 { t with predicates = pred }
	 list_eq

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
		 { left;  right = t.right; predicates = t.predicates; })		 
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
			   { left = t.left; right; predicates = t.predicates; })
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
	Node_ID.P (i, j), { left; right; predicates = t.predicates; }

    let malloc: offset list -> t -> Node_ID.t * t = fun ol t -> 
      if debug then print_debug "malloc [%s ]...\n" 
	(List.fold_left (fun s o -> Printf.sprintf "%s %s" s (pp_offset o)) "" ol);
      let i, left = L.malloc ol t.left 
      and j, right = R.malloc ol t.right in
	Node_ID.P (i, j), { left; right; predicates = t.predicates; }

    let var_alloc: Node_ID.t -> offset list -> t -> t = fun k ol t -> 
      if debug then print_debug "var_alloc [%s ] at %s\n" 
	(List.fold_left (fun s o -> Printf.sprintf "%s %s" s (pp_offset o)) "" ol)
	(Node_ID.pp k);
      let i, j = match k with
	| Node_ID.P (i, j) -> i, j 
	| Node_ID.All i -> Node_ID.All i, Node_ID.All i
	| _ -> error (Printf.sprintf "bad variable allocation: %s" (Node_ID.pp k)) in 
	  let left = L.var_alloc i ol t.left 
	  and right = R.var_alloc j ol t.right in
	    add_pred k
	      { left; right; predicates = t.predicates; }

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
	List.flatten
	  (List.map
	     (fun left -> List.map (fun right -> { left; right; predicates = t.predicates; }) rights)
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
	     (fun left -> List.map (fun right -> { left; right; predicates = t.predicates; }) rights)
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
	k, add_pred k { left; right; predicates = t.predicates; }

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
	{ left; right; predicates = t.predicates; }

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
	{ left; right; predicates = t.predicates; },	
      match i, j with
	| Some i, Some j -> Some (Node_ID.P (i, j))
	| Some i, None -> Some (Node_ID.Left i)
	| None, Some j -> Some (Node_ID.Right j)
	| None, None -> None

    let canonicalize: t -> t = fun t -> 
      if debug then print_debug "CANONICALIZATION\n";
      { left = L.canonicalize t.left;
	right = R.canonicalize t.right; 
	predicates = t.predicates; }

    let equals: t -> t -> bool =  fun t1 t2 -> 
      if debug then print_debug "checking [equals]\n";
      L.equals t1.left t2.left && R.equals t1.right t2.right

    let is_include: t -> t -> bool = fun t1 t2 -> 
      if debug then print_debug "checking [is_include]\n";
      L.is_include t1.left t2.left && R.is_include t1.right t2.right

    let union: t -> t -> (Nodes_Mapping.t * Nodes_Mapping.t * t) option = fun t1 t2 ->
      if debug then print_debug "computing [Union]\n";
      match L.union t1.left t2.left with
	| None -> None
	| Some (ml1, ml2, left) -> 
	    begin
	      match R.union t1.right t2.right with
		| None -> None
		| Some (mr1, mr2, right) ->
		    let m1 = Nodes_Mapping.combine ml1 mr1
		    and m2 = Nodes_Mapping.combine ml2 mr2 in
		    let predicates = 
		      P.union
			(P.shift m1 t1.predicates)
			(P.shift m2 t2.predicates) in
		      Some ( m1, m2, { left; right; predicates; } )
	    end 

    let widening: t -> t -> (Nodes_Mapping.t * Nodes_Mapping.t * t) option = fun t1 t2 ->
      if debug then print_debug "computing [Widening]\n";
      match L.widening t1.left t2.left with
	| None -> None
	| Some (ml1, ml2, left) -> 
	    begin
	      match R.widening t1.right t2.right with
		| None -> None
		| Some (mr1, mr2, right) ->
		    let m1 = Nodes_Mapping.combine ml1 mr1
		    and m2 = Nodes_Mapping.combine ml2 mr2 in
		    let predicates = 
		      P.union
			(P.shift m1 t1.predicates)
			(P.shift m2 t2.predicates) in
		      Some ( m1, m2, { left; right; predicates; } )
	    end 


    let pp: t -> unit = fun t -> 
      O.XML.print_center "PRED_PROD_SL_DOMAIN";
      O.XML.printf "<div class=\"box_SL\">\n";
      P.pp t.predicates;
      O.XML.printf "</div>\n<div>\n<span class='dp_i'>\n";
      L.pp t.left;
      O.XML.printf "</span>\n<span class='dp_i'>";
      R.pp t.right;
      O.XML.printf "</span>\n</div>\n"	

    let forget_inductive_length: t -> t = fun t -> 
      { left = L.forget_inductive_length t.left;
	right = R.forget_inductive_length t.right; 
	predicates = t.predicates; }
	   
 end: SL_DOMAIN)
