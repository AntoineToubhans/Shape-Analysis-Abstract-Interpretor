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
(*                                        Created: AT 07/23/11 *)
(*                                  Last modified: AT 09/27/11 *)
(* =========================================================== *)
(*                                             simple product  *)

let error(s: string) = failwith (Printf.sprintf "SL_PROD_SL_DOMAIN_ERROR: %s" s)

module MAKE_PROD_SL_DOMAIN =
  functor (S: SL_DOMAIN) -> 
    functor (T: SL_DOMAIN) -> 
      functor (O: OPTION) -> 
(struct

   let debug = O.debug

   let name = Printf.sprintf "SL_PROD_SL_DOMAIN(%s, %s)" S.name T.name

   let print_debug x = 
     Utils.print_debug ("%s:\t" ^^ x) name

   type v = Left of int | Right of int | P of int*int

   type t = 
       { left: S.t;
	 right: T.t;
	 link: v IntMap.t; 
	 next: int;
       }

   let empty = 
     { left = S.empty; 
       right = T.empty; 
       link = IntMap.singleton 0 (P (0,0)); 
       next=1; }

   let next: t -> int = fun t -> t.next

   let get_left: t -> int -> int option = fun t i ->
     try
       match IntMap.find i t.link with
	 | Left x | P (x, _) -> Some x
	 | _ -> None
     with 
       | Not_found -> None
	   
   let get_right: t -> int -> int option = fun t i ->
     try
       match IntMap.find i t.link with
	 | Right x | P (_, x) -> Some x
	 | _ -> None
     with 
       | Not_found -> None
	   
   let request_eq: int -> int -> t -> t = fun i j t -> 
     if debug then print_debug "request_eq %i %i t\n" i j;
     let il = get_left t i and ir = get_right t i 
     and jl = get_left t j and jr = get_right t j in
     let left = 
       match il, jl with
	 | Some il, Some jl -> S.request_eq il jl t.left
	 | _ -> t.left
     and right = 
       match ir, jr with
	 | Some ir, Some jr -> T.request_eq ir jr t.right
	 | _ -> t.right in
       { left; right; link = t.link; next = t.next; }

   let request_neq: int -> int -> t -> t = fun i j t -> 
     if debug then print_debug "request_neq %i %i t\n" i j;
     let il = get_left t i and ir = get_right t i 
     and jl = get_left t j and jr = get_right t j in
     let left = 
       match il, jl with
	 | Some il, Some jl -> S.request_neq il jl t.left
	 | _ -> t.left
     and right = 
       match ir, jr with
	 | Some ir, Some jr -> T.request_neq ir jr t.right
	 | _ -> t.right in
       { left; right; link = t.link; next = t.next; }


    let reduce_equalities_one_step: t -> (int*int*t) option = fun t -> 
      if debug then print_debug "reduce_equalities_one_step t...\n";
      let f i j k = if i==k then j else k in
	match S.reduce_equalities_one_step t.left with
	  | Some (i, j, l) ->
	      Some(0, 0, 
		   { left = l;
		     right = t.right;
		     link = IntMap.map 
		       (function 
			  | Left x -> Left (f i j x)
			  | Right y -> Right y
			  | P (x, y) -> P (f i j x, y)) 
		       t.link;
		     next=t.next; })
	  | None -> 
	      begin
		match T.reduce_equalities_one_step t.right with
		  | Some (i, j, r) ->
		      Some(0, 0, 
			   { left = t.left;
			     right = r;
			     link = IntMap.map 
			       (function 
				  | Left x -> Left x
				  | Right y -> Right (f i j y)
				  | P (x, y) -> P (x, f i j y)) 
			       t.link;
			     next=t.next; })
		  | None -> 
		      None
	      end
	
	
    (* under-approximation of bottom *)
    (*      is_bottom t => t=_|_     *)
    let is_bottom: t -> bool = fun t -> 
      let b = S.is_bottom t.left || T.is_bottom t.right in
	if debug && b then print_debug "is t bottom?.....Yes\n"; 
	if debug && not b then print_debug "is t bottom?.....No\n";
	b

    let create_fresh_node: t -> int * t = fun t -> 
      if debug then print_debug "create_fresh_node...[%i]\n" t.next; 
      let i, left = S.create_fresh_node t.left 
      and j, right = T.create_fresh_node t.right in
	t.next,
      { left;
	right;
	link = IntMap.add t.next (P (i, j)) t.link;
	next = t.next + 1;}      

    let malloc: offset list -> t -> int*t = fun ol t -> 
      if debug then print_debug "malloc [%s ]...\n" 
	(List.fold_left (fun s o -> Printf.sprintf "%s %s" s (pp_offset o)) "" ol);
      let i, left = S.malloc ol t.left 
      and j, right = T.malloc ol t.right in
	t.next,
      { left;
	right;
	link = IntMap.add t.next (P (i, j)) t.link;
	next = t.next + 1;}      	

    let var_alloc: int -> offset list -> t -> t = fun k ol t -> 
      if debug then print_debug "var_alloc [%s ]...\n" 
	(List.fold_left (fun s o -> Printf.sprintf "%s %s" s (pp_offset o)) "" ol);
      let i, left = S.malloc ol t.left 
      and j, right = T.malloc ol t.right in
	{ left;
	  right;
	  link = IntMap.add k (P (i, j)) t.link;
	  next = k+1; }       

    let case_inductive_forward: int -> t -> t list = fun i t -> 
      if debug then print_debug "case_inductive_forward %i t\n" i;
      try 
	match IntMap.find i t.link with
	  | Left x -> 
	      List.map 
		(fun left -> { t with left=left }) 
		(S.case_inductive_forward x t.left)
	  | Right y ->
	      List.map 
		(fun right -> { t with right=right }) 
		(T.case_inductive_forward y t.right)
	  | P (x, y) ->
	      let lt = S.case_inductive_forward x t.left
	      and rt = T.case_inductive_forward y t.right in
		List.flatten
		  (List.map
		     (fun left -> 
			List.map 
			  (fun right -> 
			     { left;
			       right;
			       link = t.link;
			       next = t.next; })
			  rt)
		     lt)		
      with
	| Not_found -> 
	    error (Printf.sprintf "can not break inductive: there's no mapping for %i in the product" i)
 
    let case_inductive_backward: int -> t -> t list = fun i t -> 
      if debug then print_debug "case_inductive_backward %i t\n" i;
      try 
	match IntMap.find i t.link with
	  | Left x -> 
	      List.map 
		(fun left -> { t with left=left }) 
		(S.case_inductive_backward x t.left)
	  | Right y ->
	      List.map 
		(fun right -> { t with right=right }) 
		(T.case_inductive_backward y t.right)
	  | P (x, y) ->
	      let lt = S.case_inductive_backward x t.left
	      and rt = T.case_inductive_backward y t.right in
		List.flatten
		  (List.map
		     (fun left -> 
			List.map 
			  (fun right -> 
			     { left;
			       right;
			       link = t.link;
			       next = t.next; })
			  rt)
		     lt)		
      with
	| Not_found -> 
	    error (Printf.sprintf "can not break inductive: there's no mapping for %i in the product" i)

    let search: int -> offset -> t -> int * t = fun i o t -> 
      if debug then print_debug "search for %i%s\n" i (pp_offset o);
      try 
	let oleft, oright = 
	  match IntMap.find i t.link with
	    | Left x -> 
		let x, left = S.search x o t.left in
		  Some (x, left), None
	    | Right y ->
		let y, right = T.search y o t.right in
		  None, Some (y, right)
	    | P (x, y) ->
		(try Some (S.search x o t.left) with | Top -> None), 
		(try Some (T.search y o t.right) with | Top -> None) in
	let v, left, right = 
	  match oleft, oright with
	    | None, Some (y, right) -> Right y, t.left, right
	    | Some (x, left), None -> Left x, left, t.right
	    | Some (x, left), Some (y, right) -> P (x, y), left, right 
	    | _ -> raise Top in
	  t.next,
	{ left = left;
	  right = right;
	  link = IntMap.add t.next v t.link;
	  next = t.next +1; }		
      with
	| Not_found -> 
	    (* this can't happen if search is called properly *)
	    error (Printf.sprintf "can search: there's no mapping for %i in the product" i)


    (* mutate a o b t                *)
    (* t MUST contains       a@o->c  *)
    (* which's replaced by:  a@o->b  *)
    let mutate: int -> offset -> int -> t -> t = fun i o j t -> t

    let canonicalize: t -> t = fun t -> t  

    let equals: t -> t -> bool =  fun _ _ -> false
    let is_include: t -> t -> bool = fun _ _ -> false

    let union: t -> t -> t option = fun _ _ -> None
    let widening: t -> t -> t option = fun _ _ -> None

    let pp: t -> unit = fun t -> ()

    let forget_inductive_length: t -> t = fun t -> t
	   
 end: SL_DOMAIN)
