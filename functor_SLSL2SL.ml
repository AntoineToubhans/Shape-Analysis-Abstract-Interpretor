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
(*                simple product with no communication for now *)

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


    let reduce_equalities_one_step: t -> int list -> int list *t option = fun t l_pt -> 
      if debug then print_debug "reduce_equalities_one_step t...\n";
      [], None
	
    (* under-approximation of bottom *)
    (*      is_bottom t => t=_|_     *)
    let is_bottom: t -> bool = fun t -> false

    let create_fresh_node: t -> int * t = fun t -> 0, t

    let malloc: offset list -> t -> int*t = fun ol t -> 0, t
    let var_alloc: int -> offset list -> t -> t = fun i ol t -> t

    let case_inductive_forward: int -> t -> t*t = fun i t -> t, t
    let case_inductive_backward: int -> t -> t*t = fun i t -> t, t

    let search: int -> offset -> t -> int * t = fun i o t -> 0, t
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
