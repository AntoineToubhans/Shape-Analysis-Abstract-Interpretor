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
(*                                  Last modified: AT 07/27/11 *)

let error(s: string) = failwith (Printf.sprintf "SL_DOMAIN_ERROR: %s" s)

module MAKE_PROD_SL_DOMAIN =
  functor (S: SL_DOMAIN) -> 
    functor (T: SL_DOMAIN) -> 
      functor (O: OPTION) -> 
(struct

   let debug = O.debug

   let name = Printf.sprintf "SL_PROD_DOMAIN(%s, %s)" S.name T.name

   let print_debug x = 
     Utils.print_debug ("%s:\t" ^^ x) name

   type t = S.t * T.t 

   let empty = S.empty, T.empty

   let next: t -> int = fun (s, t) -> max (S.next s) (T.next t)

   let request_eq: int -> int -> t -> t = fun i j (s, t) -> 
     if debug then print_debug "request_eq %i %i t\n" i j;
     (S.request_eq i j s, T.request_eq i j t)

   let request_neq: int -> int -> t -> t = fun i j (s, t) ->
     if debug then print_debug "request_neq %i %i t\n" i j;
     (S.request_neq i j s, T.request_neq i j t)

    let reduce_equalities_one_step: t -> int list -> int list *t option = fun t l -> [], None

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
