open Offset
open Utils
open Domain_sig
open Neq_pred_domain
open SL_graph_domain

(* =========================================================== *)
(* Module SL_Domain                                            *)
(* =========================================================== *)
(*                                  Last modified: AT 06/20/11 *)

let error(s: string) = failwith (Printf.sprintf "SL_DOMAIN_ERROR: %s" s)

module SL_Domain = 
  (struct
     
     module P = NEQ_Domain
     module G = SL_GRAPH_DOMAIN
      
    type t = G.t * P.t

    let empty: t = G.empty, P.empty
    	
    let fusion: int -> int -> t -> t = fun i j (g, p) ->
      if debug then print_debug "SL_DOMAIN: fusion %i %i t\n" i j;
      if i==j then 
	(g, p) 
      else if not (P.is_live i p) then
	G.fusion i j g, P.check_bottom (P.fusion i j p)
      else if not (P.is_live j p) then 
	G.fusion j i g, P.check_bottom (P.fusion j i p)
      else
	raise Bottom

    let rec reduce_egalities: t -> t = fun (g, p) ->
      try
	let i, j = get (P.pop_equality p) in
	  reduce_egalities (fusion i j (g, p))
      with | No_value -> 
	if debug then print_debug "SL_DOMAIN: reduced_egalities...\n";
	(g, p)
      
    let malloc: offset list -> t -> int*t = fun ol (g, p) ->
      let i, g = G.create_fresh_node g in
      let g = List.fold_left (fun g o -> G.add_edge i o 0 g) g ol in
      let p = List.fold_left (fun p j -> if j!=i then P.add_neq i j p else p) p (G.domain g) in
	i, (g, p)
      
	  

    let pp: t -> string = fun (g, p) -> 
      Printf.sprintf "-----Print SL_DOMAIN ------\n%s%s" (P.pp p) (G.pp g)

   end: SL_DOMAIN)


