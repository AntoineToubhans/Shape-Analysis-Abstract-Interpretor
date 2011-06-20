open Offset
open Utils
open Domain_sig
open Eq_domain

let sld_error(s: string) = failwith (Printf.sprintf "SL_DOMAIN_ERROR: %s" s)

module SL_Domain = 
  functor (G: SL_GRAPH_DOMAIN) -> 
    (struct
  
    module L = EQ_Domain

    let domainId = G.domainId
    let debug = G.debug

    type t = G.t * L.t

    let unfold: t -> int -> t list = fun (g, e) i ->
      if debug then print_debug "SL_DOMAIN:unfold t %i\n" i; 
      let ffold: t list -> (G.t* L.r) -> t list= fun l (g, r) -> 
	try (g, L.check (r e))::l with |Bottom -> l 
      in
	List.fold_left ffold [] (G.unfold g i)

    let canonicalize: t -> int list -> t = fun (g, e) lives ->     
      if debug then print_debug "SL_DOMAIN:**CANONICALIZATION\n";
      let g:G.t = (G.canonicalize g lives e.L.null) in
	g, L.check (L.remove (G.domain g) e)
      
    let find: t -> int -> offset -> (t * offseted_node list) list = fun (g, e) i o ->
     

	

     end: SL_DOMAIN)

module SL_tL_Domain = SL_Domain (SL_tList_domain.SL_TL_GRAPH_Domain)
