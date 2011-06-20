open Offset
open Utils
open Domain_sig

let tvlad_error(s: string) = failwith (Printf.sprintf "TVLA_DOMAIN_ERROR: %s" s)

module TVLADomain =
  struct

    (* the boolean field indicate wether it's a full edge (true) or a dotted edge (false) *)
    type gen_edge = offseted_node * bool
	
    type t =  gen_edge generic_graph (* plus predicates *)
	
  end

