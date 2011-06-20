(* domain signatures                          *)
(*                last modified : AT 06/19/11 *)

open Offset
open Utils

exception Request_unfolding of int
exception Can_not_defferentiate

module type SL_GRAPH_DOMAIN =
  sig  
    val domainId : int   
    type t

    val add_edge: int -> offset -> int -> t -> t
    val remove_edge: int -> offset -> t -> t
      (* update i o j t <=> add i o j (remove i o t) *)
    val update_edge: int -> offset -> int -> t -> t

    val add_inductive: int -> (int list) -> int -> t -> t
    val remove_inductive: int -> t -> t

    val fusion: int -> int -> t -> t

    val is_reached: int -> t -> int list
    val is_reached_by_edge: int -> (offset -> bool) -> int list
    val is_reached_by_inductive: int -> (int list -> bool) -> int list 

    val domain: t -> int list
    val pp: t -> string
  end

module type PRED_DOMAIN = 
  sig
    type t

    val is_live: int -> t -> bool

    val add_neq: int -> int -> t -> t
    val add_eq: int -> int -> t -> t 
    val add_live: int -> t -> t

    val fusion: int -> int -> t -> t

    val pp: t -> string
  end

module type SL_DOMAIN = 
  sig
    module G: SL_GRAPH_DOMAIN
    module E: PRED_DOMAIN

    val domainId : int   
    type t

    val malloc: offset list -> t -> t* int

    val canonicalize: t -> t 
    val find: t -> int -> offset -> offseted_node list
    val deffer: t -> int -> offset -> int 
  end

module type DOMAIN = 
  sig
    val domainId : int
  
    type t   

    val empty: t        
 
   val deffer: t-> offseted_node -> offseted_node
    (* Mutation of the content of a cell *)
    val mutation: t -> offseted_node -> offseted_node -> t 
    
    val pp: t -> string

  end 


