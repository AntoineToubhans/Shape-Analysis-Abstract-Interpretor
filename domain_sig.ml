(* domain signatures                          *)
(*                last modified : AT 06/19/11 *)

open Offset
open Utils

exception Request_unfolding of int
exception Can_not_defferentiate
 
type inductive = 
    { target: int;
      source_parameters: int list;
      target_parameters: int list;
      length: int option;}

let pp_inductive: inductive -> string = fun ind ->
  Printf.sprintf "(%s) *== %i(%s)" (pp_list ind.source_parameters) ind.target (pp_list ind.target_parameters)

let get_domain_inductive: inductive -> int list = fun ind ->
  ind.target::(List.append ind.source_parameters ind.target_parameters)

     
module type SL_GRAPH_DOMAIN =
  sig      
    type t

    val empty: t
      
    val add_edge: int -> offset -> int -> t -> t
    val remove_edge: int -> offset -> t -> t
      (* update i o j t <=> add i o j (remove i o t) *)
    val update_edge: int -> offset -> int -> t -> t

    val add_inductive: int -> inductive -> t -> t
    val remove_inductive: int -> t -> t
    val update_inductive: int -> inductive -> t -> t

    val create_fresh_node: t -> int* t

    val get_edge: int -> offset -> t -> int option
    val get_inductive: int -> t -> inductive option

    val has_edge: int -> offset -> t -> bool
    val has_inductive: int -> t -> bool

    val find: int -> offset -> t -> (offset * int) list

    val fusion: int -> int -> t -> t

    val is_reached_by_edge: int -> (int -> offset -> bool) -> t -> int list
    val is_reached_by_inductive: int -> (int -> inductive -> bool) -> t -> int list 
    val is_reached: int -> (int -> bool) -> t -> int list

    val domain: t -> int list
    val pp: t -> string
  end

module type PRED_DOMAIN = 
  sig
    type t

    val empty: t
    val is_top: t -> bool
    val is_bottom: t -> bool
    val check_bottom: t -> t

    val is_live: int -> t -> bool
    val are_not_equal: int -> int -> t -> bool

    (* usefull to perform egalities reduction in SL_DOMAIN *)
    val pop_equality: t -> (int*int) option

    val add_neq: int -> int -> t -> t
    val add_eq: int -> int -> t -> t 
    val add_live: int -> t -> t

    val forget: int -> t -> t

    val fusion: int -> int -> t -> t

    val pp: t -> string
  end

module type SL_DOMAIN = 
  sig
    module G: SL_GRAPH_DOMAIN
    module P: PRED_DOMAIN

    type t
    val empty: t

    val fusion: int -> int -> t -> t 
    val reduce_egalities: t -> t

    val malloc: offset list -> t -> int*t

    val break_inductive_backward: int -> int -> t -> t list
    val break_inductive_forward: int -> int -> t -> t list

    val unfold: int -> t -> t list

    val canonicalize: t -> t     
    val find: int -> offset -> t -> (offset * int) list
    val deffer: t -> int -> offset -> int 

    val pp: t -> string
  end

module type DOMAIN = 
  sig
    val domainId : int
  
    type t   

    val top: t        
    val bottom: t

    val deffer: t-> offseted_node -> offseted_node
      (* Mutation of the content of a cell *)
    val mutation: t -> offseted_node -> offseted_node -> t 
      
    val pp: t -> string

  end 


