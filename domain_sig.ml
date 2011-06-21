(* domain signatures                          *)
(*                last modified : AT 06/19/11 *)

open Offset
open Utils

(* request to split an inductive *)
(*      Split true, i :          *)
(* i ===_===> j                  *)
(*      -> fusion i j            *)
(*      -> i===1===> k===_===> j *)
(*      Split true, i :          *)
(* i ===_===> j                  *)
(*      -> fusion i j            *)
(*      -> i===_===> k===1===> j *)
exception Split of bool*int
 
type inductive = 
    { target: int;
      source_parameters: int list;
      target_parameters: int list;
      (* length is optional,                                    *)
      (* 0 means we don't know how long is the sequence         *)
      (* 0 long sequence are forbidden, and immediately reduced *)
      length: int;}

let pp_inductive: inductive -> string = fun ind ->
  Printf.sprintf "(%s) *=%s= %i(%s)" 
    (pp_list ind.source_parameters) 
    (if ind.length==0 then "_" else (Printf.sprintf "%i" ind.length)) 
    ind.target (pp_list ind.target_parameters)

let get_domain_inductive: inductive -> int list = fun ind ->
  ind.target::(List.append ind.source_parameters ind.target_parameters)

     
module type SL_GRAPH_DOMAIN =
  sig      
    type t

    val empty: t
      
    val is_node_empty: int -> t -> bool

    val add_edge: int -> offset -> int -> t -> t
    val remove_edge: int -> offset -> t -> t
      (* update i o j t <=> add i o j (remove i o t) *)
    val update_edge: int -> offset -> int -> t -> t

    val add_inductive: int -> inductive -> t -> t
    val remove_inductive: int -> t -> t
    val update_inductive: int -> inductive -> t -> t

    val create_fresh_node: t -> int* t
    val create_n_fresh_nodes: int -> t -> int list*t

    val get_edge: int -> offset -> t -> int option
    val get_inductive: int -> t -> inductive option

    val has_edge: int -> offset -> t -> bool
    val has_inductive: int -> t -> bool

    val find: int -> offset -> t -> (offset * int) list

    val fusion: int -> int -> t -> t

    val is_reached_by_edge: int -> (int -> offset -> bool) -> t -> int list
    val is_reached_by_inductive: int -> (int -> inductive -> bool) -> t -> int list 
    val is_reached: int -> (int -> bool) -> t -> int list

    val domain: t -> IntSet.t
    val pp: t -> string
  end

module type PRED_DOMAIN = 
  sig
    type t

    val empty: t
    val is_top: t -> bool
    (* under-approximation of bottom *)
    (*      is_bottom t => t=_|_     *)
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

module type INDUCTIVE_DEF = 
  sig

    val number_of_parameters: int

    val number_of_fresh: int

    val domain_offset: offset array

    (* length = number_of_fresh *)
    val def_points_to_fresh: offset list  
    (* length = number_of_parameters *)
    val def_points_to_parameters: offset list

    (* current node -> parameters -> fresh *)
    val new_parameters: int -> int list -> int list -> int list

  end

module type SL_DOMAIN = 
  sig
    module G: SL_GRAPH_DOMAIN
    module P: PRED_DOMAIN
    module D: INDUCTIVE_DEF

    type t
    val empty: t

    val fusion: int -> int -> t -> t 
    val reduce_egalities: t -> t

    (* under-approximation of bottom *)
    (*      is_bottom t => t=_|_     *)
    val is_bottom: t -> bool

    val malloc: offset list -> t -> int*t

    val break_inductive_forward: int -> t -> t*t
    val break_inductive_backward: int -> t -> t*t

    val unfold: int -> t -> t 
    val find: int -> offset -> t -> (offset * int) list
    val deffer: t -> int -> offset -> int 

    val fold: int -> t -> t option
    val canonicalize: t -> t  

    val mutation: int -> int -> t -> t

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


