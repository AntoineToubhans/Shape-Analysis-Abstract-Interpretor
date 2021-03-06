(* domain signatures                          *)
(*                last modified : AT 10/21/11 *)
open Offset
open Utils
open Simple_C_syntax

module type XML_GEN =
  sig
    val xml_file: string
    val printf: ('a, out_channel, unit) format -> 'a
    val print_h1: ('a, out_channel, unit) format -> 'a
    val print_h2: ('a, out_channel, unit) format -> 'a
    val print_h3: ('a, out_channel, unit) format -> 'a
    val print_bold: ('a, out_channel, unit) format -> 'a
    val print_italic: ('a, out_channel, unit) format -> 'a
    val print_center: ('a, out_channel, unit) format -> 'a
    val print_hr: unit -> unit
    val print_header: unit -> unit
    val print_footer: unit -> unit
  end

module type OPTION = 
  sig
    val debug: bool
    val reduction: int
    val c_file: string
    module XML: XML_GEN
  end

module Inductive = 
  struct

    type inductive_length = 
      | Unknown | Length of int

    let add_length x y = match x, y with
      | Length i, Length j -> Length (i+j)
      | _, _ -> Unknown

    let equals_length: inductive_length -> inductive_length -> bool = fun l1 l2 ->
      match l1, l2 with
	| Unknown, Unknown -> true
	| Length i, Length j -> i==j
	| _ -> false
	  
    type t = 
	{ target: int;
	  source_parameters: int list;
	  target_parameters: int list;
	  length: inductive_length;}
	  
    let forget_length: t -> t = fun ind ->
      { ind with length = Unknown }

    let is_positive: t -> bool = fun ind -> 
      match ind.length with
	| Unknown -> false
	| Length i -> (i > 0)

    let change_index: (int -> int) -> t -> t = fun f ind ->
      { target = f ind.target;
	source_parameters = List.map f ind.source_parameters;
	target_parameters = List.map f ind.target_parameters;
	length = ind.length;}

    let pp: t -> string = fun ind ->
      Printf.sprintf "ind(%s) *=%s= %i.ind(%s)" 
	(pp_list ind.source_parameters) 
	(match ind.length with 
	   | Unknown -> "" | Length i -> Printf.sprintf "%i" i) 
	ind.target (pp_list ind.target_parameters)
	
    let get_domain: t -> int list = fun ind ->
      ind.target::(List.append ind.source_parameters ind.target_parameters)
	
  end

(* request to split an inductive *)
(*      Split true, i :          *)
(* i ===_===> j                  *)
(*      -> fusion i j            *)
(*      -> i===1===> k===_===> j *)
(*      Split false, i :         *)
(* i ===_===> j                  *)
(*      -> fusion i j            *)
(*      -> i===_===> k===1===> j *)
exception Split of bool * Node_ID.t
     
module type SL_GRAPH_DOMAIN =
  sig      

    val debug: bool

    type t
      
    val empty: t
      
    val next: t -> int

    val is_node_empty: int -> t -> bool

    val add_edge: int -> offset -> int -> t -> t
    val remove_edge: int -> offset -> t -> t
    (* update i o j t <=> add i o j (remove i o t) *)
    val update_edge: int -> offset -> int -> t -> t

    val add_inductive: int -> Inductive.t -> t -> t
    val remove_inductive: int -> t -> t
    val update_inductive: int -> Inductive.t -> t -> t

    val create_fresh_node: t -> int* t
    val create_fresh_node_index: int -> t -> t
    val create_n_fresh_nodes: int -> t -> int list*t

    val get_edge: int -> offset -> t -> int option
    val get_inductive: int -> t -> Inductive.t option

    val has_edge: int -> offset -> t -> bool
    val has_edges: int -> t -> bool
    val has_inductive: int -> t -> bool

    (* check a predicate over one node *)
    val for_all_edges: (offset -> int -> bool) -> int -> t -> bool
    val exists_edge: (offset -> int -> bool) -> int -> t -> bool 

    (* check a predicate over all the nodes *)
    val for_all: (int -> bool) -> t -> bool
    val exists: (int -> bool) -> t -> bool 
    val get_nodes: (int -> bool) -> t -> IntSet.t

    val fold: (int -> 'a -> 'a) -> t -> 'a -> 'a 

    val find: int -> offset -> t -> (offset * int) list

    val fusion: int -> int -> t -> t

    val is_reached_by_edge: int -> (int -> offset -> bool) -> t -> bool
    val is_reached_by_inductive: int -> (int -> Inductive.t -> bool) -> t -> bool
    val is_reached: int -> (int -> bool) -> t -> bool

    val domain: t -> IntSet.t

    val equals: int IntMap.t -> int IntMap.t -> t -> t -> (int IntMap.t * int IntMap.t) option 

    val find_path: int -> int -> t -> Path.t list -> Path.t list

    val pp: t -> unit

    val forget_inductive_length: t -> t

    val clean_node: int -> t -> t
    val clean: t -> t
  end

module type PRED_DOMAIN = 
  sig

    val debug: bool

    type t

    val empty: t
    val is_top: t -> bool
    (* under-approximation of bottom *)
    (*      is_bottom t => t= _|_     *)
    val is_bottom: t -> bool
    val check_bottom: t -> t

    val is_live: int -> t -> bool
    val are_not_equal: int -> int -> t -> bool

    (* usefull to perform egalities reduction in SL_DOMAIN *)
    val pop_equality: t ref -> (int*int) option

    val add_neq: int -> int -> t -> t
    val add_eq: int -> int -> t -> t 
    val add_live: int -> t -> t

    val forget: int -> t -> t

    val fusion: int -> int -> t -> t

    val get_lives: t -> int list

    val equals: int IntMap.t -> int IntMap.t -> t -> t -> bool
    val is_include: int IntMap.t -> int IntMap.t -> t -> t -> bool

    val pp: t -> unit

    val clean: IntSet.t -> t -> t
  end

module type INDUCTIVE_DEF = 
  sig
    val name: string

    val number_of_parameters: int
    val number_of_fresh: int

    val domain_offset: offset list

    (* length = number_of_fresh *)
    val def_points_to_fresh: offset list  
    (* length = number_of_parameters *)
    val def_points_to_parameters: offset list

    (* current node -> parameters -> fresh *)
    val new_parameters: int -> int list -> int list -> int list

  end

module type SL_DOMAIN = 
  sig
    val name: string

    type t
    val empty: t

    val next: t -> Node_ID.t
    val zero: t -> Node_ID.t

    val request_eq: Node_ID.t -> Node_ID.t -> t -> t
    val request_neq: Node_ID.t -> Node_ID.t -> t -> t

    val reduce_equalities_one_step: t -> (Node_ID.t*Node_ID.t*t) option

    (* under-approximation of bottom *)
    (*      is_bottom t => t=_|_     *)
    val is_bottom: t -> bool

    val create_fresh_node: t -> Node_ID.t * t
    val malloc: offset list -> t -> Node_ID.t*t
    val var_alloc: Node_ID.t -> offset list -> t -> t

    val case_inductive_forward: Node_ID.t -> t -> t list
    val case_inductive_backward: Node_ID.t -> t -> t list

    val search: Node_ID.t -> offset -> t -> Node_ID.t * t
    (* mutate a o b t                *)
    (* t MUST contains       a@o->c  *)
    (* which's replaced by:  a@o->b  *)
    val mutate: Node_ID.t -> offset -> Node_ID.t -> t -> t

    val canonicalize: t -> t  

    val equals: t -> t -> bool
    val is_include: t -> t -> bool

    val union: t -> t -> (Nodes_Mapping.t * Nodes_Mapping.t * t) option
    val widening: t -> t -> (Nodes_Mapping.t * Nodes_Mapping.t * t) option

    val track_node: Node_ID.t -> t -> Path.t list -> Path.t list
    val reduce: t -> Node_ID.t option -> Path.t -> t * Node_ID.t option

    val pp: t -> unit

    val forget_inductive_length: t -> t

  end

module type DIS_DOMAIN = 
  sig

    val debug: bool

    type t   

    val init: t

    val top: t        
    val bottom: t

    val union: t -> t -> t
    val widening: t -> t -> t
    val is_include: t -> t -> bool

    val var_alloc: offset list -> t -> t * Node_ID.t
    
    (* mut [o1, ..on] &x &y assign *)
    val mutation: offset list -> offset list -> Node_ID.t -> Node_ID.t -> sc_assignment -> t -> t 
    val filter: offset list -> Node_ID.t -> Node_ID.t -> sc_cond -> t -> t*t

    val pp: t -> unit

    (* spec functions *)
    val forget_inductive_length: t -> t
    val canonicalize: t -> t

  end 

module type DOMAIN =
  sig

    val debug: bool

    type t

    val pp: t -> unit

    val init: t

    val eval_sc_assignment: sc_assignment -> t -> t
    val eval_sc_struct_decl: sc_struct_decl -> t -> t
    val eval_sc_var_decl: sc_var_decl -> t -> t

    val filter : sc_cond -> t -> t*t

    val union: t -> t -> t
    val widening: t -> t -> t

    val eval_sc_command: t -> sc_command -> t 

  end


