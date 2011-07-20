open Utils
open Domain_sig

(* =========================================================== *)
(* Module NEQ_Pred_ Domain, inequalities domain                *)
(* =========================================================== *)
(*                                  Last modified: AT 06/18/11 *)

module NEQ_DOMAIN = 
  (struct
    
    type t = 
	{ neq    : (int*int) list;
	  eq     : (int*int) list;
	  lives  : int list;}

    (* basic constructors *)
    let empty:t = {neq=[]; eq=[]; lives=[0];}

    let is_top: t -> bool = fun t ->
      t.neq==[] && t.eq==[] 

    let is_bottom: t -> bool = fun t ->
      List.exists (fun (x, y) -> x==y) t.neq

    let check_bottom: t -> t = fun t -> 
      if is_bottom t then raise Bottom else t

    let is_live: int -> t -> bool = 
      fun n t -> List.mem n t.lives

    let are_not_equal: int -> int -> t -> bool =
      fun i j t -> List.mem (i, j) t.neq || List.mem (j, i) t.neq 
 
    let pop_equality: t ref -> (int*int) option = 
      fun t -> match (!t).eq with | [] -> None | e::tl -> t:={!t with eq = tl}; Some e

    let add_neq: int -> int -> t -> t = fun i j t -> 
      if debug then print_debug "NEQ_DOMAIN: add_neq %i %i t\n" i j;
      {t with neq = (i, j)::t.neq}

    let add_eq: int -> int -> t -> t = fun i j t -> 
      if debug then print_debug "NEQ_DOMAIN: add_eq %i %i t\n" i j;
      {t with eq = (i, j)::t.eq}
	
    let add_live: int -> t -> t = fun i t -> 
      if debug then print_debug "NEQ_DOMAIN: add_lives %i t\n" i;
      { t with lives = i::t.lives}      

    let forget: int -> t -> t = fun i t ->
      if debug then print_debug "NEQ_DOMAIN: forget %i t\n" i;
      if is_live i t then failwith (Printf.sprintf "NEQ_DOMAIN_ERROR: can not delete %i which's alive\n" i);
      let filter (x, y) = x!=i && y!=i in
      { neq = List.filter filter t.neq;
	eq = List.filter filter t.eq;
	lives = t.lives;}

    (* deletes i *)
    let fusion: int -> int -> t -> t = fun i j t->
      if debug then print_debug "NEQ_DOMAIN: fusion %i %i t\n" i j;
      if is_live i t then failwith (Printf.sprintf "NEQ_DOMAIN_ERROR: can not delete %i which's alive\n" i);
      let change_index = fun k-> if i==k then j else k in
      let change_index_cpl = fun (x, y) -> (change_index x, change_index y) in 
     	{ neq = List.map change_index_cpl t.neq;
	  eq = List.map change_index_cpl t.eq;
	  lives = t.lives;} 

    let get_lives: t -> int list = fun t -> 
      if debug then print_debug "NEQ_DOMAIN: get_lives\n";
      t.lives

    (* checks only inequalities                    *)
    (* we assume that, at disjunction layer level, *)
    (* we have no longer equalities in t           *)
    let equals: int IntMap.t -> int IntMap.t -> t -> t -> bool = fun m1 m2 t1 t2 ->
      if debug then print_debug "NEQ_DOMAIN: checking [equals]\n";
      let b = 
	try
	  List.for_all 
	    (fun (i, j) -> are_not_equal (IntMap.find i m1) (IntMap.find j m1) t2) t1.neq
	  && List.for_all 
	    (fun (i, j) -> are_not_equal (IntMap.find i m2) (IntMap.find j m2) t1) t2.neq     
	with
	  | Not_found -> 
	      false in
	if debug && b then print_debug "NEQ_DOMAIN: [equals] ... Yes\n";
	if debug && not b then print_debug "NEQ_DOMAIN: [equals] ... No\n";
	b

    let pp: t -> string = fun t ->
      let s = List.fold_left 
	(fun s (i, j) -> Printf.sprintf "%s%i <> %i\n" s i j) "     ---Print NEQ_PRED_DOMAIN---\n" t.neq in
	List.fold_left 
	  (fun s (i, j) -> Printf.sprintf "%s%i == %i\n" s i j) s t.eq 
	
   end: PRED_DOMAIN) 
