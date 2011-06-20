open Utils
open Domain_sig

(* =========================================================== *)
(* Module NEQ_Pred_ Domain, inequalities domain                *)
(* =========================================================== *)
(*                                  Last modified: AT 06/18/11 *)

module NEQ_Domain = 
  (struct
    
    type t = 
	{ neq    : (int*int) list;
	  eq     : (int*int) list;
	  lives  : int list;}

    (* basic constructors *)
    let empty:t = {neq=[]; eq=[]; lives=[];}

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
 
    let pop_equality: t -> (int*int) option = 
      fun t -> match t.eq with | [] -> None | e::_ -> Some e

    let add_neq: int -> int -> t -> t = 
      fun i j t -> {t with neq = (i, j)::t.neq}
    let add_eq: int -> int -> t -> t = 
      fun i j t -> {t with eq = (i, j)::t.eq}
    let add_live: int -> t -> t = 
      fun i t -> { t with lives = i::t.lives}      


    let forget: int -> t -> t = fun i t ->
      if is_live i t then failwith (Printf.sprintf "NEQ_DOMAIN_ERROR: can not delete %i which's alive\n" i);
      let filter (x, y) = x==i || y==i in
      { neq = List.filter filter t.neq;
	eq = List.filter filter t.eq;
	lives = t.lives;}

    (* deletes i *)
    let fusion: int -> int -> t -> t = fun i j t->
      if is_live i t then failwith (Printf.sprintf "NEQ_DOMAIN_ERROR: can not delete %i which's alive\n" i);
      let change_index = fun k-> if i==k then j else k in
      let change_index_cpl = fun (x, y) -> (change_index x, change_index y) in 
     	{ neq = List.map change_index_cpl t.neq;
	  eq = List.map change_index_cpl t.eq;
	  lives = t.lives;} 

    let pp: t -> string = fun t ->
      let s = List.fold_left 
	(fun s (i, j) -> Printf.sprintf "%s%i != %i\n" s i j) "---Print NEQ_PRED_DOMAIN---\n" t.neq in
	List.fold_left 
	  (fun s (i, j) -> Printf.sprintf "%s%i == %i\n" s i j) s t.eq 
	
   end: PRED_DOMAIN) 
