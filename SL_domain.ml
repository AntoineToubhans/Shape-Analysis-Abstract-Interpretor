open Offset
open Utils
open Domain_sig
open Neq_pred_domain
open SL_graph_domain
open Inductive_def

(* =========================================================== *)
(* Module SL_Domain                                            *)
(* =========================================================== *)
(*                                  Last modified: AT 06/20/11 *)

let error(s: string) = failwith (Printf.sprintf "SL_DOMAIN_ERROR: %s" s)

module MAKE_SL_DOMAIN = 
  functor (D: INDUCTIVE_DEF) ->
    (struct
       
       module P = NEQ_DOMAIN
       module G = SL_GRAPH_DOMAIN
       module D = D

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
	   if debug then print_debug "SL_DOMAIN: egalities reduced...\n";
	   (g, p)
      
       let malloc: offset list -> t -> int*t = fun ol (g, p) ->
	 if debug then print_debug "SL_DOMAIN: malloc %s...\n" 
	   (List.fold_left (fun s o -> Printf.sprintf "%s %s" s (pp_offset o)) "" ol);
	 let i, g = G.create_fresh_node g in
	 let g = List.fold_left (fun g o -> G.add_edge i o 0 g) g ol in 
	 let p = IntSet.fold (fun j p -> if j!=i then P.add_neq i j p else p) (G.domain g) p in
	   i, (g, p)
	     
       let break_inductive_forward: int -> t -> t*t = fun i (g, p) ->
	 try
	   let ind = get (G.get_inductive i g) in
	     if ind.length!=0 then raise No_value;
	     let args, g0 = G.create_n_fresh_nodes D.number_of_parameters g in
	     let j, g0 = G.create_fresh_node g0 in
	     let ind0 = 
	       { target = j;
		 source_parameters = ind.source_parameters;
		 target_parameters = args;
		 length = 1;}
	     and ind1 =  
	       { target = ind.target;
		 source_parameters = args;
		 target_parameters = ind.target_parameters;
		 length = 0;} in
	     let g0 = G.add_inductive j ind1 (G.update_inductive i ind0 g0) 
	     and p1 = 
	       List.fold_left2 
		 (fun g x y -> P.add_eq x y g)
		 (P.add_eq i ind.target p) ind.source_parameters ind.target_parameters in
	       (g0, p), (G.remove_inductive i g, p1)
	 with
	   | No_value -> 
	       error (Printf.sprintf "can not break inductive from %i: there's no _inductive" i)
	   | Invalid_argument _ ->	   
	       error (Printf.sprintf "inductive from %i ill-formed: not the same numbers of args" i)

       let break_inductive_backward: int -> t -> t*t = fun i (g, p) ->
	 try
	   let ind = get (G.get_inductive i g) in
	     if ind.length!=0 then raise No_value;
	     let args, g0 = G.create_n_fresh_nodes D.number_of_parameters g in
	     let j, g0 = G.create_fresh_node g0 in
	     let ind0 = 
	       { target = j;
		 source_parameters = ind.source_parameters;
		 target_parameters = args;
		 length = 0;}
	     and ind1 =  
	       { target = ind.target;
		 source_parameters = args;
		 target_parameters = ind.target_parameters;
		 length = 1;} in
	     let g0 = G.add_inductive j ind1 (G.update_inductive i ind0 g0) 
	     and p1 = 
	       List.fold_left2 
		 (fun g x y -> P.add_eq x y g)
		 (P.add_eq i ind.target p) ind.source_parameters ind.target_parameters in
	       (g0, p), (G.remove_inductive i g, p1)
	 with
	   | No_value -> 
	       error (Printf.sprintf "can not break inductive from %i: there's no _inductive" i)
	   | Invalid_argument _ ->	   
	       error (Printf.sprintf "inductive from %i ill-formed: not the same numbers of args" i)

       let unfold: int -> t -> t = fun i t -> t 

       let canonicalize: t -> t = fun t -> t
    
       let find: int -> offset -> t -> (offset * int) list = fun i o t -> []
       let deffer: t -> int -> offset -> int = fun t i o -> i 
	   
       let mutation: int -> int -> t -> t = fun i j t -> t

       let pp: t -> string = fun (g, p) -> 
	 Printf.sprintf "-----Print SL_DOMAIN ------\n%s%s" (P.pp p) (G.pp g)
	   
     end: SL_DOMAIN)



module A = MAKE_SL_DOMAIN(TList)
module B = MAKE_SL_DOMAIN(DLList)

let _, t = B.malloc [Zero] B.empty
let _, t = B.malloc [RecordField("next",Zero); RecordField("prev",Zero); RecordField("top",Zero)] t

let _ = 
  Printf.printf "%s" (B.pp t)

