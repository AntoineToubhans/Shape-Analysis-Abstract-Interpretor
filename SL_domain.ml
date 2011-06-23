open Offset
open Utils
open Domain_sig
open Neq_pred_domain
open SL_graph_domain
open Inductive_def

(* =========================================================== *)
(* Module SL_Domain                                            *)
(* =========================================================== *)
(*                                        Created: AT 06/10/11 *)
(*                                  Last modified: AT 06/23/11 *)

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
	 if (i==0 && not (G.is_node_empty j g))||(j==0 && not(G.is_node_empty i g)) then raise Bottom; 
	 if i==j then 
	   (g, p) 
	 else if not (P.is_live i p) then
	   G.fusion i j g, P.check_bottom (P.fusion i j p)
	 else if not (P.is_live j p) then 
	   G.fusion j i g, P.check_bottom (P.fusion j i p)
	 else
	   raise Bottom
	     
       let rec reduce_equalities: t -> t = fun (g, p) ->
	 if debug then print_debug "SL_DOMAIN: reduce_equalities t...\n";
	 let rg = ref g and rp = ref p in
	 let eq = ref (P.pop_equality rp) in
	   while has !eq do
	     let i, j = get !eq in
	     let t = fusion i j (!rg, !rp) in
	       rg:= fst t; rp:= snd t;
	       eq:= P.pop_equality rp
	   done;
	   if debug then print_debug "SL_DOMAIN: egalities reduced...\n";
	   !rg, !rp
      
       (* So far, is_bottom checks:               *)
       (*  - conflict between inductive and edges *)
       (*  - is_bottom over predicates            *)
       (*!! perfom a reduction of equalities      *)
       (*!! increases chance to get bottom        *)
       let is_bottom: t -> bool = fun (g, p) -> 
	 let check_node i = 
	   let opt_ind = G.get_inductive i g in
	     (has opt_ind && (get opt_ind).length>0) 
	     || List.exists (fun o -> G.has_edge i o g) D.domain_offset in
	 let b_result = P.is_bottom p || G.for_all check_node g in
	   if debug && b_result then print_debug "SL_DOMAIN: is t bottom?.....Yes\n"; 
	   if debug && not b_result then print_debug "SL_DOMAIN: is t bottom?.....Yes\n";b_result
	   
       let malloc: offset list -> t -> int*t = fun ol (g, p) ->
	 if debug then print_debug "SL_DOMAIN: malloc [%s ]...\n" 
	   (List.fold_left (fun s o -> Printf.sprintf "%s %s" s (pp_offset o)) "" ol);
	 let i, g = G.create_fresh_node g in
	 let g = List.fold_left (fun g o -> G.add_edge i o 0 g) g ol in 
	 let p = IntSet.fold (fun j p -> if j!=i then P.add_neq i j p else p) (G.domain g) p in
	   i, (g, p)
	     
       let nullify_inductive: int -> t -> t = fun i (g, p) ->
	 if debug then print_debug "SL_DOMAIN: nullify_inductive %i t\n" i;
	 try
	   let ind = get (G.get_inductive i g) in
	   let p = 
	     List.fold_left2 
	       (fun g x y -> P.add_eq x y g)
	       (P.add_eq i ind.target p) ind.source_parameters ind.target_parameters in
	     (G.remove_inductive i g, p)
	 with
	   | No_value -> 
	       error (Printf.sprintf "can not nullify inductive from %i: there's no inductive" i)
	   | Invalid_argument _ ->	   
	       error (Printf.sprintf "can not nullify inductive from %i: ill-formed inductive" i)
		 
       let case_inductive_forward: int -> t -> t*t = fun i (g, p) ->
	 if debug then print_debug "SL_DOMAIN: case_inductive_forward %i t\n" i;
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
	     let g0 = G.add_inductive j ind1 (G.update_inductive i ind0 g0) in
	       (g0, p), (nullify_inductive i (g, p))
	 with
	   | No_value -> 
	       error (Printf.sprintf "can not break inductive from %i: there's no inductive with no length" i)

       let case_inductive_backward: int -> t -> t*t = fun i (g, p) ->
	 if debug then print_debug "SL_DOMAIN: case_inductive_backward %i t\n" i;
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
	     let g0 = G.add_inductive j ind1 (G.update_inductive i ind0 g0) in
	       (g0, p), (nullify_inductive i (g, p))
	 with
	   | No_value -> 
	       error (Printf.sprintf "can not break inductive from %i: there's no inductive with no length" i)

       let split_inductive_backward: int -> t -> t = fun i (g, p) ->
	 if debug then print_debug "SL_DOMAIN: split_inductive_backward %i t\n" i;
	 try
	   let ind = get (G.get_inductive i g) in
	     if ind.length<2 then raise No_value;
	     let args, g = G.create_n_fresh_nodes D.number_of_parameters g in
	     let j, g = G.create_fresh_node g in
	     let ind0 = 
	       { target = j;
		 source_parameters = ind.source_parameters;
		 target_parameters = args;
		 length = ind.length-1;}
	     and ind1 =  
	       { target = ind.target;
		 source_parameters = args;
		 target_parameters = ind.target_parameters;
		 length = 1;} in
	     let g = G.add_inductive j ind1 (G.update_inductive i ind0 g) in
	       g, p
	 with
	   | No_value -> 
	       error (Printf.sprintf "can not split inductive from %i: there's no inductive with length >2" i)

       (* unfold only finite sequence,                *)
       (* raise Split over sequence of unknown length *)
       (* fail if it can not unfold                   *)
       let unfold: int -> t -> t = fun i (g, p) -> 
	 if debug then print_debug "SL_DOMAIN: try_unfold %i t\n" i;
 	 try
	   let ind = get (G.get_inductive i g) in
	     if ind.length==0 then raise (Split (true, i));
	     let g = G.remove_inductive i g in
	     let fresh, g = G.create_n_fresh_nodes D.number_of_fresh g in
	     let g = List.fold_left2
	       (fun g j o -> G.add_edge i o j g) g fresh D.def_points_to_fresh in
	     let g = List.fold_left2
	       (fun g j o -> G.add_edge i o j g) g ind.source_parameters D.def_points_to_parameters
	     and ind =
	       { target = ind.target;
		 source_parameters = D.new_parameters i ind.source_parameters fresh;
		 target_parameters = ind.target_parameters;
		 length = ind.length - 1;} in
	     let g = G.add_inductive (List.hd fresh) ind g in
	       (* we reduced if the inductive has zero length *)
	     let g, p = if ind.length==0 then nullify_inductive (List.hd fresh) (g, p) else g, p in
	     let p = P.add_neq 0 i p in
	       if debug then print_debug "SL_DOMAIN: unfold successfull at %i t\n" i;
	       g, p
	 with
	   | No_value ->
	       error (Printf.sprintf "unfold failed at %i (there's no inductive)" i)
	   | Invalid_argument _ ->	   
	       error (Printf.sprintf "inductive from %i ill-formed" i)
  
       let search: int -> offset -> t -> int * t = fun i o (g, p) -> 
	 if debug then print_debug "SL_DOMAIN: search for %i%s\n" i (pp_offset o);
	 try get (G.get_edge i o g), (g, p) 
	 with | No_value ->
	   if List.mem o D.domain_offset && G.has_inductive i g then
	     (* unfold can fail or raise Split *)
	     let g, p = unfold i (g, p) in
	       (* this can NOT fail *)
	       get (G.get_edge i o g), (g, p)
	   else (* if............................................ *)
	     let j, g = G.create_fresh_node g in
	       (* we don't know where we are *)
	       j, (g, p)

       let mutate: int -> offset -> int -> offset -> t -> t = fun i o j o1 (g, p) ->
	 if debug then print_debug "SL_DOMAIN: mutate [%i%s := %i%s]\n" i (pp_offset o) j (pp_offset o1);
	 try 
	   G.add_edge i o (get (G.get_edge j o1 g)) (G.remove_edge i o g), p
	 with
	   | _ ->
	       error (Printf.sprintf "can not perform mutation [%i%s := %i%s]" i (pp_offset o) j (pp_offset o1))

       (* attempt to fold at node i: produces either     *)
       (*  - Some t   if attempt was successful          *)
       (*  - none   if it can not be fold for any reason *)
       let try_fold: int -> t -> t option = fun i (g, p) -> 
	 if debug then print_debug "SL_DOMAIN: try to fold at %i t\n" i;
	 try
	   let pt_parameters = 
	     List.map (fun o -> get (G.get_edge i o g)) D.def_points_to_parameters
	   and pt_fresh = 
	     List.map (fun o -> get (G.get_edge i o g)) D.def_points_to_fresh in
	   let ind =
	     { target = List.hd pt_fresh;
	       source_parameters = pt_parameters;
	       target_parameters = D.new_parameters i pt_parameters pt_fresh;
	       length = 1;} in
	   let g = 
	     List.fold_left (fun g o -> G.remove_edge i o g) g D.def_points_to_parameters in
	   let g = 
	     List.fold_left (fun g o -> G.remove_edge i o g) g D.def_points_to_fresh in
	   let g = G.add_inductive i ind g in
	     if debug then print_debug "SL_DOMAIN: successful folding at node %i\n" i;
	     Some(g, p)
	 with 
	   | _ -> 
	       if debug then print_debug "SL_DOMAIN: fail to fold at node %i\n" i;
	       None

       (* try a modus ponens reduction at node i         *)
       (*  - i.c(a) *== j.c(b)  |                        *)
       (*  - j.c(b) *== k.c(c)  | --> i.c(a) *== k.c(c)  *)
       (*  - pred j = true      |                        *)
       let try_modus_ponens: int -> (int -> bool) -> t -> t option = fun i pred (g, p) -> 
	 if debug then print_debug "SL_DOMAIN: try modus ponens at %i t\n" i;
	 try
	   let ind0 = get (G.get_inductive i g) in
	     if pred ind0.target then failwith "predicate failure";
	     let ind1 = get (G.get_inductive ind0.target g) in
	       if List.exists2 (fun x y -> x!=y) ind0.target_parameters ind1.source_parameters
	       then failwith "arguments don't match";
	       let ind = 
		 { target = ind0.target;
		   source_parameters = ind0.source_parameters;
		   target_parameters = ind1.target_parameters;
		   length = if ind0.length==0 || ind1.length==0 then 0 else ind0.length+ind1.length;} in
	       let g = (G.remove_inductive i (G.remove_inductive ind0.target g)) in
		 Some (G.add_inductive i ind g, p)
	 with 
	   | Failure s ->  
	       if debug then print_debug "SL_DOMAIN: failed modus ponens at node %i: %s\n" i s;
	       None
	   | _ ->  
	       if debug then print_debug "SL_DOMAIN: failed modus ponens at node %i\n" i;
	       None

       let canonicalize: t -> t = fun t -> t
(* if P.is_live ind0.target p || G.is_reached ind0.target (fun j->i!=j) g then failwith ""; *)

       let pp: t -> string = fun (g, p) -> 
	 Printf.sprintf 
	   "***-------Print SL_DOMAIN --------***\n*** with inductive: %s ***\n%s%s" 
	   D.name (P.pp p) (G.pp g)
	   
     end: SL_DOMAIN)


module B = MAKE_SL_DOMAIN(DLList)

let _, t = B.malloc [Zero] B.empty
let i, t = B.malloc [RecordField("next",Zero); RecordField("prev",Zero); RecordField("top",Zero)] t
let t1 = get (B.try_fold i t)
let t1 = B.unfold i t1
let t1 = B.reduce_equalities t1

let _ = 
  Printf.printf "%s" (B.pp t);
  Printf.printf "%s" (B.pp t1)

module A = MAKE_SL_DOMAIN(TList)

let _, t = A.malloc [Zero] A.empty
let i, t = A.malloc [RecordField("next",Zero); RecordField("prev",Zero); RecordField("top",Zero)] t
let t1 = get (A.try_fold i t)
let t1 = A.unfold i t1
let t1 = A.reduce_equalities t1

let _ = 
  Printf.printf "%s" (A.pp t);
  Printf.printf "%s" (A.pp t1)
