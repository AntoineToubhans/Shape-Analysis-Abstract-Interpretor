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
(*                                  Last modified: AT 07/14/11 *)


let error(s: string) = failwith (Printf.sprintf "SL_DOMAIN_ERROR: %s" s)

module MAKE_SL_DOMAIN = 
  functor (D: INDUCTIVE_DEF) -> functor (O: OPTION) ->
    (struct
       
       module P = NEQ_DOMAIN(O)
       module G = SL_GRAPH_DOMAIN(O)
       module D = D

       let debug = O.debug

       type t = G.t * P.t
	   
       let p1: t -> G.t = fun (g, p) -> g
       let p2: t -> P.t = fun (g, p) -> p

       let prod: ('a -> G.t) -> ('a -> P.t) -> 'a -> t = fun g p a -> (g a, p a)

       let empty: t = G.empty, P.empty

       let clean: t -> t = fun (g, p) ->
	 if debug then print_debug "SL_DOMAIN: [Cleaning]\n";
	 let g = G.clean g in
	 let dom = G.domain g in
	   g, P.clean dom p

       let next: t -> int = fun (g, _) -> G.next g 
    	
       (* WARNING : doesn't check the length, and nullify anyway *)
       let nullify_inductive: int -> t -> t = fun i (g, p) ->
	 if debug then print_debug "SL_DOMAIN: nullify_inductive %i t\n" i;
	 try
	   let ind = get (G.get_inductive i g) in
	   let p = 
	     List.fold_left2 
	       (fun g x y -> P.add_eq x y g)
	       (P.add_eq i ind.Inductive.target p) 
	       ind.Inductive.source_parameters 
	       ind.Inductive.target_parameters in
	     (G.clean_node i (G.remove_inductive i g), p)
	 with
	   | No_value -> 
	       error (Printf.sprintf "can not nullify inductive from %i: there's no inductive" i)
	   | Invalid_argument _ ->	   
	       error (Printf.sprintf "can not nullify inductive from %i: ill-formed inductive" i)
		 
       let request_eq: int -> int -> t -> t = fun i j (g, p) ->
	 if debug then print_debug "SL_DOMAIN: request_eq %i %i t\n" i j;
	 if i!=j then
	   g, P.add_eq i j p
	 else
	   g, p

       let request_neq: int -> int -> t -> t = fun i j (g, p) ->
	 if debug then print_debug "SL_DOMAIN: request_neq %i %i t\n" i j;
	 g, P.check_bottom (P.add_neq i j p)    

       (* fusion i j t gets t true means i was deleted *)
       (* fusion i j t gets t false means j was deleted*)
       let fusion: int -> int -> t -> t*bool = fun i j (g, p) ->
	 if debug then print_debug "SL_DOMAIN: fusion %i %i t\n" i j;
	 if (i==0 && G.has_edges j g)||(j==0 && G.has_edges i g) then raise Bottom;
	 if P.is_live i p && P.is_live j p && i!=j then raise Bottom; 
	 let opt_ind_i = G.get_inductive i g and opt_ind_j = G.get_inductive j g
	 and do_fusion i j g p = 
	   if P.is_live j p then (G.fusion i j g, P.check_bottom (P.fusion i j p)), true 
	   else (G.fusion j i g, P.check_bottom (P.fusion j i p)), false 
	 in
	   if i==j then (g, p), true else  
	     match opt_ind_i, opt_ind_j, i, j with
	       | Some ind_i, Some ind_j, _, _ ->
		   if Inductive.is_positive ind_i && Inductive.is_positive ind_j then 
		     raise Bottom;
		   if Inductive.is_positive ind_i then 
		     let g, p = nullify_inductive j (g, p) in do_fusion i j g p
		   else if Inductive.is_positive ind_j then
		     let g, p = nullify_inductive i (g, p) in do_fusion i j g p
		   else if ind_i.Inductive.target == j then
		     (* i ==> j ==> k  can be handled directly *)
		     let g, p = nullify_inductive i (g, p) in do_fusion i j g p
		   else if ind_j.Inductive.target == i then 
		     (* j ==> i ==> k  can be handled directly *)
		     let g, p = nullify_inductive j (g, p) in do_fusion i j g p
		   else raise (Split (true, i))
	       | _, Some ind_j, 0, _ -> 
		   if Inductive.is_positive ind_j then raise Bottom;
		   let g, p = nullify_inductive j (g, p) in 
		     do_fusion j 0 g p
	       | Some ind_i, _, _, 0 -> 
		   if Inductive.is_positive ind_i then raise Bottom;
		   let g, p = nullify_inductive i (g, p) in
		     do_fusion i 0 g p
	       | _, _, _, _ -> 
		   do_fusion i j g p
		  
	     	     
       let reduce_equalities_one_step: t -> int list -> int list * t option = fun (g, p) l_pt ->
	 if debug then print_debug "SL_DOMAIN: reduce_equalities_one_step t...\n";
	 let rp = ref p in
	   match P.pop_equality rp with
	     | Some (i, j) ->
		 let t, b = fusion i j (g, !rp) in
		   List.map (fun k->(if b && k==i then j else if not b && k==j then i else k)) l_pt, Some(t)
	     | None -> l_pt, None
(*
       let reduce_equalities: t -> t = fun (g, p) ->
	 if debug then print_debug "SL_DOMAIN: reduce_equalities t...\n";
	 let rg = ref g and rp = ref p in
	 let eq = ref (P.pop_equality rp) in
	   while has !eq do
	     let i, j = get !eq in
	     let t, _ = fusion i j (!rg, !rp) in
	       rg:= fst t; rp:= snd t;
	       eq:= P.pop_equality rp
	   done;
	   if debug then print_debug "SL_DOMAIN: egalities reduced...\n";
	   !rg, !rp
*)    
       (* So far, is_bottom checks:               *)
       (*  - conflict between inductive and edges *)
       (*  - is_bottom over predicates            *)
       (*!! perfom a reduction of equalities      *)
       (*!! increases chance to get bottom        *)
       let is_bottom: t -> bool = fun (g, p) -> 
	 let check_node i = 
	   let opt_ind = G.get_inductive i g in
	     (has opt_ind && Inductive.is_positive (get opt_ind)) 
	     || List.exists (fun o -> G.has_edge i o g) D.domain_offset in
	 let b_result = P.is_bottom p || G.for_all check_node g in
	   if debug && b_result then print_debug "SL_DOMAIN: is t bottom?.....Yes\n"; 
	   if debug && not b_result then print_debug "SL_DOMAIN: is t bottom?.....No\n";b_result

       let create_fresh_node: t -> int * t = fun (g, p) ->
	 let i, g = G.create_fresh_node g in 
	   if debug then print_debug "SL_DOMAIN: create_fresh_node...[%i]\n" i; 
	   i, (g, p)
	   
       let malloc: offset list -> t -> int*t = fun ol (g, p) ->
	 if debug then print_debug "SL_DOMAIN: malloc [%s ]...\n" 
	   (List.fold_left (fun s o -> Printf.sprintf "%s %s" s (pp_offset o)) "" ol);
	 let i, g = G.create_fresh_node g in
	 let g = List.fold_left (fun g o -> G.add_edge i o 0 g) g ol in 
	 let p = IntSet.fold (fun j p -> if j!=i then P.add_neq i j p else p) (G.domain g) p in
	   i, (g, p)
	     
       let var_alloc: int -> offset list -> t -> t = fun i ol (g, p) ->
	 if debug then print_debug "SL_DOMAIN: var_alloc [%s ]...\n" 
	   (List.fold_left (fun s o -> Printf.sprintf "%s %s" s (pp_offset o)) "" ol);
	 let g = G.create_fresh_node_index i g in
	 let g = List.fold_left (fun g o -> G.add_edge i o 0 g) g ol in 
	 let p = IntSet.fold (fun j p -> if j!=i then P.add_neq i j p else p) (G.domain g) p in
	 let p = P.add_live i p in
	   (g, p)
	     
       let case_inductive_forward: int -> t -> t*t = fun i (g, p) ->
	 if debug then print_debug "SL_DOMAIN: case_inductive_forward %i t\n" i;
	 try
	   let ind = get (G.get_inductive i g) in
	     if ind.Inductive.length!=Inductive.Unknown then raise No_value;
	     let args, g0 = G.create_n_fresh_nodes D.number_of_parameters g in
	     let j, g0 = G.create_fresh_node g0 in
	     let ind0 = 
	       { Inductive.target = j;
		 Inductive.source_parameters = ind.Inductive.source_parameters;
		 Inductive.target_parameters = args;
		 length = Inductive.Length 1;}
	     and ind1 =  
	       { Inductive.target = ind.Inductive.target;
		 Inductive.source_parameters = args;
		 Inductive.target_parameters = ind.Inductive.target_parameters;
		 length = Inductive.Unknown;} in
	     let g0 = G.add_inductive j ind1 (G.update_inductive i ind0 g0) in
	       (g0, p), (nullify_inductive i (g, p))
	 with
	   | No_value -> 
	       error (Printf.sprintf "can not break inductive from %i: there's no inductive with no length" i)

       let case_inductive_backward: int -> t -> t*t = fun i (g, p) ->
	 if debug then print_debug "SL_DOMAIN: case_inductive_backward %i t\n" i;
	 try
	   let ind = get (G.get_inductive i g) in
	     if ind.Inductive.length!=Inductive.Unknown then raise No_value;
	     let args, g0 = G.create_n_fresh_nodes D.number_of_parameters g in
	     let j, g0 = G.create_fresh_node g0 in
	     let ind0 = 
	       { Inductive.target = j;
		 Inductive.source_parameters = ind.Inductive.source_parameters;
		 Inductive.target_parameters = args;
		 Inductive.length = Inductive.Unknown;}
	     and ind1 =  
	       { Inductive.target = ind.Inductive.target;
		 Inductive.source_parameters = args;
		 Inductive.target_parameters = ind.Inductive.target_parameters;
		 Inductive.length = Inductive.Length 1;} in
	     let g0 = G.add_inductive j ind1 (G.update_inductive i ind0 g0) in
	       (g0, p), (nullify_inductive i (g, p))
	 with
	   | No_value -> 
	       error (Printf.sprintf "can not break inductive from %i: there's no inductive with no length" i)

       let split_inductive_backward: int -> t -> t = fun i (g, p) ->
	 if debug then print_debug "SL_DOMAIN: split_inductive_backward %i t\n" i;
	 try
	   let ind = get (G.get_inductive i g) in
	   let length = 
	     match ind.Inductive.length with 
	       | Inductive.Length i -> i
	       | _ -> raise No_value in
	     if length < 2 then raise No_value;
	     let args, g = G.create_n_fresh_nodes D.number_of_parameters g in
	     let j, g = G.create_fresh_node g in
	     let ind0 = 
	       { Inductive.target = j;
		 Inductive.source_parameters = ind.Inductive.source_parameters;
		 Inductive.target_parameters = args;
		 Inductive.length = Inductive.Length (length-1);}
	     and ind1 =  
	       { Inductive.target = ind.Inductive.target;
		 Inductive.source_parameters = args;
		 Inductive.target_parameters = ind.Inductive.target_parameters;
		 Inductive.length = Inductive.Length 1;} in
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
	   let length = 
	     match ind.Inductive.length with 
	       | Inductive.Length i -> i
	       | Inductive.Unknown -> raise (Split (true, i)) in
	   let g = G.remove_inductive i g in
	   let fresh, g = G.create_n_fresh_nodes D.number_of_fresh g in
	   let g = List.fold_left2
	     (fun g j o -> G.add_edge i o j g) g fresh D.def_points_to_fresh in
	   let g = List.fold_left2
	     (fun g j o -> G.add_edge i o j g) 
	     g ind.Inductive.source_parameters D.def_points_to_parameters
	   and ind =
	     { Inductive.target = ind.Inductive.target;
	       Inductive.source_parameters = 
		 D.new_parameters i ind.Inductive.source_parameters fresh;
	       Inductive.target_parameters = ind.Inductive.target_parameters;
	       Inductive.length = Inductive.Length (length-1);} in
	   let g = G.add_inductive (List.hd fresh) ind g in
	     (* we reduced if the inductive has zero length *)
	   let g, p = if length==1 then 
	     nullify_inductive (List.hd fresh) (g, p) 
	   else 
	     g, p in
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
	   if not (List.mem o D.domain_offset) then
	     (* in this case, we can't do much better... *)
	     raise Top;
	   if G.has_inductive i g then
	     (* unfold can fail or raise Split *)
	     let g, p = unfold i (g, p) in
	       (* this can NOT fail *)
	       get (G.get_edge i o g), (g, p)
	   else 
	   (* first we check wether         *)
	   (*  D.F(node, args, fresh)       *)
	   (*  contains node somewhere      *)
	   (*  !!! kinda ugly style there ! *)
	   let rec mk i n acc = 
	     if n==0 then acc else mk i (n-1) (i::acc) in
	   let l = 
	     D.new_parameters 
	       1 (mk 0 D.number_of_parameters [])
	       (mk 0 D.number_of_fresh []) in
	   let rec get0 n l acc = 
	     match l with 
	       | [] -> acc 
	       | 1::l -> get0 (n+1) l (n::acc) 
	       | _::l -> get0 (n+1) l acc in
	   let pos_back = get0 0 l [] in
	     (* we get all the nodes j s.t.   *)
	     (*  j.ind(_) *= _.ind(d1,...,dn) *)
	     (*  i = some dk                  *)
	     if pos_back=[] then 
	       (* backtrack unfold research WILL fail *)
	       raise Top;
	     let p_candidates, u_candidates =  
	       G.fold
		 (fun j (p, u) -> 
		    match G.get_inductive j g with
		      | None -> p, u
		      | Some ind ->
			  if List.exists
			    (fun n -> List.nth ind.Inductive.target_parameters n=i) 
			    pos_back then
			      if ind.Inductive.length=Inductive.Unknown then
				p, (j::u)
			      else
				(j::p), u
			  else
			    p, u)
		 g ([], []) in 
	       (* so far, we have computed the set of candidates *)
	       (* - either it's empty: we raise Top              *)
	       (* - either it conatains one elements:            *)
	       (*   we try backward unfolding                    *)
	       (* - either it contains more elements:            *)
	       (*   we've to deal with conflicts...              *)
	       match p_candidates with
		 | [] -> 
		     if u_candidates=[] then 
		       raise Top
		     else
		       raise (Split(false, List.hd u_candidates))
		 | [j] ->
		     let g, p, j =
		       let ind = get (G.get_inductive j g) in 
			 if ind.Inductive.length = Inductive.Length 1 then
			   g, p, j
			 else
			   (* we have a finite inductive of length > 1 *)
			   let g, p = split_inductive_backward j (g, p) in
			     g, p, (get (G.get_inductive j g)).Inductive.target in 
		     let g, p = unfold j (g, p) in
		       (* we MUST have i=j in P *)
		       get (G.get_edge j o g), (g, p)
		 | j::_ -> raise Bottom

       let mutate: int -> offset -> int -> t -> t = fun i o j (g, p) ->
	 if debug then print_debug "SL_DOMAIN: mutate [%i%s := %i]\n" i (pp_offset o) j;
	 try 
	   G.add_edge i o j (G.remove_edge i o g), p
	 with
	   | _ ->
	       error (Printf.sprintf "can not perform mutation [%i%s := %i]" i (pp_offset o) j)

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
	     { Inductive.target = List.hd pt_fresh;
	       Inductive.source_parameters = pt_parameters;
	       Inductive.target_parameters = 
		 D.new_parameters i pt_parameters pt_fresh;
	       Inductive.length = Inductive.Length 1;} in
	   let g = 
	     List.fold_left 
	       (fun g o -> G.remove_edge i o g) 
	       g D.def_points_to_parameters in
	   let g = 
	     List.fold_left 
	       (fun g o -> G.remove_edge i o g) 
	       g D.def_points_to_fresh in
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
       (*  - pred j = false     |                        *)
       let try_modus_ponens: int -> (int -> bool) -> t -> t option = fun i pred (g, p) -> 
 	 if debug then print_debug "SL_DOMAIN: try modus ponens at %i t\n" i;
	 try
	   let ind0 = get (G.get_inductive i g) in
	     if pred ind0.Inductive.target then failwith "predicate failure";
	     let ind1 = get (G.get_inductive ind0.Inductive.target g) in
	       if List.exists2 (fun x y -> x!=y) 
		 ind0.Inductive.target_parameters 
		 ind1.Inductive.source_parameters
	       then failwith "arguments don't match";
	       let ind = 
		 { Inductive.target = ind1.Inductive.target;
		   Inductive.source_parameters = ind0.Inductive.source_parameters;
		   Inductive.target_parameters = ind1.Inductive.target_parameters;
		   Inductive.length =
		     Inductive.add_length 
		       ind0.Inductive.length
		       ind1.Inductive.length;} in
	       let g = 
		 (G.remove_inductive i  
		    (G.remove_inductive ind0.Inductive.target g)) in
		 Some (clean (G.add_inductive i ind g, p))
	 with 
	   | Failure s ->  
	       if debug then print_debug "SL_DOMAIN: failed modus ponens at node %i: %s\n" i s;
	       None
	   | _ ->  
	       if debug then print_debug "SL_DOMAIN: failed modus ponens at node %i\n" i;
	       None
	 

       let canonicalize: t -> t = fun t -> 
 	 if debug then print_debug "SL_DOMAIN: CANONICALIZATION\n";
(*	 print_debug "%s" (G.pp (fst t)); *)
	 let pred t j i = P.is_live i (snd t) || G.is_reached i (fun k->k!=j) (fst t) in
	 let nodes = ref (G.domain (fst t)) and rt = ref t in
	   (* first try to fold at every nodes *)
	   IntSet.iter (fun i -> map_default (fun x-> rt:= x) () (try_fold i !rt)) !nodes;
	   (* then we try modus ponens *)
	   while not (IntSet.is_empty !nodes) do
	     let i = IntSet.choose !nodes in
	       match try_modus_ponens i (pred !rt i) !rt with
		 | Some t -> rt:= t; 
		 | None -> nodes:= IntSet.remove i !nodes;
	   done; 
	   (* pretty dummy code             *)
	   (* forget about inductive length *)
(*	   G.fold 
	     (fun i g ->  
		if G.has_inductive i g then
		  let ind = get (G.get_inductive i g) in
		    G.update_inductive i (Inductive.forget_length ind) g
		else 
		  g) 
	     (fst !rt) (fst !rt), (snd !rt)	 *)
	   (G.forget_inductive_length (fst !rt)), (snd !rt)
	   

       let equals: t -> t -> bool = fun (g1, p1) (g2, p2) -> 
	 if debug then print_debug "SL_DOMAIN: checking [equals]\n";
	 let matching_nodes: int IntMap.t = 
	   List.fold_left 
	     (fun m i -> IntMap.add i i m)
	     IntMap.empty (P.get_lives p1) in
	   match G.equals matching_nodes matching_nodes g1 g2 with
	     | None -> false
	     | Some (m1, m2) -> P.equals m1 m2 p1 p2

       let is_include: t -> t -> bool = fun (g1, p1) (g2, p2) -> 
	 if debug then print_debug "SL_DOMAIN: checking [is_include]\n";
	 let matching_nodes: int IntMap.t = 
	   List.fold_left 
	     (fun m i -> IntMap.add i i m)
	     IntMap.empty (P.get_lives p1) in
	   (* on graphs, for now, inclusion is equality  *)
	   (* sound and sufficient with canonicalization *)
	   match G.equals matching_nodes matching_nodes g1 g2 with
	     | None -> false
	     | Some (m1, m2) -> P.is_include m1 m2 p1 p2

       let union: t -> t -> t option = fun t1 t2 ->
	 if debug then print_debug "SL_DOMAIN: computing [Union]\n";
	 if is_include t1 t2 then Some t2 
	 else if is_include t2 t1 then Some t1
	 else None

       let widening: t -> t -> t option = fun t1 t2 ->
	 if debug then print_debug "SL_DOMAIN: computing [Widening]\n";
	 let t2 = canonicalize t2 in
	   if is_include t1 t2 then Some t2 
	   else if is_include t2 t1 then Some t1
	   else None

       let pp: t -> unit = fun (g, p) -> 
	 O.XML.print_center 
	   (Printf.sprintf "SL DOMAIN with inductive of kind <b>%s</b>" D.name); 
	 O.XML.printf "<div class=\"box\">\n";
	 P.pp p;
	 G.pp g; 
	 O.XML.printf "</div>\n"


       let mk x y = 
	 if debug then print_debug "SL_DOMAIN: MAKE ********test purposes only!\n";
	 x, y

     end: SL_DOMAIN)

(*
module A = MAKE_SL_DOMAIN(DLList)

let p = A.P.empty
let p = A.P.add_live 1 p
let p = A.P.add_live 7 p
let p = A.P.add_neq 5 0 p

let g = A.G.empty
let g = A.G.add_edge 1 Zero 2 g
let g = A.G.add_inductive 2 
  { Inductive.target=3; 
    Inductive.source_parameters=[0]; 
    Inductive.target_parameters=[4]; 
    Inductive.length=Inductive.Unknown} g
let g = A.G.add_edge 3 (RecordField ("next", Zero)) 5 g
let g = A.G.add_edge 3 (RecordField ("prev", Zero)) 4 g
let g = A.G.add_edge 3 (RecordField ("top", Zero)) 6 g
let g = A.G.add_inductive 5 
  { Inductive.target=0; 
    Inductive.source_parameters=[3]; 
    Inductive.target_parameters=[0]; 
    Inductive.length=Inductive.Unknown} g
let g = A.G.add_edge 7 Zero 3 g
let g = A.G.add_edge 12 (RecordField ("method", Zero)) 11 g
let g = A.G.add_edge 8 (RecordField ("method", Zero)) 11 g
let g = A.G.add_edge 11 (RecordField ("method", Zero)) 32 g

let t1 = A.mk g p 

let p = A.P.empty
let p = A.P.add_live 1 p
let p = A.P.add_live 7 p
let p = A.P.add_neq 0 9 p

let g = A.G.empty
let g = A.G.add_edge 1 Zero 4 g
let g = A.G.add_inductive 4 
  { Inductive.target=5; 
    Inductive.source_parameters=[0]; 
    Inductive.target_parameters=[6]; 
    Inductive.length=Inductive.Unknown} g
let g = A.G.add_edge 5 (RecordField ("next", Zero)) 9 g
let g = A.G.add_edge 5 (RecordField ("prev", Zero)) 6 g
let g = A.G.add_edge 5 (RecordField ("top", Zero)) 8 g
let g = A.G.add_inductive 9 
  { Inductive.target=0; 
    Inductive.source_parameters=[5]; 
    Inductive.target_parameters=[0]; 
    Inductive.length=Inductive.Unknown} g
let g = A.G.add_edge 7 Zero 5 g
let g = A.G.add_edge 3 (RecordField ("method", Zero)) 2 g
let g = A.G.add_edge 17 (RecordField ("method", Zero)) 2 g
let g = A.G.add_edge 2 (RecordField ("method", Zero)) 21 g

let t2 = A.mk g p 

let _ = 
  Printf.printf "%s" (A.pp t1);
  Printf.printf "%s" (A.pp t2)

let _ = 
  if A.equals t1 t2 then Printf.printf "equals!\n"
*)
(*
let t, _ = A.case_inductive_backward 1 t

let _ = 
  Printf.printf "%s" (A.pp t)

let i, t = A.search 3 (RecordField ("next", Zero)) t


let _, ot = A.reduce_equalities_one_step t []
let t = get ot
let _, ot = A.reduce_equalities_one_step t []
let t = get ot


let _ = 
  Printf.printf "Found:%i in\n%s" i (A.pp t)
*)
  

(*
module A = MAKE_SL_DOMAIN(DLList)

let _, t = A.malloc [Zero] A.empty
let i, t = A.malloc [RecordField("next",Zero); RecordField("prev",Zero); RecordField("top",Zero)] t
let t1 = get (A.try_fold i t)
let t1 = A.unfold i t1
let _, ot2 = A.reduce_equalities_one_step t1 []
let t2 = get ot2
let _, ot3 = A.reduce_equalities_one_step t2 []
let t3 = get ot3

let _ = 
  Printf.printf "%s" (A.pp t);
  Printf.printf "%s" (A.pp t1);
  Printf.printf "%s" (A.pp t2);
  Printf.printf "%s" (A.pp t3)


*)
