open Offset
open Utils
open Domain_sig


let sld_error(s: string) = failwith (Printf.sprintf "SL_TL_DOMAIN_ERROR: %s" s)

module E = Eq_domain.EQ_Domain

(* =========================================================== *)
(* Module SL with tList (Toped Linked List)                    *)
(* a.tl(d) := {a = 0  | emp}                                   *)
(*         := {a!= 0  | a@n|->b * a@p|->c * a@t|->d * b.tl(d)  *)
(* =========================================================== *)
(*                                  Last modified: AT 06/14/11 *)

module SL_TL_GRAPH_Domain =
  (struct

     let domainId = 4

     let debug = true

     exception Fusion_error
     exception Unfolding_error of string
     exception Folding_error of string
     exception Request_unfolding of int
     exception Can_not_defferentiate
    
     type inductive = 
       | Emp
       | Ind_TL of int (* Ind_TL d means i.tl(d) *)
       | Seq_TL of int*int  (* Seq_TL(d, j) means i.tl(d) *-- j.tl(d) *)

     type node =
	 { id          : int;
	   simple_edges: int OffsetMap.t;
	   induct_edge : inductive;}
	   (*  is_reach    : bool;}  GOOD IDEA??? *)
	   (* is_reached: is the node reached in the ABSTRACT graph?                          *)
	   (* it may not be reached in the abstract graph but be reach on some concrete store *)
	
     type t =    
	 { nodes  : node IntMap.t;
	   next   : int;} (* next fresh node *)

     let empty: t =
       { nodes= IntMap.empty;
	 next= 0;}

     let hasInduct: node -> bool = fun n ->
       match n.induct_edge with
	 | Emp -> false
	 | _ -> true

     let hasSeq_TL: node -> (int*int) option = fun n ->
       match n.induct_edge with
	 | Seq_TL(d, j) -> Some(d, j)
	 | _ -> None

     let hasInd_TL: node -> int option = fun n ->
       match n.induct_edge with
	 | Ind_TL d -> Some d
	 | _ -> None

     let hasEdge: offset -> node -> int option = fun o n ->
       try Some (OffsetMap.find o n.simple_edges)
       with | Not_found -> None

     let hasEdgeN: node -> int option = hasEdge (RecordField("n", Zero))
     let hasEdgeT: node -> int option = hasEdge (RecordField("t", Zero)) 
     let hasEdgeP: node -> int option = hasEdge (RecordField("p", Zero)) 
	     
     (* check whether there's a j!= k s.t. j@o->i or j.tl(_) *= i.tl(_) *)
     let node_is_reached: t -> int -> int option -> bool = fun t i ok ->
       if debug && has ok then 
	 print_debug "SL_TL_GRAPH_DOMAIN:check whether Node(%i) is reached [except from Node(%i)]...." i (get ok);
       if debug && hasnot ok then
	 print_debug "SL_TL_GRAPH_DOMAIN:check whether Node(%i) is reached......" i;   
       let check_node: int -> node -> bool = fun j n ->
	 if (map_default (fun k -> j==k) false ok) then false else
	   match n.induct_edge with
	     | Seq_TL(d, j) -> i==j || (OffsetMap.exists (fun o j -> i==j) n.simple_edges)  
	     | _ -> (OffsetMap.exists (fun o j -> i==j) n.simple_edges) in
       let reached = IntMap.exists check_node t.nodes in
	 if debug && reached then print_debug "Yes\n";
	 if debug && not reached then print_debug "No\n";
	 reached
 
     (* is o equals to "n" or "p" or "t"? *)
     let isIndOffset: offset -> bool = fun o -> 
       Offset.equals o (RecordField("t", Zero)) ||
       Offset.equals o (RecordField("p", Zero)) || 
       Offset.equals o (RecordField("n", Zero)) 

     (* add_edge t i o j  adds i@o|--->j to t*)
     let add_edge: t -> int -> offset -> int -> t = fun t i o j -> 
       if debug then print_debug "SL_TL_GRAPH_DOMAIN:add_edge t %i %s %i\n" i (offset2str o) j;
       try 
	 let n = IntMap.find i t.nodes in 
	   if OffsetMap.mem o n.simple_edges 
	   then sld_error 
	     (Printf.sprintf "Separation issue: %i%s already set" i (offset2str o));
	   if hasInduct n && isIndOffset o
	   then sld_error 
	     (Printf.sprintf 
		"Separation issue: cannot set %i%s because an inductive already occurs on node(%i)" i (offset2str o) i);
	   let n = 
	     {n with simple_edges = OffsetMap.add o j n.simple_edges} in
	     {nodes = IntMap.add i n t.nodes;
	      next = max t.next (j+1);}	     
       with 
	 | Not_found ->
	     let n = 
	       { id = i;
		 simple_edges = OffsetMap.singleton o j;
		 induct_edge = Emp;} in
	       { nodes = IntMap.add i n t.nodes;
		 next = max t.next ((max i j)+1);}

     (* add_int t i d  adds i.tl(d) to t*)
     let add_ind: t -> int -> int -> t = fun t i d ->
       if debug then print_debug "SL_TL_GRAPH_DOMAIN:add_ind t %i %i\n" i d;
       try 
	 let n = IntMap.find i t.nodes in 
	 let f_err = fun o -> 
	   if OffsetMap.mem o n.simple_edges 
	   then sld_error 
	     (Printf.sprintf 
		"Separation issue: cannot set an inductive on node(%i) because %i%s is already set" i i (offset2str o)) in
	   f_err (RecordField("n", Zero));
	   f_err (RecordField("p", Zero));
	   f_err (RecordField("t", Zero));
	   if hasInduct n 
	   then sld_error 
	     (Printf.sprintf "Separation issue: an inductive is already set on node(%i)" i);
	   let n = 
	     {n with induct_edge = Ind_TL d} in
	     {t with nodes = IntMap.add i n t.nodes}
       with 
	 | Not_found ->
	     let n = 
	       { id = i;
		 simple_edges = OffsetMap.empty;
		 induct_edge = Ind_TL d;} in
	       { nodes = IntMap.add i n t.nodes;
		 next = max t.next (i+1);}

     (* add_seq t i d j adds i.tl(d) *-- j.tl(d)  to t*)
     let add_seq: t -> int -> int -> int -> t = fun t i d j ->
       if debug then print_debug "SL_TL_GRAPH_DOMAIN:add_seq t %i %i %i\n" i d j;
       try 
	 let n = IntMap.find i t.nodes in 
	 let f_err = fun o -> 
	   if OffsetMap.mem o n.simple_edges 
	   then sld_error 
	     (Printf.sprintf 
		"Separation issue: cannot set an inductive because %i%s is already set" i (offset2str o)) in
	   f_err (RecordField("n", Zero));
	   f_err (RecordField("p", Zero));
	   f_err (RecordField("t", Zero));
	   if hasInduct n 
	   then sld_error 
	     (Printf.sprintf "Separation issue: an inductive is already set on node(%i)" i);
	   let n = 
	     {n with induct_edge = Seq_TL(d, j)} in
	     {nodes = IntMap.add i n t.nodes;
	      next = max t.next (j+1);}	     
       with  
	 | Not_found ->
	     let n = 
	       { id = i;
		 simple_edges = OffsetMap.empty;
		 induct_edge = Seq_TL(d, j);} in
	       { nodes = IntMap.add i n t.nodes;
		 next = max t.next ((max i j)+1);}

     let node_is_empty: node -> bool = fun n ->
       let emp=OffsetMap.is_empty n.simple_edges && n.induct_edge==Emp in
	 if debug && emp then print_debug "SL_TL_GRAPH_DOMAIN:check if Node(%i) is empty.....Yes" n.id;
	 if debug && not emp then print_debug "SL_TL_GRAPH_DOMAIN:check if Node(%i) is empty.....No" n.id;
	 emp

     let nodeEmpty: int -> t -> bool = fun i t ->
       try 
	 node_is_empty (IntMap.find i t.nodes)
       with
	 | Not_found -> true

     (* !!! do not fully remove Node(i), it may be j@n->i or ... *)
     let remove_node: t -> int -> t = fun t i ->
       if debug then print_debug "SL_TL_GRAPH_DOMAIN:remove_node t %i" i;
       { nodes = IntMap.remove i t.nodes;
	 next = if i+1=t.next && not (node_is_reached t i (Some i)) then i else t.next;} 

     let remove_induct: t -> int -> t = fun t i ->
       if debug then print_debug "SL_TL_GRAPH_DOMAIN:remove_induct t %i" i;
       try 
	 let n = IntMap.find i t.nodes in
	 let nn = {n with induct_edge = Emp} in
	   if node_is_empty nn then remove_node t i else
	     {t with nodes = IntMap.add i nn t.nodes}
       with 
	 | Not_found -> t

     let remove_edge: t -> int -> offset -> t = fun t i o ->
       if debug then print_debug "SL_TL_GRAPH_DOMAIN:remove_edge t %i %s" i (offset2str o);
       try 
	 let n = IntMap.find i t.nodes in
	 let nn = {n with simple_edges = OffsetMap.remove o n.simple_edges} in
	   if node_is_empty nn then remove_node t i else
	     {t with nodes = IntMap.add i nn t.nodes}
       with 
	 | Not_found -> t
	   

     (* fusion i j deletes i *)
     let fusion_node: t -> int -> int -> t = fun t i j -> 
       if debug then print_debug "SL_TL_GRAPH_DOMAIN:fusion_node t %i %i\n" i j;
       let change_index = fun k-> if i==k then j else k in
       let change_inductive = fun ind -> 
	 match ind with
	   | Emp -> Emp
	   | Ind_TL k -> Ind_TL (change_index k)
	   | Seq_TL(d, k) -> Seq_TL((change_index d), (change_index k)) in
       let renaming_f = fun no -> 
	 { id = no.id;
	   simple_edges = OffsetMap.map change_index no.simple_edges;
	   induct_edge = change_inductive no.induct_edge;} 
       and merging_simple_edge = fun o (oi: int option) (oj: int option) ->
	 match oi, oj with
	   | Some i, Some j -> 
	       raise Fusion_error (*this shouldn'd happen*)
	   | Some i, _ -> oi
	   | _, _ -> oj 
       and merging_induct_edge = fun aa bb -> 
	 match aa, bb with 
	   | _, Emp -> aa
	   | Emp, _ -> bb
	   | _, _ -> 
	       raise Fusion_error in (*this shouldn'd happen (?)*)
       let merge_node: node-> node-> node = fun n m ->
	 {id=j; 
	  simple_edges = OffsetMap.merge merging_simple_edge n.simple_edges m.simple_edges;
	  induct_edge = merging_induct_edge n.induct_edge m.induct_edge;} in
       let n = 
	 try Some (IntMap.find i t.nodes)
	 with Not_found -> None in
       let m = 
	 try Some (IntMap.find j t.nodes)
	 with Not_found -> None in
	 match n, m with
	   | Some n, Some m ->	       
	       {nodes = IntMap.map renaming_f (IntMap.add j (merge_node n m) (IntMap.remove i t.nodes));
		next  = if t.next==i+1 then i else t.next;}
	   | Some n, None ->
	       {nodes = IntMap.map renaming_f (IntMap.add j {n with id=j} (IntMap.remove i t.nodes));
		next  = if t.next==i+1 then i else t.next;}
	   | None, _ ->
	       {nodes = IntMap.map renaming_f t.nodes;
		next  = if t.next==i+1 then i else t.next;}		   
	       

     (* ====== serious stuff ====== *)

     let unfold: t -> int -> (t* E.r) list = fun t i -> 
       if debug then print_debug "SL_TL_GRAPH_DOMAIN:unfold t %i\n" i;
       try 
	 let n = IntMap.find i t.nodes in
	   match n.induct_edge with
	     | Ind_TL j ->
		 if has (hasEdgeT n) || has (hasEdgeP n) || has (hasEdgeN n)
		 then sld_error "Separation issue";
		 (* new node i *)
		 let m =   
		   { id = n.id;  
		     simple_edges= 
		       OffsetMap.add 
			 (RecordField("p", Zero)) 
			 (t.next + 1) 
			 (OffsetMap.add 
			    (RecordField("n", Zero)) 
			    t.next 
			    (OffsetMap.add (RecordField("t", Zero)) j n.simple_edges));
		     induct_edge= Emp;} 
		 (* new node pointed by i@n *)
		 and nn = 
		   { id = t.next;
		     simple_edges=OffsetMap.empty;
		     induct_edge=Ind_TL j;} in
		 let new_t = 
		   { nodes=IntMap.add t.next nn (IntMap.add i m t.nodes);
		     next= t.next+2;} in
		   if OffsetMap.is_empty n.simple_edges
		   then 
		     begin
		       if debug then print_debug "SL_TL_GRAPH_DOMAIN:Unfolding Ind_TL produces 2 graphs\n";
		       [({t with nodes=IntMap.add i {n with induct_edge=Emp} t.nodes}, E.add_null i);
			(new_t, E.add_notnull i)]
		     end
		   else
		     begin
		       if debug then print_debug "SL_TL_GRAPH_DOMAIN:Unfolding Ind_TL produces only one graph\n";
		       [(new_t, E.add_notnull i)] 
		     end
	     | Seq_TL(j, k) ->
		 if has (hasEdgeT n) || has (hasEdgeP n) || has (hasEdgeN n)
		 then sld_error "Separation issue"; (* this shouldn't happen! *)
		 (* new node i *)
		 let m =    
		   { id = n.id;  
		     simple_edges= 
		       OffsetMap.add 
			 (RecordField("p", Zero)) 
			 (t.next + 1) 
			 (OffsetMap.add 
			    (RecordField("n", Zero)) 
			    t.next 
			    (OffsetMap.add (RecordField("t", Zero)) j n.simple_edges));
		     induct_edge= Emp;} in
		 (* new node pointed by i@n *)
		 let nn = 
		   { id = t.next;
		     simple_edges=OffsetMap.empty;
		     induct_edge=Seq_TL(j, k);} in	
		 let t2 = 
		   { nodes=IntMap.add t.next nn (IntMap.add i m t.nodes);
		     next= t.next+2;} in
		   begin
		     try
		       let t3 = fusion_node {t with nodes=IntMap.add i {n with induct_edge=Emp} t.nodes} i k in
			 if debug then print_debug "SL_TL_GRAPH_DOMAIN:Unfolding Seq_TL produces 2 graphs\n";
			 [(t3, E.fusion_node i k); (t2, E.add_notnull i)] 
		     with
		       | Fusion_error -> 
			   if debug then print_debug "SL_TL_GRAPH_DOMAIN:Unfolding Seq_TL only produces one graph\n";
			   [(t2, E.add_notnull i)] (* shall I catch this exception ? *)
		   end			 
	     | Emp -> 
		 raise (Unfolding_error (Printf.sprintf "no inductives from node(%i)" i)) 
       with 
	 | Not_found -> 
	     raise (Unfolding_error (Printf.sprintf "node(%i) doesn't exist" i))


     (* dir_bckw_unfold t i unfold i.tl(d) *-- j.tl(d) onto i.tl(d) *-- k.tl(d) * k@n|-> j *)
     let dir_bckw_unfold: t -> int -> t list = fun t i ->
      if debug then print_debug "SL_TL_GRAPH_DOMAIN:dir_bckw_unfold t %i\n" i;
      try 
	 let n = IntMap.find i t.nodes in
	   match n.induct_edge with	     
	     | Seq_TL(d, j) ->
		 if OffsetMap.mem (RecordField("t", Zero)) n.simple_edges 
		   || OffsetMap.mem (RecordField("n", Zero)) n.simple_edges 
		   || OffsetMap.mem (RecordField("p", Zero)) n.simple_edges 
		 then sld_error "Separation issue"; (* this shouldn't happen! *)
		 (* new node i *)
		 let m =    
		   { n with induct_edge = Seq_TL(d, t.next)} in
		 (* new node t.next *)
		 let next = 
		   { id = t.next;
		     simple_edges=
                       OffsetMap.add
                         (RecordField("n", Zero))
                         j
                         (OffsetMap.add 
                           (RecordField("p", Zero))
                           (t.next+1)
                           (OffsetMap.singleton (RecordField("t", Zero)) d));
		     induct_edge=Emp;} in	         
		 let t2 = 
		   { nodes=IntMap.add t.next next (IntMap.add i m t.nodes);
		     next= t.next+2;} in
		   begin
		     try
		       [fusion_node {t with nodes=IntMap.add i {n with induct_edge=Emp} t.nodes} i j; t2] 
		     with
		       | Fusion_error -> [t2] (* shall I catch this exception ? *)
		   end			 
	     | _ -> 
		 raise (Unfolding_error (Printf.sprintf "no sequence from node(%i), can't unfold backward" i)) 
       with 
	 | Not_found -> 
	     raise (Unfolding_error (Printf.sprintf "node(%i) doesn't exist" i))
  

     let backward_unfold: t -> int -> t list = fun t i ->
       if debug then print_debug "SL_TL_GRAPH_DOMAIN:backward_unfold t %i\n" i;
       (* first we'll try to find all nodes j s.t. j.tl(d) *-- i.tl(d) *)
       let ffilter: int-> node-> bool = fun j n -> 
	 match n.induct_edge with |Seq_TL(d, k) -> k==i |_ -> false in
       let map = IntMap.filter ffilter t.nodes in
       let ffold: int-> node-> t list-> t list = fun i n l -> 
         List.append (dir_bckw_unfold t i) l
       in
	 IntMap.fold ffold map []	 
   	 

     let fold: t -> int -> t = fun t i -> 
       if debug then print_debug "SL_TL_GRAPH_DOMAIN:fold t %i\n" i;
       try 
	 let n = IntMap.find i t.nodes in
	   if hasInduct n then 
	     raise (Folding_error (Printf.sprintf "node(%i) already has an inductive" i));
	   if has (hasEdgeN n) then 
	     raise (Folding_error(Printf.sprintf "%i%s isn't set" i (offset2str (RecordField("n", Zero)))));
	   if has (hasEdgeP n) then 
	     raise (Folding_error(Printf.sprintf "%i%s isn't set" i (offset2str (RecordField("p", Zero)))));
	   if has (hasEdgeT n) then 
	     raise (Folding_error(Printf.sprintf "%i%s isn't set" i (offset2str (RecordField("t", Zero)))));
	   let new_n = 
	     {id           = n.id;
	      simple_edges = 
		 OffsetMap.remove 
		   (RecordField("t", Zero)) 
		   (OffsetMap.remove 
		      (RecordField("p", Zero)) 
		      (OffsetMap.remove (RecordField("n", Zero)) n.simple_edges));
	      induct_edge  = 
		 Seq_TL(
		   OffsetMap.find (RecordField("t", Zero)) n.simple_edges, 
		   OffsetMap.find (RecordField("n", Zero)) n.simple_edges);} in
	     {t with nodes=IntMap.add i new_n t.nodes}
       with 
	 | Not_found -> 
	     raise (Folding_error (Printf.sprintf "node(%i) doesn't exist" i))         

     (* ======================= CANONICALIZATION ========================= *)
     (* Args:                                                              *)
     (* - t: t              the one which's gonna be canonicalized         *)
     (* - lives: int list   nodes pointed by a program variable            *)
     (* - nulls: int list   nodes which are null thru constraints          *)
     (*        Rq: the intersection of lives and nulls is empty            *)
     (* Rules:                                                             *)
     (* (I) Sequence points to null                                        *)
     (*             M * (a.tl(d) *= b.tl(d))   /\  b in nulls              *)
     (*             _________________________________________              *)
     (*                             M * a.tl(d)                            *)
     (* (II.1)                                                             *)
     (*              M * (a.tl(d) *= b.tl(d)) * b.tl(d)                    *) 
     (*         /\  b not in lives /\ b isn't pointed by anything          *)
     (*     _____________________________________________________          *)
     (*                           M * a.tl(d)                              *)
     (* (II.2)                                                             *)
     (*          M * (a.tl(d) *= b.tl(d)) * (b.tl(d) *= c.tl(d))           *)
     (*         /\  b not in lives /\ b isn't pointed by anything          *)
     (*   ____________________________________________________________     *)
     (*                    M * (a.tl(d) *= c.tl(d)                         *)
     (* (III.1) folding                                                    *)
     (*                  M * a@n->a1 * a@p->c * a@t->d *                   *)
     (*                   a1@n->b * a1@p->c1 * a1@t->d                     *)
     (*        /\ a1 is not in lives /\ a1 isn't pointed by anything       *)
     (*   ______________________________________________________________   *)
     (*                     M * (a.tl(d) *= b.tl(d))                       *)
     (* (III.2left) folding                                                *)
     (*       M * (a.tl(d) *= b.tl(d)) * b@n->b1 * b@t->d * b@p->c         *)
     (*        /\ b is not in lives /\ b isn't pointed by anything         *)
     (*   ______________________________________________________________   *)
     (*                     M * (a.tl(d) *= b1.tl(d)                       *)
     (* (III.2right) folding                                               *)
     (*        M * a@n->b * a@t->d * a@p->c * (b.tl(d) *= b1.tl(d))        *)
     (*        /\ b is not in lives /\ b isn't pointed by anything         *)
     (*   ______________________________________________________________   *)
     (*                     M * (a.tl(d) *= b1.tl(d)                       *)
     (* (III.3) folding                                                    *)
     (*              M * a@n->b * a@t->d * a@p->c * b.tl(d)                *)
     (*        /\ b is not in lives /\ b isn't pointed by anything         *)
     (*   ______________________________________________________________   *)
     (*                            M *  a.tl(d)                            *)
     (* Strategy: (III_)* -> (II_)* -> I^1                                 *)
     (* ================================================================== *)

     let ruleI: t -> int list -> int list -> t = fun t lives nulls ->
       if debug then print_debug "SL_TL_GRAPH_DOMAIN:*Applying rule (I) globally\n";
       let ruleInode: node -> node = fun n ->
	 match n.induct_edge with
	   | Seq_TL(d, j) -> 
	       if List.mem j nulls 
	       then {n with induct_edge=Ind_TL d}
	       else n
	   | _ -> n in
	 {t with nodes= IntMap.map ruleInode t.nodes}

     let ruleII1: int list -> int -> t -> t = fun lives i t ->
       try 
	 let nn = IntMap.find i t.nodes in
	 let d0, j  = get (hasSeq_TL nn) in
	   if node_is_reached t j (Some i)|| List.mem j lives then 
	     raise (Folding_error "ruleII1")
	   else
	     let mm = IntMap.find j t.nodes in
	     let d1 = get (hasInd_TL mm) in
	       if d0!=d1 || not (OffsetMap.is_empty mm.simple_edges) then 
		 raise (Folding_error "ruleII1")
	       else
		 (* i and j are not equal *)
		 { nodes = IntMap.add i {nn with induct_edge=Ind_TL d0} (IntMap.remove j t.nodes); 
		   next  = if j+1=t.next then j else t.next;}
       with
	 | No_value | Not_found -> raise (Folding_error "ruleII1")

    let ruleII2: int list -> int -> t -> t = fun lives i t -> 
       try
	 let nn = IntMap.find i t.nodes in 
	 let d0, j  = get (hasSeq_TL nn) in
	   (* !!! in some weird case, i and j may be equal !!! *)
	   if node_is_reached t j (Some i)|| List.mem j lives || i==j then  
	     raise (Folding_error "ruleII2")
	   else
	     let mm = IntMap.find j t.nodes in
	     let d1, k = get (hasSeq_TL mm) in
	       if d0!=d1 || not (OffsetMap.is_empty mm.simple_edges) then 
		 raise (Folding_error "ruleII2")
	       else
		 { nodes = IntMap.add i {nn with induct_edge=Seq_TL(d0, k)} (IntMap.remove j t.nodes); 
		   next  = if j+1=t.next then j else t.next;}
       with
	 | No_value | Not_found -> raise (Folding_error "ruleII2")

 
     let ruleIII1: int list -> int -> t -> t = fun lives i t ->
       try
	 let n = IntMap.find i t.nodes in 
	 let i0 = get (hasEdgeN n) and d0 = get (hasEdgeT n) in
	 let n0 = IntMap.find i0 t.nodes in 
	 let i1 = get (hasEdgeN n0) and d1 = get (hasEdgeT n0) in
	   if 
	     hasnot (hasEdgeP n0) || hasnot (hasEdgeP n) 
	     || node_is_reached t i0 (Some i) || List.mem i0 lives
	     || OffsetMap.exists (fun o k -> not (isIndOffset o)) n0.simple_edges
	     || d0!=d1 || i==i0
	   then 
	     raise (Folding_error "ruleIII1")
	   else
	     let nn = 
	       { id           = i;
		 simple_edges = OffsetMap.remove 
		   (RecordField("t", Zero)) 
		   (OffsetMap.remove 
		      (RecordField("n", Zero)) 
		      (OffsetMap.remove (RecordField("p", Zero)) n.simple_edges));
		 induct_edge  = Seq_TL(d0, i1);} in
	       { nodes = IntMap.add i nn (IntMap.remove i0 t.nodes);
		 next  = if i0+1=t.next then i0 else t.next;}
       with 
	 | Not_found | No_value -> raise (Folding_error "ruleIII1")

     let ruleIII2left: int list -> int -> t -> t = fun lives i t -> 
       try
	 let n = IntMap.find i t.nodes in 
	 let d0, i0 = get (hasSeq_TL n) in
	 let n0 = IntMap.find i0 t.nodes in 
	 let j = get (hasEdgeN n0) and d1 = get (hasEdgeT n0) in
	   if 
	     hasnot (hasEdgeP n0)  
	     || node_is_reached t i0 (Some i) || List.mem i0 lives
	     || OffsetMap.exists (fun o k -> not (isIndOffset o)) n0.simple_edges 
	     || d0!=d1
	   then
	     raise (Folding_error "ruleIII2left")
	   else
	     let nn = {n with induct_edge = Seq_TL(d0, j)} in
	       { nodes = IntMap.add i nn (IntMap.remove i0 t.nodes);
		 next  = if i0+1=t.next then i0 else t.next;}
       with 
	 | Not_found | No_value -> raise (Folding_error "ruleIII2left")

     let ruleIII2right: int list -> int -> t -> t = fun lives i t -> 
       try
	 let n = IntMap.find i t.nodes in 
	 let i0 = get (hasEdgeN n) and d0 = get (hasEdgeT n) in
	 let n0 = IntMap.find i0 t.nodes in 
	 let d1, j = get (hasSeq_TL n0) in
	   if 
	     hasnot (hasEdgeP n) 
	     || node_is_reached t i0 (Some i) || List.mem i0 lives
	     || not (OffsetMap.is_empty n0.simple_edges)
	     || d0!=d1 
	   then
	     raise (Folding_error "ruleIII2right")
	   else
	     let nn = 
	       { id           = i;
		 simple_edges = OffsetMap.remove 
		   (RecordField("t", Zero)) 
		   (OffsetMap.remove 
		      (RecordField("n", Zero)) 
		      (OffsetMap.remove (RecordField("p", Zero)) n.simple_edges));
		 induct_edge  = Seq_TL(d0, j);} in
	       { nodes = IntMap.add i nn (IntMap.remove i0 t.nodes);
		 next  = if i0+1=t.next then i0 else t.next;}
       with 
	 | Not_found | No_value -> raise (Folding_error "ruleIII2right")

     let ruleIII3: int list -> int -> t -> t = fun lives i t -> 
       try
	 let n = IntMap.find i t.nodes in 
	 let i0 = get (hasEdgeN n) and d0 = get (hasEdgeT n) in
	 let n0 = IntMap.find i0 t.nodes in 
	 let d1 = get (hasInd_TL n0) in
	   if 
	     hasnot (hasEdgeP n) 
	     || node_is_reached t i0 (Some i) || List.mem i0 lives
	     || not (OffsetMap.is_empty n0.simple_edges)
	     || d0!=d1 
	   then
	     raise (Folding_error "ruleIII3")
	   else
	     let nn = 
	       { id           = i;
		 simple_edges = OffsetMap.remove 
		   (RecordField("t", Zero)) 
		   (OffsetMap.remove 
		      (RecordField("n", Zero)) 
		      (OffsetMap.remove (RecordField("p", Zero)) n.simple_edges));
		 induct_edge  = Ind_TL(d0);} in
	       { nodes = IntMap.add i nn (IntMap.remove i0 t.nodes);
		 next  = if i0+1=t.next then i0 else t.next;}
       with 
	 | Not_found | No_value -> raise (Folding_error "ruleIII3")

     let canonicalize: t -> int list -> int list -> t = fun t lives nulls -> 
       if debug then print_debug "SL_TL_GRAPH_DOMAIN:**CANONICALIZATION\n";
       let choose_not_treated_node: int list -> t -> (int * node) option = fun l t ->
	 try 
	   Some (IntMap.choose (IntMap.filter (fun i n -> not (List.mem i l)) t.nodes)) 
	 with | Not_found -> None in
       let treated_nodes: (int list) ref = ref []
       and current_t: t ref = ref t 
       and current_n: ((int * node) option) ref = ref (choose_not_treated_node [] t) 
       and reduced: bool ref = ref true in
	 while has !current_n do
	   reduced:= true;
	   let i = fst (get !current_n) and n = snd (get !current_n) in
	     if has (hasEdgeN n) then 
	       begin
		 reduced:= false;
		 try current_t:= ruleIII3 lives i !current_t;
		   if debug then print_debug "SL_TL_GRAPH_DOMAIN:*Rule (III3) applied to Node(%i)\n" i 
		 with | Folding_error _ ->
		 try current_t:= ruleIII2right lives i !current_t;
		   if debug then print_debug "SL_TL_GRAPH_DOMAIN:*Rule (III2left) applied to Node(%i)\n" i 
	         with | Folding_error _ ->
	         try current_t:= ruleIII1 lives i !current_t;
		   if debug then print_debug "SL_TL_GRAPH_DOMAIN:*Rule (III1) applied to Node(%i)\n" i 
	         with | Folding_error _ -> reduced:= true
	       end;
	     if has (hasSeq_TL n) then
	       begin
		 reduced:= false;
	         try current_t:= ruleIII2left lives i !current_t;
		   if debug then print_debug "SL_TL_GRAPH_DOMAIN:*Rule (III2left) applied to Node(%i)\n" i 
	         with | Folding_error _ ->
	         try current_t:= ruleII2 lives i !current_t;
		   if debug then print_debug "SL_TL_GRAPH_DOMAIN:*Rule (II2) applied to Node(%i)\n" i 
	         with | Folding_error _ ->
	         try current_t:= ruleII1 lives i !current_t;
		   if debug then print_debug "SL_TL_GRAPH_DOMAIN:*Rule (II1) applied to Node(%i)\n" i 
	         with | Folding_error _ -> reduced:= true
	       end;	  
	     if !reduced then 
	       begin
		 treated_nodes:= i::(!treated_nodes);
		 if debug then print_debug "SL_TL_GRAPH_DOMAIN:*Node(%i) fully reduced\n" i; 
		 current_n := choose_not_treated_node !treated_nodes !current_t 
	       end;
	 done; 
	 ruleI !current_t lives nulls


     let find: t -> int -> offset -> offseted_node list = fun t i o ->
       if debug then print_debug "SL_TL_GRAPH_DOMAIN: finding edges from Node(%i)%s...\n" i (offset2str o);
       try 
	 let n = IntMap.find i t.nodes 
	 and ffold: offset -> int -> offseted_node list -> offseted_node list = fun oo j l ->
	   try (j, (replaceOffset oo o Zero))::l with | Offset_error _ -> l in 
	   if (isIndOffset o || Offset.equals o Zero) && hasInduct n then raise (Request_unfolding i);  
	   OffsetMap.fold ffold (IntMap.find i t.nodes).simple_edges []
       with 
	 | Not_found -> []

     let deffer: t -> int -> offset -> int = fun t i o ->
       if debug then print_debug "SL_TL_GRAPH_DOMAIN: defferentiate from Node(%i)%s...\n" i (offset2str o);
       try 
	 let n = IntMap.find i t.nodes in
	   if isIndOffset o && hasInduct n then raise (Request_unfolding i);  
	   get (hasEdge o n)
       with 
	 | Not_found | No_value -> raise Can_not_defferentiate

     let domain: t -> int list = fun t ->
       let ffold o j l = j::l in
       let fffold i n l =
	 match n.induct_edge with 
	   |Seq_TL(d, j) -> i::d::j::(OffsetMap.fold ffold n.simple_edges l)
	   |Ind_TL(d) -> i::d::(OffsetMap.fold ffold n.simple_edges l)
	   |_ -> i::(OffsetMap.fold ffold n.simple_edges l)
       in
	 IntMap.fold fffold t.nodes []

     let pp_node: node -> string = fun n ->
       let s = Printf.sprintf "Node(%i):\n========\n" n.id in
       let f = fun o j s -> Printf.sprintf "%s %i%s|---> %i\n" s n.id (offset2str o) j in
       let s = OffsetMap.fold f n.simple_edges s in 
	 match n.induct_edge with
	   | Emp -> s
	   | Ind_TL j -> Printf.sprintf "%s %i.tl(%i)\n" s n.id j
	   | Seq_TL(j, k) -> Printf.sprintf "%s %i.tl(%i) *== %i.tl(%i)\n" s n.id j k j
	      
     let pp: t -> string = fun t ->
       let s = Printf.sprintf "---Print SL_tList symbolic heap---\nNext free node:%i\n" t.next in
	 IntMap.fold (fun i n s -> Printf.sprintf "%s%s" s (pp_node n)) t.nodes s

   end: SL_GRAPH_DOMAIN)





 


