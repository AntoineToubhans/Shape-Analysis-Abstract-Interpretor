open Offset
open Utils
open Domain_sig

let cd_error(s: string) = failwith (Printf.sprintf "CONCRETE_DOMAIN_ERROR: %s" s)

module ConcreteDomain = 
    (struct

       let domainId = 0      
	   
       (* contains only the destination node *) 
       type gen_edge = offseted_node 
	     	 
       type t = gen_edge generic_graph

       let empty = 
          { g_nodes = IntMap.empty;
	    g_next_node = 0;}
      
       let insertEdge(t: t) (e: gen_edge full_edge) =
	 let (i, o), on = e in
	 (* i --@o----------@o2----> j *)
	 let n = 
	   try IntMap.find i t.g_nodes with
	     | Not_found -> cd_error (Printf.sprintf "edge inserting failure: node %i doesn't exist" i) in
	 let n = 
	   if (OffsetMap.mem o n.n_edges) then
	     cd_error (Printf.sprintf 
			 "edge inserting failure: edge from node %i offset %s already exists" 
			 i
			 (offset2str o)) 
	   else
	     {n with n_edges = OffsetMap.add o on n.n_edges} in
	   {t with g_nodes = IntMap.add i n t.g_nodes}	  
	 
       let createFreshNode(t: t) = 
	 let m = t.g_next_node in
	 let n: gen_edge generic_node = 
	   {n_id =m;
	    n_edges = OffsetMap.empty;} in
	   {g_nodes = IntMap.add m n t.g_nodes;
	    g_next_node = m+1;}, m


       let removeNode(t: t) (n: int) =
	 {t with g_nodes = IntMap.remove n t.g_nodes}

     
       let getEdgesFromNode(t: t) ((i, o): offseted_node) =
	 try
	   let n = IntMap.find i t.g_nodes in	    
	     OffsetMap.fold (fun o2 a l -> if (inclOffset o o2) then ((i,o2),a)::l else l) n.n_edges []
	 with
	   | Not_found -> []

	       
       let removeEdgesFromNode(t: t) ((i, o): offseted_node) =
	 try
	   let n = IntMap.find i t.g_nodes in
	   let ofm = OffsetMap.filter (fun o2 _-> not (inclOffset o o2)) n.n_edges in
	   let n = {n with n_edges = ofm} in
	     {t with g_nodes = IntMap.add i n t.g_nodes}
	 with
	   | Not_found -> t

       let deffer(t: t) ((i, o): offseted_node) = 
	 let n = 
	   try IntMap.find i t.g_nodes
	   with
	     | Not_found -> cd_error (Printf.sprintf "defferentiation failure: node %i doesn't exist" i)
	 in
	   try OffsetMap.find o n.n_edges
	   with
	     | Not_found -> cd_error 
		 (Printf.sprintf "defferentiation failure: node %i offset %s can't be deferentied" i (offset2str o))

       let mutation
           (t: t)
           ((i, o): offseted_node) 
           ((j, f): offseted_node) = 
         let listEdges = getEdgesFromNode t (j, f) in
         let l = List.map (fun ((_, o1), on) -> (i, replaceOffset o1 f o), on) listEdges in 
         let t = removeEdgesFromNode t (i, o) in
           List.fold_left insertEdge t l
         

       let pp_edge ((i, o), (j, f): gen_edge full_edge) = 
	 Printf.sprintf "Node(%i)%s ---> Node(%i)%s" i (offset2str o) j (offset2str f)
	   
       let pp_node (n: gen_edge generic_node) = 
	 OffsetMap.fold 
	   (fun k a s -> Printf.sprintf "%s%s\n" s (pp_edge ((n.n_id, k), a)))
	   n.n_edges
	   (Printf.sprintf "Node(%i)\n======\n" n.n_id)

       let pp (t: t) = 
	 IntMap.fold 
	   (fun i n s -> Printf.sprintf "%s%s" s (pp_node n))
	   t.g_nodes
	   ""

     end: DOMAIN) 

module C = ConcreteDomain




