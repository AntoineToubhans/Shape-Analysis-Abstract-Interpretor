open Offset
open Utils
open Domain_sig

(* =========================================================== *)
(* Module SL_GRAPH_ Domain                                     *)
(* =========================================================== *)
(*                                  Last modified: AT 06/20/11 *)

let error s =  failwith (Printf.sprintf "SL_GRAPH_DOMAIN_ERROR: %s" s)


module SL_GRAPH_DOMAIN = 
  (struct
     
     type node =
	 { edges: int OffsetMap.t;
	   inductive : inductive option;}

     type t =    
	 { nodes  : node IntMap.t;
	   next   : int;} (* next fresh node *)

     let empty:t = 
       { nodes = IntMap.empty;
	 next = 1;}

     let is_node_empty: int -> t -> bool = fun i t ->
       try
	 let n = IntMap.find i t.nodes in
	   n.inductive==None && OffsetMap.is_empty n.edges
       with
	 | Not_found -> true

     let add_edge: int -> offset -> int -> t -> t = fun i o j t ->   
       if debug then print_debug "SL_GRAPH_DOMAIN:add_edge %i %s %i t\n" i (pp_offset o) j;
       try
	 let n = IntMap.find i t.nodes in 
	   if OffsetMap.mem o n.edges then error 
	     (Printf.sprintf "Separation issue: %i%s already set" i (pp_offset o));
	   { nodes = IntMap.add i {n with edges = OffsetMap.add o j n.edges} t.nodes;
	     next = max t.next (j+1)}
       with
	 | Not_found ->
	     { nodes = IntMap.add i {edges = OffsetMap.singleton o j; inductive = None;} t.nodes;
	       next = max t.next ((max i j)+1);}


     let remove_edge: int -> offset -> t -> t = fun i o t ->
       if debug then print_debug "SL_GRAPH_DOMAIN:remove_edge %i %s t\n" i (pp_offset o);
       try
	 let n = IntMap.find i t.nodes in
	   if not (OffsetMap.mem o n.edges) then raise Not_found;
	   { t with nodes = IntMap.add i {n with edges= OffsetMap.remove o n.edges} t.nodes}
       with
	 | Not_found ->
	     error 
	       (Printf.sprintf "Separation issue: %i%s isn't set, can't be removed" i (pp_offset o))
	     
	       
     let update_edge: int -> offset -> int -> t -> t = fun i o j t ->
       if debug then print_debug "SL_GRAPH_DOMAIN:update_edge %i %s %i t\n" i (pp_offset o) j;
       add_edge i o j (remove_edge i o t)

     let add_inductive: int -> inductive -> t -> t = fun i ind t ->
       if debug then print_debug "SL_GRAPH_DOMAIN:add_inductive %i ind t\n" i;
       try
	 let n = IntMap.find i t.nodes in
	   if has (n.inductive) then error 
	     (Printf.sprintf "Separation issue: %i already has an inductive" i);
	   { nodes = IntMap.add i {n with inductive = Some ind } t.nodes;
	     next = max t.next (maxlist (get_domain_inductive ind) + 1)}
       with
	 | Not_found ->
	     { nodes = IntMap.add i {edges = OffsetMap.empty; inductive = Some ind;} t.nodes;
	       next = max t.next (maxlist (i::get_domain_inductive ind) + 1);} 

     let remove_inductive: int -> t -> t = fun i t ->
       if debug then print_debug "SL_GRAPH_DOMAIN:remove_inductive %i t\n" i;
       try
	 let n = IntMap.find i t.nodes in
	   if hasnot (n.inductive) then raise Not_found;
	   { t with nodes = IntMap.add i {n with inductive=None} t.nodes}
       with
	 | Not_found ->
	     error 
	       (Printf.sprintf "Separation issue: %i has no inductive, can't be removed" i)
	       
    let update_inductive: int -> inductive -> t -> t = fun i ind t ->
      if debug then print_debug "SL_GRAPH_DOMAIN:update_inductive %i ind t\n" i;
      add_inductive i ind (remove_inductive i t)


    let create_fresh_node: t -> int* t = fun t ->
      if debug then print_debug "SL_GRAPH_DOMAIN: create fresh node...[%i]\n" t.next;
      t.next, {t with next = t.next + 1}

    let create_n_fresh_nodes: int -> t -> int list* t = fun n t ->
      if debug then print_debug "SL_GRAPH_DOMAIN: create %i fresh nodes...[%i,...,%i]\n" n t.next (t.next+n-1);
      let l = ref [] in 
	for i=t.next to t.next+n-1 do l:=i::(!l) done;
	!l, {t with next = t.next + n}

    let get_edge: int -> offset -> t -> int option = fun i o t ->
      try 
	let j = OffsetMap.find o (IntMap.find i t.nodes).edges in
	  if debug then print_debug "SL_GRAPH_DOMAIN:get_edge %i %s t.....%i\n" i (pp_offset o) j;
	  Some j
      with
	| Not_found -> 
	    if debug then print_debug "SL_GRAPH_DOMAIN:get_edge %i %s t.....None\n" i (pp_offset o);
	    None
	      
    let get_inductive: int -> t -> inductive option = fun i t ->
      try
	let ind = get (IntMap.find i t.nodes).inductive in
	  if debug then print_debug "SL_GRAPH_DOMAIN:get_inductive %i t.....%i.%s\n" i i (pp_inductive ind);
	  Some ind
      with 
	| Not_found | No_value ->
	    if debug then print_debug "SL_GRAPH_DOMAIN:get_inductive %i t.....None\n" i;
	    None

    let has_edge: int -> offset -> t -> bool = fun i o t ->
      let b = 
	try OffsetMap.mem o (IntMap.find i t.nodes).edges 
	with | Not_found -> false in
	if debug && b then print_debug "SL_GRAPH_DOMAIN:has_edge %i %s t.....Yes\n" i (pp_offset o);
	if debug && not b then print_debug "SL_GRAPH_DOMAIN:has_edge %i %s t.....No\n" i (pp_offset o);
	b

    let has_inductive: int -> t -> bool = fun i t ->
      let b = try has (IntMap.find i t.nodes).inductive with | Not_found -> false in
	if debug && b then print_debug "SL_GRAPH_DOMAIN:has_inductive %i t.....Yes\n" i;
	if debug && not b then print_debug "SL_GRAPH_DOMAIN:has_inductive %i t.....No\n" i;
	b
	      
    let find: int -> offset -> t -> (offset * int) list = fun i o t ->
      if debug then print_debug "SL_GRAPH_DOMAIN: finding edges from Node(%i)%s...\n" i (pp_offset o);
      try 
	let n = IntMap.find i t.nodes 
	and ffold: offset -> int -> (offset * int) list -> (offset * int) list = fun oo j l ->
	  try ((replaceOffset oo o Zero), j)::l with | Offset_error _ -> l in  
	  OffsetMap.fold ffold n.edges []
      with 
	 | Not_found -> []

    (* fusion i j deletes i *)
    let fusion: int -> int -> t -> t = fun i j t ->
      if debug then print_debug "SL_TL_GRAPH_DOMAIN:fusion_node %i %i t\n" i j;
      let change_index = fun k-> if i==k then j else k in
      let change_inductive = function | None -> None | Some ind ->
	Some
	  { target = change_index ind.target;
	    source_parameters = List.map change_index ind.source_parameters;
	    target_parameters = List.map change_index ind.target_parameters;
	    length = ind.length;} in
      let change_node = fun n -> 
	{ edges = OffsetMap.map change_index n.edges;
	  inductive = change_inductive n.inductive;} 
      and merging: int option -> int option -> int option = 
	function | None -> (fun x -> x) | x -> (function | None -> x | _ -> raise Bottom) 
      (* I had to duplicate merging 'a option -> 'a option -> 'a option, doesn't work otherwise... *)
      and merging0: inductive option -> inductive option -> inductive option = 
 	function | None -> (fun x -> x) | x -> (function | None -> x | _ -> raise Bottom) in
      let merge_node: node -> node -> node = fun n m ->
	{edges = OffsetMap.merge (fun o -> merging) n.edges m.edges;
	 inductive = merging0 n.inductive m.inductive;} in
      let n = 
	try Some (IntMap.find i t.nodes)
	with Not_found -> None in
      let m = 
	try Some (IntMap.find j t.nodes)
	with Not_found -> None in
	match n, m with
	  | Some n, Some m ->	       
	      {nodes = IntMap.map change_node (IntMap.add j (merge_node n m) (IntMap.remove i t.nodes));
	       next  = if t.next==i+1 then i else t.next;}
	   | Some n, None ->
	       {nodes = IntMap.map change_node (IntMap.add j n (IntMap.remove i t.nodes));
		next  = if t.next==i+1 then i else t.next;}
	   | None, _ ->
	       {nodes = IntMap.map change_node t.nodes;
		next  = if t.next==i+1 then i else t.next;}

    (* computes all j such that: *)
    (*  -  j@o |--> i            *)
    (*  -  p j o                 *)
    let is_reached_by_edge: int -> (int -> offset -> bool) -> t -> int list = fun i p t ->
      if debug then print_debug "SL_GRAPH_DOMAIN: is_reached_by_edge %i p t\n" i;
      IntMap.fold
 	(fun j n l -> OffsetMap.fold (fun o k l -> if k==i && p j o then j::l else l) n.edges l)
	t.nodes
	[]

    (* computes all j such that: *)
    (*  -  j.c(a) *== i.c(b)     *)
    (*  -  p j a b               *)
    let is_reached_by_inductive: int -> (int -> inductive -> bool) -> t -> int list = fun i p t -> 
      if debug then print_debug "SL_GRAPH_DOMAIN: is_reached_by_inductive %i p t\n" i;
      IntMap.fold
	(fun j n l -> map_default (fun ind -> if p j ind && ind.target==i then j::l else l) l n.inductive)
	t.nodes
	[]

    let is_reached: int -> (int -> bool) -> t -> int list = fun i p t ->
      if debug then print_debug "SL_GRAPH_DOMAIN: is_reached %i p t\n" i;
      List.append (is_reached_by_edge i (fun i _ -> p i) t) (is_reached_by_inductive i (fun i _ -> p i) t)	


    (* may contains duplicates *)
    let domain: t -> IntSet.t = fun t ->
      let add j dom = 
	if j>=t.next then error 
	  (Printf.sprintf "Domain issue: contains %i which's bigger then t.next: %i" j t.next);
	IntSet.add j dom in
      let fffold i n dom =
	let dom = add i (OffsetMap.fold (fun o -> add) n.edges dom) in
	  map_default 
	    (fun ind->
	       List.fold_left (fun dom i -> add i dom)
		 (List.fold_left (fun dom i -> add i dom) (IntSet.add ind.target dom) ind.source_parameters)
		 ind.target_parameters) 
	    dom n.inductive
      in
	IntMap.fold fffold t.nodes IntSet.empty
	  
     let pp_node: int -> node -> string = fun i n ->
       let s = Printf.sprintf "Node(%i):\n========\n" i in
       let f = fun o j s -> Printf.sprintf "%s %i%s|---> %i\n" s i (pp_offset o) j in
       let s = OffsetMap.fold f n.edges s in 
	 map_default
	   (fun ind -> Printf.sprintf "%s %i.%s\n" s i (pp_inductive ind)) s n.inductive
	      
     let pp: t -> string = fun t ->
       let s = Printf.sprintf "     ---Print SL_GRAPH_DOMAIN---\nNext free node:%i\n" t.next in
	 IntMap.fold (fun i n s -> Printf.sprintf "%s%s" s (pp_node i n)) t.nodes s

   end: SL_GRAPH_DOMAIN)
