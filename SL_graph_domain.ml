open Offset
open Utils
open Domain_sig

(* =========================================================== *)
(* Module SL_GRAPH_ Domain                                     *)
(* =========================================================== *)
(*                                  Last modified: AT 06/20/11 *)

let error s =  failwith (Printf.sprintf "SL_GRAPH_DOMAIN_ERROR: %s" s)


module SL_GRAPH_DOMAIN = functor (O: OPTION) ->
  (struct
     
     let debug = O.debug

     let print_debug x = 
       Utils.print_debug ("SL_GRAPH_DOMAIN:\t" ^^ x) 

     type node =
	 { edges: int OffsetMap.t;
	   inductive : Inductive.t option;}

     type t =    
	 { nodes  : node IntMap.t;
	   next   : int;} (* next fresh node *)

     let empty:t = 
       { nodes = IntMap.empty;
	 next = 1;}

     let next: t -> int = fun t -> t.next

     let is_node_empty: int -> t -> bool = fun i t ->
       try
	 let n = IntMap.find i t.nodes in
	   n.inductive==None && OffsetMap.is_empty n.edges
       with
	 | Not_found -> true

     (* =============================================== *)
     (* graph tools                                     *)
     (* =============================================== *)

     let fold_from_node: (int -> 'a -> 'a) -> node -> 'a -> 'a = fun f n a ->
       let a = OffsetMap.fold (fun _ -> f) n.edges a in
	 match n.inductive with
	   | None -> a
	   | Some ind ->
	       let a = f ind.Inductive.target a in
	       let a = 
		 List.fold_left 
		   (fun a i -> f i a) a ind.Inductive.source_parameters in
		 List.fold_left 
		   (fun a i -> f i a) a ind.Inductive.target_parameters 

     (* bad function: TO BE FIXED *)
     let compute_connex: t -> node IntMap.t list = fun t ->
       if debug then print_debug "compute connex comps\n";
       let get_n i (nodes, queue) = 
	 try
	   let n = IntMap.find i nodes in
	     if n.inductive = None && OffsetMap.is_empty n.edges then
	       (IntMap.remove i nodes), queue
	     else
	       (IntMap.remove i nodes), ((i, n)::queue)
	 with
	   | Not_found ->
	       nodes, queue in 
       let rec compute_one nodes comp queue = 
	 match queue with
	   | [] -> nodes, comp
	   | (i, n)::queue ->
	       let nodes, queue = 
		 OffsetMap.fold 
		   (fun _ -> get_n) n.edges (nodes, queue) in
	       let nodes, queue = 
		 if has (n.inductive) then
		   let ind = get (n.inductive) in
		     List.fold_left
		       (fun cp i -> get_n i cp) (nodes, queue) 
		       (Inductive.get_domain ind)
		 else
		   nodes, queue in
		 compute_one nodes (IntMap.add i n comp) queue in
       let rec compute_all nodes lcomp = 
	 if IntMap.is_empty nodes then
	   lcomp
	 else
	   let i, n = IntMap.choose nodes in
	   let nodes = IntMap.remove i nodes in
	   let nodes, comp = compute_one nodes (IntMap.empty) [i, n] in
	     compute_all nodes (comp::lcomp) in
	 compute_all t.nodes []

     (* get entry points                   *)
     (* very naive, can't deal with cycles *)
     let get_entry_points: t -> IntSet.t = fun t ->
       let rec r_gep nodes ep rp = 
	 if IntMap.is_empty nodes then ep else
	   let i, n = IntMap.choose nodes in
	   let ep = if IntSet.mem i rp then ep else IntSet.add i ep in
	   let ep, rp = 
	     fold_from_node
	       (fun i (ep, rp) -> IntSet.remove i ep, IntSet.add i rp) 
	       n (ep, rp) in
	     r_gep (IntMap.remove i nodes) ep rp in
	 r_gep t.nodes IntSet.empty IntSet.empty	     
  
     (* =============================================== *)

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

     let add_inductive: int -> Inductive.t -> t -> t = fun i ind t ->
       if debug then print_debug "SL_GRAPH_DOMAIN:add_inductive %i ind t\n" i;
       try
	 let n = IntMap.find i t.nodes in
	   if has (n.inductive) then error 
	     (Printf.sprintf "Separation issue: %i already has an inductive" i);
	   { nodes = IntMap.add i {n with inductive = Some ind } t.nodes;
	     next = max t.next (maxlist (Inductive.get_domain ind) + 1)}
       with
	 | Not_found ->
	     { nodes = IntMap.add i {edges = OffsetMap.empty; inductive = Some ind;} t.nodes;
	       next = max t.next (maxlist (i::Inductive.get_domain ind) + 1);} 

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
	       
    let update_inductive: int -> Inductive.t -> t -> t = fun i ind t ->
      if debug then print_debug "SL_GRAPH_DOMAIN:update_inductive %i ind t\n" i;
      add_inductive i ind (remove_inductive i t)


    let create_fresh_node: t -> int* t = fun t ->
      if debug then print_debug "create fresh node...[%i]\n" t.next;
      t.next, {t with next = t.next + 1}

    let create_fresh_node_index: int -> t -> t = fun i t ->
      if i<t.next then 
	error (Printf.sprintf "can't create node at %i, not available..." i);
      if debug then print_debug "create fresh node (index)...[%i]\n" i;
      {t with next = i+1}

    let create_n_fresh_nodes: int -> t -> int list* t = fun n t ->
      if debug then print_debug "create %i fresh nodes...[%i,...,%i]\n" n t.next (t.next+n-1);
      let l = ref [] in 
	for i=t.next to t.next+n-1 do l:=i::(!l) done;
	!l, {t with next = t.next + n}

    let get_edge: int -> offset -> t -> int option = fun i o t ->
      try 
	let j = OffsetMap.find o (IntMap.find i t.nodes).edges in
	  if debug then print_debug "SL_GRAPH_DOMAIN:get_edge %i %s t.....[%i]\n" i (pp_offset o) j;
	  Some j
      with
	| Not_found -> 
	    if debug then print_debug "SL_GRAPH_DOMAIN:get_edge %i %s t.....None\n" i (pp_offset o);
	    None
	      
    let get_inductive: int -> t -> Inductive.t option = fun i t ->
      try
	let ind = get (IntMap.find i t.nodes).inductive in
	  if debug then print_debug "SL_GRAPH_DOMAIN:get_inductive %i t.....[%i.%s]\n" i i (Inductive.pp ind);
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

    let has_edges: int -> t -> bool = fun i t ->
      let b = 
	try not (OffsetMap.is_empty (IntMap.find i t.nodes).edges) 
	with | Not_found -> false in
	if debug && b then print_debug "SL_GRAPH_DOMAIN:has_edges %i t.....Yes\n" i;
	if debug && not b then print_debug "SL_GRAPH_DOMAIN:has_edges %i t.....No\n" i;
	b

    let has_inductive: int -> t -> bool = fun i t ->
      let b = try has (IntMap.find i t.nodes).inductive with | Not_found -> false in
	if debug && b then print_debug "SL_GRAPH_DOMAIN:has_inductive %i t.....Yes\n" i;
	if debug && not b then print_debug "SL_GRAPH_DOMAIN:has_inductive %i t.....No\n" i;
	b


    let for_all_edges: (offset -> int -> bool) -> int -> t -> bool = fun p i t ->
      try 
	OffsetMap.for_all p (IntMap.find i t.nodes).edges
      with
	| Not_found -> true

    let exists_edge: (offset -> int -> bool) -> int -> t -> bool = fun p i t ->
      try 
	OffsetMap.exists p (IntMap.find i t.nodes).edges
      with
	| Not_found -> false
	      
    let for_all: (int -> bool) -> t -> bool = fun p t ->
      IntMap.for_all (fun i n -> p i) t.nodes

    let exists: (int -> bool) -> t -> bool = fun p t ->
      IntMap.exists (fun i n -> p i) t.nodes

    let str_get_nodes: (int -> node -> bool) -> t -> IntSet.t = fun p t ->
      if debug then print_debug "SL_TL_GRAPH_DOMAIN: str_get pred t\n";
      IntMap.fold
	(fun i n set -> if p i n then IntSet.add i set else set) t.nodes IntSet.empty

    let get_nodes: (int -> bool) -> t -> IntSet.t = fun p t ->
      str_get_nodes (fun i n -> p i) t

    let fold: (int -> 'a -> 'a) -> t -> 'a -> 'a = fun f t a ->
      IntMap.fold (fun i _ a -> f i a) t.nodes a

    let find: int -> offset -> t -> (offset * int) list = fun i o t ->
      if debug then print_debug "finding edges from Node(%i)%s...\n" i (pp_offset o);
      try 
	let n = IntMap.find i t.nodes 
	and ffold: offset -> int -> (offset * int) list -> (offset * int) list = fun oo j l ->
	  try ((replaceOffset oo o Zero), j)::l with | Offset_error _ -> l in  
	  OffsetMap.fold ffold n.edges []
      with 
	 | Not_found -> []

    (* fusion i j deletes i *)
    let fusion: int -> int -> t -> t = fun i j t ->
      if debug then print_debug "SL_GRAPH_DOMAIN:fusion %i %i t\n" i j;
      let change_index = fun k-> if i==k then j else k in
      let change_inductive = Inductive.change_index change_index in
      let change_node = fun n -> 
	{ edges = OffsetMap.map change_index n.edges;
	  inductive = 
	    match n.inductive with
	      | Some ind -> Some (change_inductive ind)
	      | _ -> None;} 
      and merging: int option -> int option -> int option = 
	function | None -> (fun x -> x) | x -> (function | None -> x | _ -> raise Bottom) 
      (* I had to duplicate merging 'a option -> 'a option -> 'a option, doesn't work otherwise... *)
      and merging0: Inductive.t option -> Inductive.t option -> Inductive.t option = 
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

    (* is the node reached by some j such that: *)
    (*  -  j@o |--> i                           *)
    (*  -  pred j o                             *)
    let is_reached_by_edge: int -> (int -> offset -> bool) -> t -> bool = fun i p t ->
      if debug then print_debug "is_reached_by_edge %i p t\n" i;
      IntMap.exists
	(fun j n -> OffsetMap.exists (fun o k -> k==i && p j o) n.edges) t.nodes

    (* is the node reached by some j such that: *)
    (*  -  j.c(a) *== i.c(b)                    *)
    (*  -  pred j a b                           *)
    let is_reached_by_inductive: int -> (int -> Inductive.t -> bool) -> t -> bool = fun i p t -> 
      if debug then print_debug "is_reached_by_inductive %i p t\n" i;
      IntMap.exists
	(fun j n -> has n.inductive && (get n.inductive).Inductive.target==i && p j (get n.inductive))
	t.nodes

    let is_reached: int -> (int -> bool) -> t -> bool = fun i p t ->
      if debug then print_debug "is_reached %i p t\n" i;
      is_reached_by_edge i (fun i _ -> p i) t || is_reached_by_inductive i (fun i _ -> p i) t	


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
		 (List.fold_left (fun dom i -> add i dom) (IntSet.add ind.Inductive.target dom) ind.Inductive.source_parameters)
		 ind.Inductive.target_parameters) 
	    dom n.inductive
      in
	IntMap.fold fffold t.nodes IntSet.empty
	  
    let equals: int IntMap.t -> int IntMap.t -> t -> t -> (int IntMap.t * int IntMap.t) option =
      fun m1 m2 t1 t2 -> 
	if debug then print_debug "checking [equals]\n";
	let acc = ref (IntMap.bindings m1) 
	and m1 = ref m1 and m2 = ref m2 in
	let add i j = 
	  try 
	    if IntMap.find i !m1 != j then 
	      raise (Nope (Printf.sprintf "multiple matching for node %i" i))
	  with
	    | Not_found -> 
		m1:= IntMap.add i j !m1; 
		m2:= IntMap.add j i !m2;
		acc:= (i, j)::!acc in
	let do_node n1 n2 = 
	  OffsetMap.iter 
	    (fun o i -> 
	       try add i (OffsetMap.find o n2.edges)
	       with | Not_found -> 
		 raise (Nope (Printf.sprintf "%s-->%i don't match" (pp_offset o) i)))
	    n1.edges;
	  OffsetMap.iter  
	    (fun o j -> 
	       try add (OffsetMap.find o n1.edges) j
	       with | Not_found -> 
		 raise (Nope (Printf.sprintf "%s-->%i don't match" (pp_offset o) j)))
	    n2.edges;
	  match n1.inductive, n2.inductive with
	    | None, None -> ()
	    | Some ind1, Some ind2 -> 
		if not 
		  (Inductive.equals_length 
		     ind1.Inductive.length ind2.Inductive.length) then 
		    raise (Nope "inductive length doesn't match");
		add ind1.Inductive.target ind2.Inductive.target;
		List.iter2 
		  add ind1.Inductive.source_parameters ind2.Inductive.source_parameters;
		List.iter2 
		  add ind1.Inductive.target_parameters ind2.Inductive.target_parameters
	    | _ -> 
		raise (Nope "inductive doesn't match") in
	let do_it i j = 
	  let ni =  
	    try Some(IntMap.find i t1.nodes)
	    with | Not_found -> None 
	  and nj = 
	    try Some (IntMap.find j t2.nodes)
	    with | Not_found -> None in
	    match ni, nj with
	      | None, None -> ()
	      | None, Some n | Some n, None ->
		  if n.inductive != None || not (OffsetMap.is_empty n.edges) then 
		    raise (Nope "nodes don't match")
	      | Some ni, Some nj -> 
		  do_node ni nj in
	  try
	    while !acc != [] do
	      let i, j = List.hd !acc in
		acc:= List.tl !acc;
		do_it i j;
	    done;
	    (* now we deal with untracked nodes *)
	    if debug then 
	      print_debug 
		"[equals] partial mapping found... resolving untracked nodes\n";
	    (* we get potential entry points of the graph *)
	    let u_ep1 = 
	      IntSet.filter 
		(fun i -> not (IntMap.mem i !m1)) (get_entry_points t1) 
	    and u_ep2 = 
	      IntSet.filter
		(fun i -> not (IntMap.mem i !m2)) (get_entry_points t2) in
	    if IntSet.cardinal u_ep1 != IntSet.cardinal u_ep2 then 
	      raise (Nope "entry points of untracked nodes doesn't match");
	      (* awfull dummy code... *)
	    let old_m1 = ref IntMap.empty and old_m2 = ref IntMap.empty in 
	    let ep1 = ref u_ep1 and ep2 = ref u_ep2 and ep22 = ref u_ep2 in
	      while not (IntSet.is_empty !ep1) do
		let i = IntSet.choose !ep1 and success = ref false in
		  ep22 := !ep2;
		  old_m1:= !m1;
		  old_m2:= !m2;
		  while not (IntSet.is_empty !ep22) && not !success do
		    let j = IntSet.choose !ep22 in
		      acc:= [i, j];
		      m1:= IntMap.add i j !old_m1;
		      m2:= IntMap.add j i !old_m2;
		      try 
			while !acc != [] do
			  let i, j = List.hd !acc in
			    acc:= List.tl !acc;
			    do_it i j;
			done;
			success:= true;
			ep1:= IntSet.remove i !ep1; 
			ep2:= IntSet.remove j !ep2;
		      with
			| Nope _ ->
			    ep22:= IntSet.remove j !ep22;
		  done;
	      done;
	    if debug then  
	      begin 
		print_debug "[equals] mapping found:\n";
		IntMap.iter 
		  (fun i j -> print_debug "[equals] t1.Node(%i) = t2.Node(%i)\n" i j)
		  !m1
	      end;
	    Some(!m1, !m2) 
	  with 
	    | Nope e -> 
		if debug then print_debug "[equals] no mapping found: %s\n" e;
		None

    (* deep search first *)
    let rec rec_find_path target t acc acc_r = 
      match acc with 
	| [] -> acc_r
	| (lo, i)::acc -> 
	    begin
	      let acc_r = if i=target then lo::acc_r else acc_r in
		try
		  let n = IntMap.find i t.nodes in 
		  let acc = 
		    OffsetMap.fold 
		      (fun o j acc -> 
			 if List.exists (fun (_, i) -> i=j) acc then			 
			   acc
			 else
			   (o::lo,j)::acc)
		      n.edges acc in
		    rec_find_path target t acc acc_r
		with
		  | Not_found -> rec_find_path target t acc acc_r
	    end

    let find_path: int -> int -> t -> Path.t list -> Path.t list = fun live i t l -> 
      if debug then print_debug "looking for path from %i to %i\n" live i;
      let l = rec_find_path i t [[], live] [] in
      let l = List.map (fun o -> live, List.rev o) l in
	if debug then print_debug "paths found: %s\n"
	  (List.fold_left (fun s p -> Printf.sprintf "%s, %s" s (Path.pp p)) "" l);
	l

    let pp_node: int -> node -> unit = fun i n ->
       O.XML.print_italic "Node(%i):<br/>" i;
       OffsetMap.iter
	 (fun o j ->  
	    O.XML.printf "%i%s|---> %i<br/>" i (pp_offset o) j)
	 n.edges; 
       match n.inductive with
	 | Some ind ->
	     O.XML.printf "%i.%s<br/>" i (Inductive.pp ind)
	 | _ -> ()
	      
     let pp: t -> unit = fun t ->
       O.XML.print_bold "GRAPH (Next free node:%i):<br/>" t.next;
       IntMap.iter pp_node t.nodes

     let clean_node: int -> t -> t = fun i t ->
       if debug then print_debug "Cleaning node %i\n" i;
       if is_node_empty i t then
	 { t with nodes = IntMap.remove i t.nodes }
       else
	 t

     let clean: t -> t = fun t ->
       if debug then print_debug "[Cleaning]\n";
       { t with nodes = 
	   IntMap.filter 
	     (fun _ n -> not (OffsetMap.is_empty n.edges) || n.inductive != None)
	     t.nodes }
	 
     let forget_inductive_length: t -> t = fun t ->
       if debug then print_debug "forget inductive length\n";
       let nodes = 
	 IntMap.map 
	   (fun n -> 
	      match n.inductive with
		| Some ind ->
		    { n with inductive = Some(Inductive.forget_length ind) }
		| _ -> n) 
	   t.nodes in
	 { t with nodes = nodes }


(* TESTS

     let g = empty 
       
     let g = add_edge 1 Zero 2 g
     let g = add_edge 3 Zero 2 g
     let g = add_edge 2 Zero 4 g
     let g = add_inductive 4 
       { Inductive.target = 5;
	 Inductive.source_parameters= [7];
	 Inductive.target_parameters = [0];
	 Inductive.length = Inductive.Unknown;} g
     let g = add_edge 5 (RecordField("plop", Zero)) 6 g
     let g = add_edge 7 (RecordField("junk", Zero)) 8 g
       
     let l_g = compute_connex g

     let s = get_entry_points g 
       
     let _ = 
       Printf.printf "%s\n" (pp g);
       let i = ref 0 in
	 List.iter
	   (fun g -> 
	      i:= !i + 1; 
	      Printf.printf "%i nth comp:\n%s\n" !i (pp {nodes = g; next=0;})) 
	   l_g;
	 IntSet.iter 
	   (fun i -> Printf.printf "%i\t" i) s
*)

   end: SL_GRAPH_DOMAIN)


