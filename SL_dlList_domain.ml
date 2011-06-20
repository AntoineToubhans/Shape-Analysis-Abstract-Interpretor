open Offset
open Utils
open Domain_sig

(* ============================================================= *)
(* Module SL with dlList (Doubly Linked List)                    *)
(* a.dll(e) := {a = 0  | emp}                                    *)
(*          := {a!= 0  | a@n|->b * a@p|->e * a@t|->c * b.dll(a)  *)
(* ============================================================= *)
(* Last modified: AT 06/06/11                                    *)


let sld_error(s: string) = failwith (Printf.sprintf "SL_DOMAIN_ERROR: %s" s)

module SL_TL_Domain =
  (struct

    let debug = true

     exception Fusion_error
     exception Unfolding_error of string
     exception Folding_error of string
    
     let domainId = 5

     type inductive = 
       | Emp
       | Ind_DLL of int (* Ind_DLL d means i.dll(d) *)
       | Seq_DLL of int*int  (* Seq_DLL(d, j) means i.dll(d) *-- j.dll(d) *)

     type node =
	 { id          : int;
	   simple_edges: int OffsetMap.t;
	   induct_edge : inductive;}
	
     type t =  
	 { nodes  : node IntMap.t;
	   next   : int;} (* next fresh node *)

     let empty: t =
       { nodes= IntMap.empty;
	 next= 0;}

     let hasInduct: t -> int -> bool = fun t i ->
       try 
	 match (IntMap.find i t.nodes).induct_edge with
	   | Emp -> false
	   | _ -> true
       with  _ -> false

     (* is o equals to "n" or "p" or "t"? *)
     let isIndOffset: offset -> bool = fun o -> 
       Offset.equals o (RecordField("t", Zero)) ||
       Offset.equals o (RecordField("p", Zero)) || 
       Offset.equals o (RecordField("n", Zero)) 

     (* add_edge t i o j  adds i@o|--->j to t*)
     let add_edge: t -> int -> offset -> int -> t = fun t i o j -> 
       if debug then Printf.printf "SL_TL_Domain:add_edge t %i %s %i\n" i (offset2str o) j;
       try 
	 let n = IntMap.find i t.nodes in 
	   if OffsetMap.mem o n.simple_edges 
	   then sld_error 
	     (Printf.sprintf "Separation issue: %i%s already set" i (offset2str o));
	   if hasInduct t i && isIndOffset o
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
       if debug then Printf.printf "SL_TL_Domain:add_ind t %i %i\n" i d;
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
	   if hasInduct t i 
	   then sld_error 
	     (Printf.sprintf "Separation issue: an inductive is already set on node(%i)" i);
	   let n = 
	     {n with induct_edge = Ind_DLL d} in
	     {t with nodes = IntMap.add i n t.nodes}
       with 
	 | Not_found ->
	     let n = 
	       { id = i;
		 simple_edges = OffsetMap.empty;
		 induct_edge = Ind_DLL d;} in
	       { nodes = IntMap.add i n t.nodes;
		 next = max t.next (i+1);}

     (* add_seq t i d j adds i.tl(d) *-- j.tl(d)  to t*)
     let add_seq: t -> int -> int -> int -> t = fun t i d j ->
       if debug then Printf.printf "SL_TL_Domain:add_seq t %i %i %i\n" i d j;
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
	   if hasInduct t i 
	   then sld_error 
	     (Printf.sprintf "Separation issue: an inductive is already set on node(%i)" i);
	   let n = 
	     {n with induct_edge = Seq_DLL(d, j)} in
	     {nodes = IntMap.add i n t.nodes;
	      next = max t.next (j+1);}	     
       with  
	 | Not_found ->
	     let n = 
	       { id = i;
		 simple_edges = OffsetMap.empty;
		 induct_edge = Seq_DLL(d, j);} in
	       { nodes = IntMap.add i n t.nodes;
		 next = max t.next ((max i j)+1);}
 
     (* fusion i j deletes i *)
     let fusion_node: t -> int -> int -> t = fun t i j -> 
       if debug then Printf.printf "SL_TL_Domain:fusion_node t %i %i\n" i j;
       let change_index = fun k-> if i==k then j else k in
       let change_inductive = fun ind -> 
	 match ind with
	   | Emp -> Emp
	   | Ind_DLL k -> Ind_DLL (change_index k)
	   | Seq_DLL(d, k) -> Seq_DLL((change_index d), (change_index k)) in
       let renaming_f = fun no -> 
	 { id = no.id;
	   simple_edges = OffsetMap.map change_index no.simple_edges;
	   induct_edge = change_inductive no.induct_edge;} in
       let merging_simple_edge = fun o (oi: int option) (oj: int option) ->
	 match oi, oj with
	   | Some i, Some j -> 
	       raise Fusion_error (*this shouldn'd happen*)
	   | Some i, _ -> oi
	   | _, _ -> oj in
       let merging_induct_edge = fun aa bb -> 
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

     let unfold: t -> int -> t list = fun t i -> 
       if debug then Printf.printf "SL_TL_Domain:unfold t %i\n" i;
       try 
	 let n = IntMap.find i t.nodes in
	   match n.induct_edge with
	     | Ind_DLL j ->
		 if OffsetMap.mem (RecordField("t", Zero)) n.simple_edges 
		   || OffsetMap.mem (RecordField("n", Zero)) n.simple_edges 
		   || OffsetMap.mem (RecordField("p", Zero)) n.simple_edges 
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
		     induct_edge= Emp;} in
		 (* new node pointed by i@n *)
		 let nn = 
		   { id = t.next;
		     simple_edges=OffsetMap.empty;
		     induct_edge=Ind_DLL j;} in		 
		   [{t with nodes=IntMap.add i {n with induct_edge=Emp} t.nodes};
		    { nodes=IntMap.add t.next nn (IntMap.add i m t.nodes);
		     next= t.next+2;}]
	     | Seq_DLL(j, k) ->
		 if OffsetMap.mem (RecordField("t", Zero)) n.simple_edges 
		   || OffsetMap.mem (RecordField("n", Zero)) n.simple_edges 
		   || OffsetMap.mem (RecordField("p", Zero)) n.simple_edges 
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
		     induct_edge=Seq_DLL(j, k);} in	
		 let t2 = 
		   { nodes=IntMap.add t.next nn (IntMap.add i m t.nodes);
		     next= t.next+2;} in
		   begin
		     try
		       if debug then Printf.printf "SL_TL_Domain:Unfold produces 2 graphs\n";
		       [fusion_node {t with nodes=IntMap.add i {n with induct_edge=Emp} t.nodes} i k; t2] 
		     with
		       | Fusion_error -> 
			   if debug then Printf.printf "SL_TL_Domain:Unfold only produces one graph\n";
			   [t2] (* shall I catch this exception ? *)
		   end			 
	     | Emp -> 
		 raise (Unfolding_error (Printf.sprintf "no inductives from node(%i)" i)) 
       with 
	 | Not_found -> 
	     raise (Unfolding_error (Printf.sprintf "node(%i) doesn't exist" i))


     (* dir_bckw_unfold t i unfold i.tl(d) *-- j.tl(d) onto i.tl(d) *-- k.tl(d) * k@n|-> j *)
     let dir_bckw_unfold: t -> int -> t list = fun t i ->
      if debug then Printf.printf "SL_TL_Domain:dir_bckw_unfold t %i\n" i;
      try 
	 let n = IntMap.find i t.nodes in
	   match n.induct_edge with	     
	     | Seq_DLL(d, j) ->
		 if OffsetMap.mem (RecordField("t", Zero)) n.simple_edges 
		   || OffsetMap.mem (RecordField("n", Zero)) n.simple_edges 
		   || OffsetMap.mem (RecordField("p", Zero)) n.simple_edges 
		 then sld_error "Separation issue"; (* this shouldn't happen! *)
		 (* new node i *)
		 let m =    
		   { n with induct_edge = Seq_DLL(d, t.next)} in
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
       if debug then Printf.printf "SL_TL_Domain:backward_unfold t %i\n" i;
       (* first we'll try to find all nodes j s.t. j.tl(d) *-- i.tl(d) *)
       let ffilter: int-> node-> bool = fun j n -> 
	 match n.induct_edge with |Seq_DLL(d, k) -> k==i |_ -> false in
       let map = IntMap.filter ffilter t.nodes in
       let ffold: int-> node-> t list-> t list = fun i n l -> 
         List.append (dir_bckw_unfold t i) l
       in
	 IntMap.fold ffold map []	 
   	 

     let fold: t -> int -> t = fun t i -> 
       if debug then Printf.printf "SL_TL_Domain:fold t %i\n" i;
       try 
	 let n = IntMap.find i t.nodes in
	   if n.induct_edge != Emp 
	   then 
	     raise (Folding_error (Printf.sprintf "node(%i) already has an inductive" i));
	   if not (OffsetMap.mem (RecordField("n", Zero)) n.simple_edges)
	   then 
	     raise (Folding_error(Printf.sprintf "%i%s isn't set" i (offset2str (RecordField("n", Zero)))));
	   if not (OffsetMap.mem (RecordField("p", Zero)) n.simple_edges)
	   then 
	     raise (Folding_error(Printf.sprintf "%i%s isn't set" i (offset2str (RecordField("p", Zero)))));
	   if not (OffsetMap.mem (RecordField("t", Zero)) n.simple_edges)
	   then 
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
		 Seq_DLL(
		   OffsetMap.find (RecordField("t", Zero)) n.simple_edges, 
		   OffsetMap.find (RecordField("n", Zero)) n.simple_edges);} in
	     {t with nodes=IntMap.add i new_n t.nodes}
       with 
	 | Not_found -> 
	     raise (Folding_error (Printf.sprintf "node(%i) doesn't exist" i))         

     (* add rules *)
     (* -- int list of program variable pointed nodes *)
     (* -- a.tl(d) *-- b.tl(d) && null(n) ---rw---> a.tl(d) *)
     let canonicalize: t -> t = fun t -> 
       t
	 
     let deffer: t -> offseted_node -> offseted_node = fun t (i, o) ->
       (i, o)
	 
     let mutation: t -> offseted_node -> offseted_node -> t = fun t (i, o1) (j, o2) ->
       t
	 
	 
     let pp_node: node -> string = fun n ->
       let s = Printf.sprintf "Node(%i):\n========\n" n.id in
       let f = fun o j s -> Printf.sprintf "%s %i%s|---> %i\n" s n.id (offset2str o) j in
       let s = OffsetMap.fold f n.simple_edges s in 
	 match n.induct_edge with
	   | Emp -> s
	   | Ind_DLL j -> Printf.sprintf "%s %i.tl(%i)\n" s n.id j
	   | Seq_DLL(j, k) -> Printf.sprintf "%s %i.tl(%i) *-- %i.tl(%i)\n" s n.id j k j
	      
     let pp: t -> string = fun t ->
       let s = Printf.sprintf "---Print SL_tList symbolic heap---\nNext free node:%i\n" t.next in
	 IntMap.fold (fun i n s -> Printf.sprintf "%s%s" s (pp_node n)) t.nodes s

   end)


(* ============================================== *)
module A = SL_TL_Domain

let e = A.add_seq A.empty 2 0 1
let e = A.add_seq e 3 2 1
let e = A.add_seq e 4 3 1
 
let e = A.add_edge e 2 (RecordField("c", Zero)) 3
let e = A.add_edge e 3 (RecordField("c", Zero)) 4
 
let f = A.unfold e 2
let g = A.unfold (List.hd f) 3

let _ = 
  Printf.printf "%s\n" (A.pp e);
  List.iter (fun e -> Printf.printf "%s\n" (A.pp e)) f;
  List.iter (fun e -> Printf.printf "%s\n" (A.pp e)) g;
