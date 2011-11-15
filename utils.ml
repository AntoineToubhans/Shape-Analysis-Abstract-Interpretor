module Int = 
  struct    
    type t = int
    let compare: t -> t -> int = fun x y -> x-y
  end

module IntMap = Map.Make(Int)
module IntSet = Set.Make(Int)

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

let debug_channel = open_out "debug.log"
let print_debug = fun x -> Printf.fprintf debug_channel x 
  
exception No_value
let get: 'a option -> 'a = function | Some x -> x | None -> raise No_value
let has: 'a option -> bool = function | Some _ -> true | None -> false
let hasnot: 'a option -> bool = function | Some _ -> false | None -> true
let map_default: ('a -> 'b) -> 'b -> 'a option -> 'b = fun f b -> 
  function | Some x -> f x | None -> b

exception Top
exception Bottom

exception Nope of string

let rec map3: ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list = fun f aa bb cc -> 
    match aa, bb, cc with
    | [], [], [] -> []
    | a::aa, b::bb, c::cc -> (f a b c)::(map3 f aa bb cc)
    | _ -> raise (Invalid_argument "Utils.map3")

(* tail recursive *)
let tail_map3: ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list = fun f aa bb cc -> 
  let rec aux acc f aa bb cc = 
    match aa, bb, cc with
    | [], [], [] -> acc
    | a::aa, b::bb, c::cc -> aux ((f a b c)::acc) f aa bb cc 
    | _ -> raise (Invalid_argument "Utils.tail_map3") in
    aux [] f aa bb cc

let maxlist l = 
  let rec ml l acc = 
    match l with | [] -> acc | a::l -> ml l (max a acc) in ml l 0

let pp_list l = 
  let rec pp_nl l s = match l with | []->s |i::l-> pp_nl l (Printf.sprintf "%s, %i" s i) in
    match l with |[]-> "" |a::l-> pp_nl l (Printf.sprintf "%i" a)


(* assume the list is sorted *)
let delete_duplicates: ('a -> 'a -> bool) -> 'a list -> 'a list = fun c l ->
  let rec aux: ('a->'a->bool)->'a list->'a list->'a list = fun c l cur -> 
    match l, cur with 
      | [], _ -> cur
      | x::l, [] -> aux c l [x]
      | x::l, y::ll -> aux c l (if c x y then cur else x::cur) in
  aux c l []

(*
let intlist2str: int list -> string = fun l ->
  match l with
    | [] -> "[]" 
    | x::l -> 
	"["^(List.fold_left (fun s a -> Printf.sprintf "%s, %i" s a) (Printf.sprintf "%i" x) l)^"]" *)

module BinaryTree = 
  struct
    type 'a t = Empty | Leaf of 'a | Node of 'a t * 'a t 
  
    let rec flatten: 'a t list -> 'a t list = fun l ->
      match l with
	| [] -> []
	| t::[] -> [t]
	| t1::t2::l -> (Node (t1, t2))::(flatten l)
	    
    let list: 'a list -> 'a t = fun l ->
      let rec f l = 
	match l with | [] -> Empty | t::[] -> t | _ -> f (flatten l) in
	f (List.map (fun a -> Leaf a) l)

    let rec pp_blank: int -> unit = fun i ->
      if i>0 then begin 
	Printf.printf "-"; 
	pp_blank (i-1)
      end

    let rec pp_r: int -> ('a -> string) -> 'a t -> unit = fun i p t ->
      pp_blank i;
      match t with
	| Empty -> Printf.printf "Empty\n" 
	| Leaf a -> Printf.printf "%s\n" (p a)
	| Node (a, b) -> 
	    Printf.printf "Prod:\n";
	    pp_r (i+1) p a;
	    pp_r (i+1) p b
    let pp: ('a -> string) -> 'a t -> unit = fun p t -> pp_r 0 p t
    
    (* basic tools *)
    let rec iter: ('a -> unit) -> 'a t -> unit = fun f t ->
      match t with
	| Empty -> ()
	| Leaf a -> f a
	| Node (t1, t2) -> iter f t1; iter f t2
    let rec map: ('a -> 'b) -> 'a t -> 'b t = fun f t ->
      match t with
	| Empty -> Empty
	| Leaf a -> Leaf (f a)
	| Node (t1, t2) -> Node (map f t1, map f t2)
    let rec fold: ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b = fun f t b ->
      match t with
	| Empty -> b
	| Leaf a -> f a b 
	| Node (t1, t2) -> fold f t2 (fold f t1 b)
  end

module Node_ID = 
  struct
    (* tree path *) 
    type t =
 	Id of int
      | Left of t
      | Right of t
      | P of t * t
	  (* All i means i every where in th product *)
      | All of int	 

    let rec pp: t -> string = function   
      | All x -> Printf.sprintf "Everywhere: %i" x
      | Id x -> Printf.sprintf "Id %i" x
      | Left t -> Printf.sprintf "Left (%s)" (pp t)
      | Right t -> Printf.sprintf "Right (%s)" (pp t)
      | P (t1, t2) -> Printf.sprintf "P (%s, %s)" (pp t1) (pp t2)

    let get: t -> int = function 
      | Id x | All x -> x
      | _ -> failwith "can't get the node ID"
	  
    let left: t -> t option = function
      | Left x | P (x, _) -> Some x
      | All x -> Some (All x)
      | _ -> None
    let right: t -> t option = function
      | Right x | P (_, x) -> Some x
      | All x -> Some (All x)
      | _ -> None

    let rec fusion: t -> t -> t -> t = fun i j k -> 
      match i, j, k with
	| Left i, Left j, Left k -> Left (fusion i j k)
	| Left i, Left j, P (k, r) -> P (fusion i j k, r)
	| Right i, Right j, Right k -> Right (fusion i j k)
	| Right i, Right j, P (l, k) -> P (l, fusion i j k)
	| Id i, Id j, Id k -> Id (if i=k then j else k)
	| _ -> k

    let rec is_complete: t -> bool = function
      | Id _ | All _ -> true
      | P (x, y) -> is_complete x && is_complete y
      | _ -> false

    let rec greatestId: t -> int = function
      | All x | Id x -> x
      | Left t | Right t -> greatestId t
      | P (t1, t2) -> Pervasives.max (greatestId t1) (greatestId t2)

    let rec max: t -> t -> t = fun i j ->
      match i, j with
	| All x, y | y, All x -> All (Pervasives.max x (greatestId y))
	| Id x, Id y -> Id (Pervasives.max x y)
	| P (il, ir), P (jl, jr) -> P (max il jl, max ir jr) 
	| _ -> failwith 
	    (Printf.sprintf "Node_ID.max: bad args [%s, %s]" (pp i) (pp j))

    (* i MUST be linear path *)
    let rec is_include: t -> t -> bool = fun i j ->
      match i, j with
	| All _, _ | P _, _ -> failwith "Node_ID.is_include: first arg must be linear"
	| Id x, Id y | Id x, All y -> x=y
	| Left x, Left y | Left x, P (y, _) 
	| Right x, Right y | Right x, P (_, y) -> is_include x y
	| Left x, All y | Right x, All y -> is_include x (All y)
	| _ -> false

    (*******************************************************)
    (*    /\        /\          /    /             /\      *)
    (*   /  \      /  \   -->  / =  /   , Some(   /  \   ) *)
    (*  /\  /     /\  /\      /\   /\            /\  /\    *)
    (* a  b c    a' b'c d    a  b a' b'         a b  c d   *)
    (*******************************************************)
    (*    /\        /\                             /\      *)
    (*   /  \      /  \   -->  None     , Some(   /  \   ) *)
    (*   \  /\    /\  /                          /\  /\    *)
    (*    b c d  a  b c                         a b  c d   *)
    (*******************************************************)
    (*    /\        /\                                     *)
    (*   /  \      /  \   --> None,  None                  *)
    (*  /\  /     /\  /\                                   *) 
    (* a  b c    a' b'c'd                                  *)
    (*******************************************************)
    let fusion_eq: t -> t -> (t*t) option * t option = fun i j ->
      let comb eq1 eq2 = 
	match eq1, eq2 with
	  | Some (eq1l, eq1r), Some (eq2l, eq2r) -> Some (P (eq1l, eq2l), P (eq1r, eq2r))
	  | Some (eql, eqr), None -> Some (Left eql, Left eqr)
	  | None, Some (eql, eqr) -> Some (Right eql, Right eqr)
	  | _ -> None in 
      let rec f i j = 
	match i, j with 
	  | Id x, Id y | Id x, All y | All x, Id y -> 
	      if x=y then Id x, None, true else Id x, Some(Id x, Id y), false
	  | All x, All y -> 
	      if x=y then All x, None, true else All x, Some(All x, All y), false
	  | _ ->
	      begin
		let oil = left i and oir = right i and ojl = left j and ojr = right j in
		let left = match oil, ojl with
		  | Some i, Some j -> Some (f i j)
		  | Some i, None | None, Some i -> Some (i, None, false)
		  | _ -> None
		and right = match oir, ojr with
		  | Some i, Some j -> Some (f i j)
		  | Some i, None | None, Some i -> Some (i, None, false)
		  | _ -> None in
		  match left, right with
		    | Some (l, eql, bl), Some (r, eqr, br) -> 
			P (l, r), comb eql eqr, (bl || br)
		    | Some (l, eql, bl), None -> 
			Left l, comb eql None, bl
		    | None, Some (r, eqr, br) -> 
			Right r, comb None eqr, br
		    | _ -> failwith "Node_ID.fusion_eq: this should never happen"
	      end in
      let k, eq, b = f i j in 
	if b then eq, Some k else None, None

    (******************************************)
    (*    /\        /\               /\       *)
    (*   /  \      /  \   -->       /  \      *)
    (*  /   /      \   \           /\  /\     *)
    (* a    c       b   d         a b  c d    *)
    (******************************************)
    (*    /\        /\                        *)
    (*   /  \      /  \   -->   error         *)
    (*  /   /     /    \                      *)
    (* a    c    a      d                     *)
    (******************************************)	    
    let rec union: t -> t -> t = fun i j ->
      match i, j with
	| P (x, y), P (z, t) -> P (union x z, union y t)
	| Left x, P(y, z) | P (x, z), Left y -> P (union x y, z)
	| Right x, P(y, z) | P (y, x), Right z -> P (y, union x z)
	| Left x, Right y | Right y, Left x -> P (x, y)
	| _ -> failwith "Node_ID.union: args must be disjoint"

    let compare: t -> t -> int = fun s t -> String.compare (pp s) (pp t) 

  end

module Node_IDMap = Map.Make( Node_ID )
module Node_IDSet = Set.Make( Node_ID )

module Nodes_Mapping:
sig
  type b
  val empty: b
  val identity: b
  val get: int -> b -> int option
  val get_rev: int -> b -> IntSet.t
  val add: int -> int -> b -> b
  type t
  val mapsto: Node_ID.t -> t -> Node_ID.t
  val is_mapped_by: Node_ID.t -> t -> Node_IDSet.t
  val combine: t -> t -> t
end = struct
  type b = 
      Partial_Identity of int IntMap.t * IntSet.t IntMap.t
    | Enum of int IntMap.t * IntSet.t IntMap.t
  let empty: b = Enum (IntMap.empty, IntMap.empty)
  let identity: b = Partial_Identity (IntMap.empty, IntMap.empty)
  let get: int -> b -> int option = fun i -> function
    | Partial_Identity (m, _) ->
	begin 
	  try Some (IntMap.find i m) with | Not_found -> Some i
	end
    | Enum (m, _) ->
	begin 
	  try Some (IntMap.find i m) with | Not_found -> None
	end

  let pi_get_rev k rev = try IntMap.find k rev with | Not_found -> IntSet.singleton k
  let en_get_rev k rev = try IntMap.find k rev with | Not_found -> IntSet.empty

  let get_rev: int -> b -> IntSet.t = fun i -> function
    | Partial_Identity (_, rev) -> pi_get_rev i rev
    | Enum (_, rev) -> en_get_rev i rev

  let pi_add_rev k i rev =
    let rev_k = pi_get_rev k rev in
    let rev_k = IntSet.add i rev_k in
      if IntSet.cardinal rev_k = 1 && i=k then 
	IntMap.remove k rev
      else
	IntMap.add k rev_k rev
  let en_add_rev k i rev =
    let rev_k = pi_get_rev k rev in
    let rev_k = IntSet.add i rev_k in
      IntMap.add k rev_k rev
  let pi_rm_rev k i rev =
    let rev_k = pi_get_rev k rev in
    let rev_k = IntSet.remove i rev_k in
      if IntSet.cardinal rev_k = 1 && IntSet.choose rev_k = k then 
	IntMap.remove k rev
      else
	IntMap.add k rev_k rev
  let en_rm_rev k i rev =
    let rev_k = pi_get_rev k rev in
    let rev_k = IntSet.remove i rev_k in
      if IntSet.is_empty rev_k then
	IntMap.remove k rev
      else
	IntMap.add k rev_k rev

  let add: int -> int -> b -> b = fun i j -> function 
    | Partial_Identity (m, rev) -> 
	if IntMap.mem i m then
	  (* i is mapped to some k *)
	  let k = IntMap.find i m in
	  let rev = pi_rm_rev k i rev in	    
	  let rev = pi_add_rev j i rev in
	    Partial_Identity (IntMap.add i j m, rev) 
	else
	  (* i is mapped to i *)
	  let rev = pi_rm_rev i i rev in
	  let rev = pi_add_rev j i rev in
	    Partial_Identity (IntMap.add i j m, rev) 
    | Enum (m, rev) -> 
	if IntMap.mem i m then
	  (* i is mapped to some k *)
	  let k = IntMap.find i m in
	  let rev = en_rm_rev k i rev in	    
	  let rev = en_add_rev j i rev in
	    Partial_Identity (IntMap.add i j m, rev) 
	else
	  (* i is not mapped *)
	  let rev = pi_add_rev j i rev in
	    Partial_Identity (IntMap.add i j m, rev) 
	  
  type t = b BinaryTree.t
  let b_mapsto: int -> b -> int = fun i (m, _) ->
    try IntMap.find i m 
    with | Not_found -> i
  let rec mapsto: Node_ID.t -> t -> Node_ID.t = fun p t ->
    match t with
      | BinaryTree.Empty -> failwith "Nodes_Mapping.mapsto: t is an Empty tree\n"
	(* this can fail if p isn't All or Id *)
      |	BinaryTree.Leaf b -> Node_ID.Id (b_mapsto (Node_ID.get p) b)
      | BinaryTree.Node (t1, t2) -> 
	  begin
	    match p with
	      | Node_ID.P (p1, p2) -> Node_ID.P (mapsto p1 t1, mapsto p2 t2)
	      | Node_ID.Left p -> Node_ID.Left (mapsto p t1) 
	      | Node_ID.Right p -> Node_ID.Right (mapsto p t2)
	      | _ -> failwith "Nodes_Mapping.mapsto: bad args\n"
	  end	  
  let b_is_mapped_by: int -> b -> int list = fun i (_, m) -> 
    []
  let is_mapped_by: Node_ID.t -> t -> Node_ID.t list = fun p t ->
    []
  let combine: t -> t -> t = fun t1 t2 -> BinaryTree.Node (t1, t2)
end
