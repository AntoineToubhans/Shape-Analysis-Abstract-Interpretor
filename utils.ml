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
	  
type 'a bTree = Empty | Leaf of 'a | Node of 'a bTree * 'a bTree 
  
let rec bTree_flatten: 'a bTree list -> 'a bTree list = fun l ->
  match l with
    | [] -> []
    | t::[] -> [t]
    | t1::t2::l -> (Node (t1, t2))::(bTree_flatten l)

let list2bTree: 'a list -> 'a bTree = fun l ->
  let rec f l = 
    match l with | [] -> Empty | t::[] -> t | _ -> f (bTree_flatten l) in
    f (List.map (fun a -> Leaf a) l)


let rec pp_blank: int -> unit = fun i ->
  if i>0 then begin 
    Printf.printf "-"; 
    pp_blank (i-1)
  end

let rec bTree_pp_r: int -> ('a -> string) -> 'a bTree -> unit = fun i p t ->
  pp_blank i;
  match t with
    | Empty -> Printf.printf "Empty\n" 
    | Leaf a -> Printf.printf "%s\n" (p a)
    | Node (a, b) -> 
	Printf.printf "Prod:\n";
	bTree_pp_r (i+1) p a;
	bTree_pp_r (i+1) p b

let bTree_pp: ('a -> string) -> 'a bTree -> unit = fun p t -> bTree_pp_r 0 p t

module Node_ID = 
  struct
    type t =
	Id of int
      | Left of t
      | Right of t
      | P of t * t
	  
    let get: t -> int = function 
      | Id x -> x
      | _ -> failwith "can't get the node ID"
	  
    let left: t -> t option = function
      | Left x | P (x, _) -> Some x
      | _ -> None
    let right: t -> t option = function
      | Right x | P (_, x) -> Some x
      | _ -> None

    let rec fusion: t -> t -> t -> t = fun i j k -> 
      match i, j, k with
	| Left i, Left j, Left k -> Left (fusion i j k)
	| Left i, Left j, P (k, r) -> P (fusion i j k, r)
	| Right i, Right j, Right k -> Right (fusion i j k)
	| Right i, Right j, P (l, k) -> P (l, fusion i j k)
	| Id i, Id j, Id k -> Id (if i=k then j else k)
	| _ -> failwith "Node_ID.fusion error"

    let rec max: t -> t -> t = fun t1 t2 ->
      match t1, t2 with
	| Id x, Id y -> Id (Pervasives.max x y)
	| Id _, t | t, Id _ -> t
	| P (t11, t12), P (t21, t22) -> P (max t11 t21, max t12 t22)
	| Left t, P (t2, t3) | P (t2, t3), Left t -> P (max t t2, t3)
	| Right t, P (t2, t3) | P (t2, t3), Right t -> P (t2, max t t3)
	| Left t1, Right t2 | Right t2, Left t1 -> P (t1, t2)
	| Right t1, Right t2 -> Right (max t1 t2)
	| Left t1, Left t2 -> Left (max t1 t2)

    let rec pp: t -> string = function 
      | Id x -> Printf.sprintf "Id %i" x
      | Left t -> Printf.sprintf "Left (%s)" (pp t)
      | Right t -> Printf.sprintf "Right (%s)" (pp t)
      | P (t1, t2) -> Printf.sprintf "P (%s, %s)" (pp t1) (pp t2)

  end


