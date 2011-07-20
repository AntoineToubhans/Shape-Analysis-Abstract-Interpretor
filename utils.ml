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

let injectionNSquare2N: (int * int) -> int = fun (x, y) ->
  x*x+y*y+2*x*y+x+3*y

let intlist2str: int list -> string = fun l ->
  match l with
    | [] -> "[]" 
    | x::l -> 
	"["^(List.fold_left (fun s a -> Printf.sprintf "%s, %i" s a) (Printf.sprintf "%i" x) l)^"]"
	  

(* tests
let l = [(0,2); (5,14); (5, 14); (0, 2)]

let f x y = fst x==fst y && snd x == snd y

let ll = delete_duplicates f l

let _ = 
  List.iter (fun x -> Printf.printf "%i %i\n" (fst x) (snd x)) l;
  List.iter (fun x -> Printf.printf "%i %i\n" (fst x) (snd x)) ll
*)
