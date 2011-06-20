exception Offset_error of string
let offset_error(s: string) = raise (Offset_error (Printf.sprintf "OFFSET_ERROR: %s" s))

type offset =
    | Zero
    | RecordField of string*offset
    | ArrayRange of int*offset

let rec equals(o1: offset)(o2: offset) = 
  match o1, o2 with
    | Zero, Zero -> true
    | RecordField(s1, o1), RecordField(s2, o2) -> (String.compare s1 s2)==0 && equals o1 o2
    | ArrayRange(i1, o1), ArrayRange(i2, o2) -> i1==i2 && equals o1 o2
    | _, _ -> false

let rec pp_offset(o: offset)=
  match o with
    | Zero -> ""
    | RecordField(s, o)-> 
        Printf.sprintf "%s@%s" (pp_offset o) s
    | ArrayRange(i, o)->
        Printf.sprintf "%s+%i" (pp_offset o) i

(* this deals with inclusion of offset           *)
(* s.t. +3 is included in +3@n or +3+2@n@q       *)
(* i.e. ArrayField(3,Zero) <= RF("n",AF(3,Zero)) *)
let inclOffset(o: offset)(o2: offset) =
  let rec rev a b = 
    match a with
      | Zero -> b
      | RecordField(s, a) -> rev a (RecordField(s, b))
      | ArrayRange(i, a) -> rev a (ArrayRange(i, b))
  in
  let ro = rev o Zero and ro2 = rev o2 Zero in
  let rec aux a b = 
    match a, b with 
      | Zero, _ -> true
      | RecordField(s, a), RecordField(r, b) ->
          (String.compare s r)==0 && aux a b
      | ArrayRange(s, a), ArrayRange(r, b) ->
          s==r && aux a b
      | _ -> false 
  in
    aux ro ro2 

(* ===== replaceOffset o o1 o2 ==================*)
(* replace o1 by o2 in o                         *)
(* o  = +3@n@p = RF p (RF n (AF 3 Zero))         *)
(* o1 = +3     = AF 3 Zero                       *)
(* o2 = @q     = RF q Zero                       *)
(* res= @q@n@p = RF p (RF n (RF q Zero))         *)
(* ============================================= *)
let replaceOffset(o: offset)(o1: offset)(o2: offset) =
  let rec rev a b =
    match a with
      | Zero -> b
      | RecordField(s, a) -> rev a (RecordField(s, b))
      | ArrayRange(i, a) -> rev a (ArrayRange(i, b))
  in
  let ro = rev o Zero and ro1 = rev o1 Zero in
  let replace_error a b = 
    offset_error 
      (Printf.sprintf 
        "replacing offset failure: %s is not smaller than %s" 
        (pp_offset a) 
        (pp_offset b)) in
  let rec aux a b = 
    match a, b with 
      | Zero, _ -> b
      | RecordField(s, a), RecordField(r, b) ->
          if (String.compare s r)==0 then aux a b else replace_error o1 o
      | ArrayRange(s, a), ArrayRange(r, b) ->
          if s==r then aux a b else replace_error o1 o
      | _ -> 
          replace_error o1 o
  in
    rev (aux ro1 ro) o2

let rec appendOffset(o: offset) (o2: offset) = 
  match o with
    | Zero -> o2
    | RecordField(s, o)-> 
        RecordField(s, appendOffset o o2)
    | ArrayRange(i, o)->
        ArrayRange(i, appendOffset o o2)

(* !!!! to DO !!! *)
let cmp_offset o1 o2 = String.compare (pp_offset o1) (pp_offset o2) 

module OffsetOrd = 
  struct 
    type t = offset
    let compare: t -> t -> int = cmp_offset
  end

module OffsetMap = Map.Make(OffsetOrd)
module OffsetSet = Set.Make(OffsetOrd)
type offseted_node = int * offset
