(* ============ simple C ========= *)
type sc_record_field = string
type sc_array_i = int

type sc_type = 
  | Void
  | ScInt
  | ScFloat
  | Array of sc_type
  | Struct of string
  | PointerTo of sc_type

type sc_struct_decl = string*(sc_record_field*sc_type) list

type sc_uniqueId = int

type sc_var = 
    { var_name:      string;     (* name *)
      (*sc_var_extent:   extent;     (* position in the source file *) *)
      var_type:      sc_type;     (* type *)
      var_uniqueId:  sc_uniqueId; (* key *) }

and sc_var_decl = sc_var * sc_exp option

and sc_hvalue = (*heap value*)
  | Var of string
  | ArrayAccess of sc_array_i*sc_hvalue
  | FieldAccess of sc_record_field*sc_hvalue
  | Deref of sc_hvalue

and sc_vvalue = (*virtual value*)
  | Malloc of int
  | Address of sc_hvalue
  | FloatConst of float
  | IntConst of int
  | Null

and sc_exp =
  | HValue of sc_hvalue 
  | VValue of sc_vvalue

type sc_assignment =  sc_hvalue * sc_exp (* e1:=e2 *)

type sc_cond = 
  | Eq of sc_exp*sc_exp (* e1==e2 *)
  | Neq of sc_exp*sc_exp (* e1!=e2 *)

type spec = 
  | Add_Induct of sc_exp * sc_exp * int list * int list 

type sc_command = 
    | Assignment of sc_assignment
    | StructDeclaration of sc_struct_decl
    | VarDeclaration of sc_var_decl
    | Seq of sc_block
    | If of sc_cond * sc_block * sc_block
    | While of sc_cond * sc_block
and sc_block = sc_command list

(* ======== pretty printers ============ *)
let sc_record_field2str(s: sc_record_field) = s

let sc_array_i2str(i: sc_array_i) = 
  Printf.sprintf "%i" i

let rec sc_type2str(t: sc_type) = 
  match t with
    | Void -> "void"
    | ScInt -> "int"
    | ScFloat -> "float"
    | Array t -> Printf.sprintf "%s[]" (sc_type2str t)
    | PointerTo t -> Printf.sprintf "%s*" (sc_type2str t)
    | Struct s-> Printf.sprintf "struct %s" s
 
let sc_struct_decl2str(d: sc_struct_decl) =
  Printf.sprintf "struct %s{\n%s}\n" (fst d)
    (List.fold_left (fun s (f,t)-> Printf.sprintf "%s\t%s %s;\n" s (sc_type2str t) f) "" (snd d))

let sc_uniqueId2str(i: sc_uniqueId) = Printf.sprintf "%i" i

let sc_var2str(v: sc_var) = v.var_name

let rec sc_hvalue2str_aux(e: sc_hvalue) = (* to deal with parentethis (*x).f & *x.f *)*)
  match e with
    | Var v -> v, false
    | ArrayAccess(i, e) -> 
	let s, b= sc_hvalue2str_aux e in
	  if b then
	    Printf.sprintf "(%s)[%i]" s i, false
	  else
	    Printf.sprintf "%s[%i]" s i, false
    | FieldAccess(f, e) -> 
	let s, b= sc_hvalue2str_aux e in
	  if b then
	    Printf.sprintf "(%s).%s" (fst (sc_hvalue2str_aux e)) f, false
	  else
	    Printf.sprintf "%s.%s" (fst (sc_hvalue2str_aux e)) f, false
    | Deref e -> Printf.sprintf "*%s" (fst (sc_hvalue2str_aux e)), true

let sc_hvalue2str(e: sc_hvalue) = fst (sc_hvalue2str_aux e)

let sc_vvalue2str(e: sc_vvalue) = 
  match e with
    | Malloc n -> Printf.sprintf "malloc(%i)" n
    | Address e -> Printf.sprintf "&%s" (sc_hvalue2str e)
    | FloatConst x -> Printf.sprintf "%f" x
    | IntConst i -> Printf.sprintf "%i" i
    | Null -> "NULL"

let sc_exp2str(e: sc_exp) = 
  match e with
    | HValue e -> sc_hvalue2str e
    | VValue e -> sc_vvalue2str e

let sc_var_decl2str(d: sc_var_decl) =
  let v = fst d in
    match (snd d) with
      | None -> Printf.sprintf "%s %s;\n" (sc_type2str v.var_type) v.var_name
      | Some e -> Printf.sprintf "%s %s = %s;\n" (sc_type2str v.var_type) v.var_name (sc_exp2str e)


let sc_assignment2str(a: sc_assignment) =
  Printf.sprintf "%s = %s;\n" (sc_hvalue2str (fst a))(sc_exp2str (snd a))

let sc_cond2str(c: sc_cond) = 
  match c with
    | Eq(e, f) -> Printf.sprintf "%s==%s"  (sc_exp2str e) (sc_exp2str f)
    | Neq(e, f) -> Printf.sprintf "%s!=%s"  (sc_exp2str e) (sc_exp2str f)


let rec sc_command2str (p: sc_command)=
  match p with
    | Assignment a -> sc_assignment2str a
    | StructDeclaration sd -> sc_struct_decl2str sd
    | VarDeclaration vd -> sc_var_decl2str vd
    | Seq b -> sc_block2str b
    | If(c, b1, b2) ->
        Printf.sprintf "if(%s){\n%s}Else{\n%s}\n" (sc_cond2str c) (sc_block2str b1) (sc_block2str b2)
    | While(c, b) ->
        Printf.sprintf "while(%s){\n%s}\n" (sc_cond2str c) (sc_block2str b)

and sc_block2str(b: sc_block) =
  List.fold_left (fun s p -> Printf.sprintf "%s%s" s (sc_command2str p)) "" b 


(* ======= test pp======== 

let dll = ("dll",[("data", ScInt);("next", PointerTo(Struct "dll"));("prev", PointerTo(Struct "dll"))]) 
let l={var_name="l"; var_type=Struct "dll"; var_uniqueId=0;}
let rc={var_name="rc"; var_type=PointerTo(Struct "dll"); var_uniqueId=1;}

let ldecl=(l, None)
let rcdecl=(rc, Some(HValue(Malloc 42)))

let ass=(Deref(Var rc),HValue(Var l))

let c=Neq(HValue(Var rc), VValue Null)

let assw=(Var rc, HValue(FieldAccess("next", Deref(Var rc))))

let w=While(c, [Assignment assw])

let p=Seq [StructDeclaration dll; VarDeclaration ldecl; VarDeclaration rcdecl; Assignment ass; w]



let _ =   
  Printf.printf "%s" (sc_command2str p);
  
  
*)
