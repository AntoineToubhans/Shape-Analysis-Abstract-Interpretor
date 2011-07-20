open Offset
open Utils
open Domain_sig
open Neq_pred_domain
open SL_graph_domain
open Inductive_def
open SL_domain
open Simple_C_syntax
open Functor_SL2DIS

(* =========================================================== *)
(* Module Domain Functor                                       *)
(* =========================================================== *)
(*                                        Created: AT 06/30/11 *)
(*                                  Last modified: AT 06/30/11 *)

let error(s: string) = failwith (Printf.sprintf "DOMAIN_ERROR: %s" s)

module MAKE_DOMAIN =
  functor (D: DIS_DOMAIN) -> functor (O: OPTION) ->
    (struct

       let debug = O.debug 

       type t = 
	   { env: int IntMap.t;
	     heap: D.t;
	     var_decls: sc_var StringMap.t;
	     struct_decls: sc_struct_decl StringMap.t}

       let pp: t -> unit = fun t ->
	 Printf.printf "**************************************\n";
	 Printf.printf "*****-------Print DOMAIN --------*****\n";
	 Printf.printf "**************************************\nENV:\n";
	 StringMap.iter
	   (fun s v -> Printf.printf "&%s -------------> %i\n" s (IntMap.find v.var_uniqueId t.env))
	   t.var_decls;
	 Printf.printf "HEAP:\n%s" (D.pp t.heap); 
	 Printf.printf "**************************************\n"

       let init: t = 
	 { env = IntMap.empty;
	   heap = D.init;
	   var_decls = StringMap.empty;
	   struct_decls = StringMap.empty}

       let rec get_type_hv: sc_hvalue -> t -> sc_type = fun e t ->
	 if debug then print_debug "DOMAIN: [rec] get type of sc_hvalue %s \n" (sc_hvalue2str e);
	 match e with
	   | Var x ->
	       (StringMap.find x t.var_decls).var_type
	   | ArrayAccess(i, e) ->
	       begin
		 match get_type_hv e t with
		   | Array ty -> ty
		   | _ -> error 
		       (Printf.sprintf "inconsistant expression %s" (sc_hvalue2str (ArrayAccess(i, e))))
	       end
	   | FieldAccess (f, e) ->
	       begin
		 match get_type_hv e t with
		   | Struct s ->
		       begin try List.assoc s (snd (StringMap.find s t.struct_decls))
		       with | _ -> error "bad record field argument" 
		       end 
		   | _ -> error  
		       (Printf.sprintf "inconsistant expression %s" (sc_hvalue2str (FieldAccess (f, e))))
	       end
	   | Deref e ->
	       begin
		 match get_type_hv e t with
		   | PointerTo ty -> ty
		   | _ -> error  
		       (Printf.sprintf "inconsistant expression %s" (sc_hvalue2str (Deref e)))
	       end

       let get_type_vv: sc_vvalue -> t -> sc_type = fun e t ->
	 if debug then print_debug "DOMAIN: get type of sc_vvalue %s \n" (sc_vvalue2str e);
	 match e with
	   | Malloc _ -> PointerTo(Void)
	   | Address e -> PointerTo (get_type_hv e t)
	   | FloatConst _ -> ScFloat 
	   | IntConst _ -> ScInt
	   | Null -> PointerTo(Void)

       let get_type: sc_exp -> t -> sc_type = fun e t ->
	 if debug then print_debug "DOMAIN: get type of sc_exp %s \n" (sc_exp2str e);
	 match e with
	   | VValue e -> get_type_vv e t
	   | HValue e -> get_type_hv e t


       let rec get_fields: sc_type -> t -> offset list = fun ty t -> 
	 if debug then print_debug "DOMAIN: get fields %s \n" (sc_type2str ty);
	 match ty with
	   | Void -> error "don't know fields corresponding to void"
	   | ScInt | ScFloat | PointerTo _ -> [Zero]
	   | Struct s ->
	       begin
		 try
		   List.map (fun (s, ty) -> RecordField(s, Zero)) (snd (StringMap.find s t.struct_decls))
		 with
		   | _ -> error "bad record field argument"
	       end
	   | Array _ -> 
	       error "array: feature not supported yet"

       let rec get_entry_point_hv: sc_hvalue -> t -> int = fun e t ->
	 if debug then print_debug "DOMAIN: [rec] get entry_point of sc_hvalue %s \n" (sc_hvalue2str e);
	 match e with
	   | ArrayAccess (_, e) | FieldAccess(_, e) | Deref e ->
	       get_entry_point_hv e t
	   | Var x -> 
	       IntMap.find (StringMap.find x t.var_decls).var_uniqueId t.env

       let get_entry_point_vv: sc_vvalue -> t -> int = fun e t ->
	 if debug then print_debug "DOMAIN: get entry_point of sc_vvalue %s \n" (sc_vvalue2str e);
	 match e with
	   | Address e -> get_entry_point_hv e t
	   | _ -> 0 (* useless in those particular cases *)

       let get_entry_point: sc_exp -> t -> int = fun e t -> 
	 if debug then print_debug "DOMAIN: get entry_point of sc_exp %s \n" (sc_exp2str e);
	 match e with
	   | HValue e -> get_entry_point_hv e t
	   | VValue e -> get_entry_point_vv e t	       

       let eval_sc_assignment: sc_assignment -> t -> t = fun (la, ra) t -> 
	 if debug then print_debug "DOMAIN: eval sc_assignment %s \n" (sc_assignment2str (la, ra));
	 let ty = get_type_hv la t in
	 let l_o = get_fields ty t 
	 and l_o_malloc = 
	   match ty with | PointerTo ty -> (get_fields ty t) | _ -> [] 
	 and i = get_entry_point_hv la t and j = get_entry_point ra t in
	   { t with heap = D.mutation l_o l_o_malloc i j (la, ra) t.heap }

       let eval_sc_struct_decl: sc_struct_decl -> t -> t = fun s t -> 
	 {t with struct_decls = StringMap.add (fst s) s t.struct_decls }

       let eval_sc_var_decl: sc_var_decl -> t -> t = fun (x, oe) t -> 
	 if debug then print_debug "DOMAIN: eval sc_var_decl %s \n" (sc_var_decl2str (x, oe));
	 if IntMap.mem x.var_uniqueId t.env || StringMap.mem x.var_name t.var_decls then
	   error (Printf.sprintf "declaration of var %s : already exists..." (sc_var2str x));
	 let fields = get_fields x.var_type t in
	 let heap, i = D.var_alloc fields t.heap in
	   { env = IntMap.add x.var_uniqueId i t.env;
	     heap = heap;
	     var_decls = StringMap.add x.var_name x t.var_decls;
	     struct_decls = t.struct_decls;}

       let eval_spec: spec -> t -> t = fun s t -> 
	 if debug then print_debug "DOMAIN: eval spec\n";
	 match s with
	   | Add_Induct(e1, e2, l1, l2) ->
	       let i = get_entry_point_hv e1 t
	       and j = get_entry_point e2 t in
		 { t with heap = D.spec_assume_inductive i j e1 e2 l1 l2 t.heap }
	       
       let filter: sc_cond -> t -> t * t = fun c t -> 
	 if debug then print_debug "DOMAIN: filter %s\n" (sc_cond2str c);
	 let ei, ej = 
	   match c with | Eq(ei, ej) | Neq(ei, ej) -> ei, ej in
	 let i = get_entry_point ei t and j = get_entry_point ej t 
	 and l_o = get_fields (get_type ei t) t in 
	 let heap1, heap2 = D.filter l_o i j c t.heap in
	   {t with heap = heap1}, {t with heap = heap2}

       let union: t -> t -> t = fun t1 t2 ->
	 if debug then print_debug "DOMAIN: Union\n";
	 (* t1.env & t2.env shoul'd be the same *)
	 (* t1.struct_decls & t2.struct_decls shoul'd be the same *)
	 { t1 with heap = D.union t1.heap t2.heap}

       let widening: t -> t -> t = fun t1 t2 ->
	 if debug then print_debug "DOMAIN: Widening\n";
	 (* t1.env & t2.env shoul'd be the same *)
	 (* t1.struct_decls & t2.struct_decls shoul'd be the same *)
	 { t1 with heap = D.widening t1.heap t2.heap}

       let is_include: t -> t -> bool = fun t1 t2 -> 
	 if debug then print_debug "DOMAIN: is include\n";
	 D.is_include t1.heap t2.heap

       let rec eval_sc_command: t -> sc_command -> t = fun t c -> 
	 if debug then print_debug "DOMAIN: [rec] eval command %s\n" (sc_command2str c);
	 Printf.printf "BEFORE: %s\n" (sc_command2str c);
	 pp t;
	 match c with
	   | Assignment a -> 
	       eval_sc_assignment a t
	   | StructDeclaration sd ->
	       eval_sc_struct_decl sd t
	   | VarDeclaration vd ->
	       eval_sc_var_decl vd t 
	   | Seq block -> 
	       List.fold_left eval_sc_command t block
	   | If(cond, b1, b2) ->
	       let t1, t2 = filter cond t in
	       let t1 = List.fold_left eval_sc_command t1 b1
	       and t2 = List.fold_left eval_sc_command t2 b2 in
	       union t1 t2
	   | While(cond, block) -> 
	       let t1, t2 = filter cond t in
	       let t_entry_loop = ref t1 
	       and t_mem = ref {t with heap = D.bottom} 
	       and t_out = ref t2 
	       and counter = ref 0 in
		 while not (is_include !t_entry_loop !t_mem) do
		   t_mem := !t_entry_loop;
		   counter:= 1 + !counter;
		   let t1, t2 = 
		     if !counter <3 then
		       filter cond 
			 (union t 
			    (List.fold_left eval_sc_command !t_entry_loop block)) 
		     else 
		       filter cond 
			 (widening t 
			    (List.fold_left eval_sc_command !t_entry_loop block)) in
		     t_entry_loop := t1;
		     t_out := t2;
		 done; !t_out
	   | Spec s -> 
	       eval_spec s t

     end: DOMAIN)
