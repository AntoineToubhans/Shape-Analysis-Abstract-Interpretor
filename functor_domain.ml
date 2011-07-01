open Offset
open Utils
open Domain_sig
open Neq_pred_domain
open SL_graph_domain
open Inductive_def
open SL_domain
open Simple_C_syntax
open SL_Functor_domain

(* =========================================================== *)
(* Module Domain Functor                                       *)
(* =========================================================== *)
(*                                        Created: AT 06/30/11 *)
(*                                  Last modified: AT 06/30/11 *)

let error(s: string) = failwith (Printf.sprintf "DOMAIN_ERROR: %s" s)

module MAKE_DOMAIN =
  functor (D: DIS_DOMAIN) -> 
    (struct

       type t = 
	   { env: int IntMap.t;
	     heap: D.t;
	     struct_defs: sc_struct_decl StringMap.t}

       let rec get_type_hv: sc_hvalue -> t -> sc_type = fun e t ->
	 if debug then print_debug "DOMAIN: [rec] get type of sc_hvalue %s \n" (sc_hvalue2str e);
	 match e with
	   | Var x ->
	       x.var_type
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
		       begin try List.assoc s (snd (StringMap.find s t.struct_defs))
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
		   List.map (fun (s, ty) -> RecordField(s, Zero)) (snd (StringMap.find s t.struct_defs))
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
	       IntMap.find x.var_uniqueId t.env

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

       let eval_sc_struct_decl: sc_struct_decl -> t -> t = fun s t -> t

       let eval_sc_var_decl: sc_var_decl -> t -> t = fun (x, oe) t -> 
	 if debug then print_debug "DOMAIN: eval sc_var_decl %s \n" (sc_var_decl2str (x, oe));
	 if IntMap.mem x.var_uniqueId t.env then
	   error (Printf.sprintf "declaration of var %s : already exists..." (sc_var2str x));
	 let t = { t with env = IntMap.add x.var_uniqueId 0 t.env } in
	   t 

     end: DOMAIN)
