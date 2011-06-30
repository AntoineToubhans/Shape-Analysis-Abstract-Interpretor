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

       type t = unit

       let eval_sc_assignment: sc_assignment -> t -> t = fun a t -> t
       let eval_sc_struct_decl: sc_struct_decl -> t -> t = fun s t -> t
       let eval_sc_var_decl: sc_var_decl -> t -> t = fun vd t -> t

     end: DOMAIN)
