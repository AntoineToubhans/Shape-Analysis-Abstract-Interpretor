open Simple_C_syntax
open Utils
open Offset
open Domain

let env_error(s: string) = failwith (Printf.sprintf "ENVIRONMENT_ERROR: %s" s)

module Env =
  functor (D: GRAPH_DOMAIN) ->
struct
  
  type stack_env = D.node StringMap.t
  
  type env = 
      { stack: stack_env;
	heap: D.t;}

  let rec getNodeFromHeapValue(e: env)(exp: sc_hvalue): env*D.node*offset = 
    match exp with 
      | Var x -> 
	  e, StringMap.find x.var_name e.stack, None
      | ArrayAccess(i, exp) ->
	  let e, a, o = getNodeFromHeapValue e exp in
	    e, a, ArrayRange(i, o)
      | FieldAccess(f, exp) ->
	  let e, a, o = getNodeFromHeapValue e exp in
	    e, a, RecordField(f, o)
      | Deffer exp ->
	  let e, a, o = getNodeFromHeapValue e exp in
	  let a, o = D.deffer e.heap a o in
	    e, a, o
      | Malloc _ ->
	  let t, a = D.createFreshNode e.heap in
	    {e with heap = t}, a, None

  let evalAssignment(e: env)(a: sc_assignment): env = 
    let e1, e2 = a in
      match e2 with 
	| HValue e2 ->
            let e, n1, o1 = getNodeFromHeapValue e e1 in
            let e, n2, o2 = getNodeFromHeapValue e e2 in
            let l = getEdgesFromNode (e.heap) n2 o2 in
            let t = D.removeEdgesFromNode (e.heap) n1 o1 in
            
	| VValue e2 -> 

end
