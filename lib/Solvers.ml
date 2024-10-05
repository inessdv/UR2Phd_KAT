(***** Solver functor *****)

module type Solver = sig
    (*functor for solvers*)
    type func_t
    type context
    type solver
  
    val mk_true: context -> func_t
    val mk_false: context -> func_t
    val mk_pBool: context -> string -> func_t
    val mk_not: context -> func_t -> func_t
    val mk_or: context -> func_t list -> func_t
    val mk_and: context -> func_t list -> func_t
    (*val mk_solver: context -> 'a option -> solver*)
    val to_z3: 'a * func_t -> func_t
    (*val mk_iff: context -> 'a * func_t -> 'a * func_t -> func_t*)
    val is_false: context -> 'a * func_t -> bool
end


module Z3_solver: Solver = struct

  type func_t = Z3.Expr.expr
  type context =  Z3.context
  type solver = Z3.Solver.solver

  let mk_context (): context = 
    Z3.mk_context []
  let mk_true (ctx: context) : func_t =
    Z3.Boolean.mk_true ctx
  
  let mk_false (ctx: context) : func_t =
    Z3.Boolean.mk_true ctx

  let mk_pBool (ctx:context) (str: string): func_t =
    Z3.Boolean.mk_const_s ctx str
  let mk_not (ctx: context) (z:func_t): func_t =
    Z3.Boolean.mk_not ctx z
  let mk_or (ctx: context) (z3_list: func_t list): func_t =
    Z3.Boolean.mk_or ctx z3_list
  let mk_and (ctx: context) (z3_list:func_t list): func_t =
    Z3.Boolean.mk_and ctx z3_list
  
  (*let mk_solver (ctx:context) (a: 'a option): solver = (*check option type?*)
    Z3.Solver.mk_solver ctx None*)
    
  let to_z3 (b:'a * func_t): func_t = snd b
  let is_false (ctx:context) (b_z1:'a * func_t): bool =
    match Z3.Solver.check (Z3.Solver.mk_solver ctx None) [ to_z3 b_z1 ] with
   | Z3.Solver.UNSATISFIABLE -> true
   | _ -> false

  let equiv (ctx: context) (b_z1:'a * func_t) (b_z2:'a * func_t) : bool =
    let iff_exp = Z3.Boolean.mk_iff ctx (to_z3 b_z1) (to_z3 b_z2) in
    let not_iff_exp = mk_not ctx iff_exp in 
    (* if ¬ (b1 ↔ b2) is unsatisfiable, then b1 ↔ b2 is a tautology,
       thus b1 and b2 are semantically equivalent.*)
    match Z3.Solver.check (Z3.Solver.mk_solver ctx None) [ not_iff_exp ] with
    | Z3.Solver.UNSATISFIABLE -> true
    | _ -> false
  

end


module Mlbdd_solver: Solver = struct
  type func_t = MLBDD.t
  type context = MLBDD.init ()
  let mk_true = MLBDD.dtrue
  let mk_false = MLBDD.dfalse
end
