(***** Solver functor *****)
module type Solver = sig
    (*functor for solvers*)
    type func_t
    type context
    type solver
    
    val mk_context: context
    val mk_true: context -> func_t
    val mk_false: context -> func_t
    val mk_pBool: context -> int -> func_t
    val mk_not: context -> func_t -> func_t
    val mk_or: context -> func_t -> func_t -> func_t
    val mk_and: context -> func_t -> func_t -> func_t
    (*val mk_solver: context -> 'a option -> solver*)
    val to_solver: 'a * func_t -> func_t
    (*val mk_iff: context -> 'a * func_t -> 'a * func_t -> func_t*)
    val is_false: context -> 'a * func_t -> bool
    val equiv: context -> 'a * func_t -> 'a * func_t -> bool
    val to_string: func_t -> string
end


module Z3_solver: Solver = struct

  type func_t = Z3.Expr.expr
  type context =  Z3.context
  type solver = Z3.Solver.solver

  let mk_context: context = 
    Z3.mk_context []
  let mk_true (ctx: context) : func_t =
    Z3.Boolean.mk_true ctx
  
  let mk_false (ctx: context) : func_t =
    Z3.Boolean.mk_true ctx

  let mk_pBool (ctx:context) (num: int): func_t =
    let s_num = string_of_int num in
    Z3.Boolean.mk_const_s ctx ("b"^s_num)
  let mk_not (ctx:context) (z:func_t): func_t =
    Z3.Boolean.mk_not ctx z
  let mk_or (ctx: context) (b1_z3:func_t) (b2_z3:func_t): func_t =
    Z3.Boolean.mk_or ctx [ b1_z3; b2_z3 ]
  let mk_and (ctx: context) (b1_z3:func_t) (b2_z3:func_t): func_t =
    Z3.Boolean.mk_and ctx [ b1_z3; b2_z3 ]

  let to_solver (b:'a * func_t): func_t = snd b
  let is_false (ctx:context) (b_z1:'a * func_t): bool =
    match Z3.Solver.check (Z3.Solver.mk_solver ctx None) [ to_solver b_z1 ] with
   | Z3.Solver.UNSATISFIABLE -> true
   | _ -> false

  let equiv (ctx: context) (b_z1:'a * func_t) (b_z2:'a * func_t) : bool =
    let iff_exp = Z3.Boolean.mk_iff ctx (to_solver b_z1) (to_solver b_z2) in
    let not_iff_exp = mk_not ctx iff_exp in 
    (* if ¬ (b1 ↔ b2) is unsatisfiable, then b1 ↔ b2 is a tautology,
       thus b1 and b2 are semantically equivalent.*)
    match Z3.Solver.check (Z3.Solver.mk_solver ctx None) [ not_iff_exp ] with
    | Z3.Solver.UNSATISFIABLE -> true
    | _ -> false

    let to_string (e: func_t): string = Z3.Expr.to_string @@ e 
end

module Mlbdd_solver: Solver = struct
  type func_t = MLBDD.t
  type context = MLBDD.man
  type solver = unit

  let mk_context: context = 
    MLBDD.init ()
  let mk_true (ctx: context) : func_t =
    MLBDD.dtrue ctx
  let mk_false (ctx: context) : func_t =
    MLBDD.dfalse ctx
  let mk_pBool (ctx:context) (num: int): func_t =
    MLBDD.ithvar ctx num
  let mk_not (ctx:context) (z:func_t): func_t =
    MLBDD.dnot z
  let mk_or (ctx: context) (b1_:func_t) (b2_:func_t): func_t =
    MLBDD.dor b1_ b2_
  let mk_and (ctx: context) (b1_:func_t) (b2_:func_t): func_t =
    MLBDD.dand b1_ b2_

  let to_solver (b:'a * func_t): func_t = snd b
  let is_false (ctx:context) (b_:'a * func_t): bool =
    MLBDD.is_false (to_solver b_)

  let equiv (ctx: context) (b1_:'a * func_t) (b2_:'a * func_t) : bool =
    MLBDD.equal (to_solver b1_) (to_solver b2_)
  
  let to_string(e: func_t): string =
    MLBDD.to_string e

end
