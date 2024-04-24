module BExp = struct
  (** Module for working with boolean expressions *)

  type t = t_ Hashcons.hash_consed
  (** The type for a hashconsed boolean expression *)

  (* The internal type of the boolean expression*)
  and t_ =
    | Zero
    | One
    | PBool of string
    | Or of t * t
    | And of t * t
    | Not of t

  (** table used for hash consing 
    notice because of hash consing, we can build *)
  let tbl = Hashcons.create 251

  let hashcons = Hashcons.hashcons tbl
  let zero : t = hashcons @@ Zero
  let one : t = hashcons One
  let pBool (str : string) : t = hashcons @@ PBool str

  let b_not (b1 : t) : t =
    if b1 == one then zero else if b1 == zero then one else hashcons @@ Not b1

  let b_or (b1 : t) (b2 : t) : t =
    if b1 == one then one
    else if b2 == one then one
    else if b1 == zero then b2
    else if b2 == zero then b1
    else if b1 == b2 then b1
    else if b1 == b_not b2 then one
    else hashcons @@ Or (b1, b2)

  let b_and (b1 : t) (b2 : t) : t =
    if b1 == one then b2
    else if b2 == one then b1
    else if b1 == zero then zero
    else if b2 == zero then zero
    else if b1 == b2 then b1
    else if b1 == b_not b2 then zero
    else hashcons @@ And (b1, b2)

  let z3_empty_ctx = Z3.mk_context []

  (** convert a boolean expression to z3 expression *)
  let rec to_z3 (b : t) : Z3.Expr.expr =
    let open Z3.Boolean in
    match b.node with
    | Zero -> mk_false z3_empty_ctx
    | One -> mk_true z3_empty_ctx
    | PBool str -> mk_const_s z3_empty_ctx str
    | Or (b1, b2) -> mk_or z3_empty_ctx [ to_z3 b1; to_z3 b2 ]
    | And (b1, b2) -> mk_and z3_empty_ctx [ to_z3 b1; to_z3 b2 ]
    | Not b1 -> mk_not z3_empty_ctx @@ to_z3 b1

  (** test if a boolean expression is constant false
      
  In other word, whether it is unsatisfiable. *)
  let is_false (b : t) : bool =
    let solver = Z3.Solver.mk_solver z3_empty_ctx None in
    match Z3.Solver.check solver [ to_z3 b ] with
    | Z3.Solver.UNSATISFIABLE -> true
    | _ -> false
end

module Exp = struct
  type t = t_ Hashcons.hash_consed
  (** hashconsed GKAT expression*)

  and t_ =
    | Pact of string
    | Seq of t * t
    | If of BExp.t * t * t
    | Test of BExp.t
    | While of BExp.t * t

  (** table used for hash consing 
  notice because of hash consing, we can build *)
  let tbl = Hashcons.create 251

  let hashcons : t_ -> t = Hashcons.hashcons tbl
  let p_act (p : string) : t = hashcons @@ Pact p
  let test (b : BExp.t) : t = hashcons @@ Test b
  let skip : t = test BExp.one
  let fail : t = test BExp.zero

  let seq (e : t) (f : t) : t =
    match (e.node, f.node) with
    | Test a, Test b -> test (BExp.b_and a b)
    | _ ->
        if e == skip then f
        else if f == skip then e
        else if e == fail then fail
        else if f == fail then fail
        else hashcons @@ Seq (e, f)

  let if_then_else (b : BExp.t) (e : t) (f : t) : t =
    if b == BExp.one then e
    else if b == BExp.zero then f
    else if e == fail then seq (test @@ BExp.b_not b) f
    else if f == fail then seq (test b) f
    else hashcons @@ If (b, e, f)

  let while_do (b : BExp.t) (e : t) : t = hashcons @@ While (b, e)
end

module Derivatives = struct
  (** defines derivatives *)

  type ('k, 'v) map = ('k, 'v) Hashcons.Hmap.t
  (** a fast immutable map for hashconsed key *)

  (** The epsilon of the expression,
      
  The boolean expression consists of all the atoms 
  that is accepted by the expression *)
  let epsilion (exp : Exp.t) : BExp.t = _

  (** The derivative of a expression: δ ∈ exp -> (BExp ↛ exp × Σ)
  
  This uses the map representation of the derivative for the ease of implementation,
  and primitive action is encoded as a string *)
  let derivative (exp : Exp.t) : (BExp.t, Exp.t * string) map = _
end

module Equiv = struct
  module LiveExps : sig
    val is_live : Exp.t -> bool
  end = struct
    open Derivatives
    (** Modules for computing live expressions. 
    This module performs a modified Tarjan's algorithm to find live states.
    
    This is a seperate module, since it contains internal states.*)

    (** current index to assign to the next node*)
    let cur_idx : int ref = ref 0

    (** A stack that contains all explored expression that haven't been assigned to a SCC*)
    let stack : Exp.t Stack.t = Stack.create ()

    type expInfo = {
      idx : int;
      (* the element used for SCC, which is represented as an union-find object*)
      elem : Exp.t UnionFind.elem;
      (* the lowest reachable index from the current expression *)
      mutable low_link : int;
      (* whether the expression is on the stack.

         This variable is to aviod the linear time check of whether a expression is in the stack.*)
      mutable on_stack : bool;
    }

    (** find the representative expression of for the SCC of the input `e` 
        
    This function assumes that the SCC of the expression `e` 
    has already been collected as a union-find object*)
    let rep (info_of_e : expInfo) : Exp.t =
      UnionFind.get @@ UnionFind.find info_of_e.elem

    (** A mutable hash table of expressions *)
    module ExpTbl = Hashtbl.Make (struct
      type t = Exp.t

      let hash (e : t) = e.hkey
      let equal e1 e2 = e1 == e2
    end)

    (** a mutable hash set of expressions *)
    module ExpHSet = struct
      type t = unit ExpTbl.t

      let create : int -> t = ExpTbl.create
      let add (exp : Exp.t) (s : t) : unit = ExpTbl.add s exp ()
      let remove (exp : Exp.t) (s : t) : unit = ExpTbl.remove s exp

      let mem (exp : Exp.t) (s : t) : bool =
        Option.is_some @@ ExpTbl.find_opt s exp
    end

    (** get the info of a particular expression 
        
    TODO: use the expression size to compute the reachable expressions, instead of a fixed number.*)
    let info_of : expInfo ExpTbl.t = ExpTbl.create 251

    (* Whether a expression transitions to a live scc

       Notice that if a expression is in the set, then exp is necessarily live,
       but if it is not, exp is not necessarily dead.
       This only keeps track of the expression on the stack,
       expressions not on the stack but explored are already collected as scc,
       hence should use `live_scc` instead.*)
    let to_live_scc : ExpHSet.t = ExpHSet.create 251

    (* all the currently discovered live scc,
       each scc is marked by its "representing expression" in the union-find object.
       for a expression `e`, the representing expression for its scc
       can be computed by `rep_{scc} e`.*)
    let live_scc : ExpHSet.t = ExpHSet.create 251

    (** visit the predecessor of e
    
    this will set the info of e to the correct value 
    and compute the `detected_liveness` of `e`.
    **this function assumes `e` is in the `info_of` table.** *)
    let rec visit_predecessor_of (e : Exp.t) (info_of_e : expInfo) : unit =
      let e_to_live_scc : bool ref = ref false in
      (* visit the predecessor `e'` of `e`.*)
      let visit_single_predecessor (e' : Exp.t) : unit =
        (* f hasn't been explored, then explore f *)
        if not @@ ExpTbl.mem info_of e' then (
          visit e';
          let info_of_e' = ExpTbl.find info_of e' in
          info_of_e.low_link <- min info_of_e.low_link info_of_e'.low_link)
        else
          let info_of_e' = ExpTbl.find info_of e' in
          if info_of_e'.on_stack then
            (* if f has been explored, and on stack, then it is in the scc of e
               Thus we update the `low_link` of `e`*)
            info_of_e.low_link <- min info_of_e.low_link info_of_e'.low_link
          else
            (* if f explored but not on stack This means that f is part of an explored scc. We will update the `e_to_live_scc` value *)
            e_to_live_scc :=
              !e_to_live_scc || ExpHSet.mem (rep info_of_e') live_scc
      in
      Hashcons.Hmap.iter
        (fun _bexp (e', _p) -> visit_single_predecessor e')
        (derivative e)

    and construct_scc_of e : unit =
      (* pop the top element of the stack and return whether it is live *)
      let pop_to_live_scc () = _ in
      _

    and visit (e : Exp.t) : unit = _

    let is_live = _
  end
end
