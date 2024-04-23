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
  (** define the datat type of on-the-fly automaton *)

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

  module LiveExps : sig
    val is_live : Exp.t -> bool
  end = struct
    (** Modules for computing live expressions. 
    This module performs a modified Tarjan's algorithm to find live states.
    
    This is a seperate module, since it contains internal states.*)

    (** current index to assign to the next node*)
    let cur_idx : int ref = ref 0

    (** A stack that contains all explored expression that haven't been assigned to a SCC*)
    let stack : Exp.t Stack.t = Stack.create ()

    type expInfo = {
      idx : int;  (** the lowest reachable index from the current expression *)
      mutable low_link : int;
          (** whether the expression is on the stack. 
          
      This variable is to aviod the linear time check of whether a expression is in the stack.*)
      mutable on_stack : bool;
    }
    (** some attributes of a expression used in Tarjan's algorithm *)

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
    let visit_predecessor_of (e: Exp.t): unit = _
    let is_live = _
  end
end
