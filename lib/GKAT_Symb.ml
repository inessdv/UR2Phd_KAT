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

  module Hmap = Hashcons.Hmap
  (** a fast immutable map for hashconsed key *)

  (** The epsilon of the expression,
      
  The boolean expression consists of all the atoms 
  that is accepted by the expression *)
  let rec epsilion (exp : Exp.t) : BExp.t =
    match exp.node with
    | Pact p -> BExp.zero
    | Seq (exp1, exp2) -> BExp.b_and (epsilion exp1) (epsilion exp2)
    | If (be, exp1, exp2) ->
        BExp.b_or
          (BExp.b_and be (epsilion exp1))
          (BExp.b_and (BExp.b_not be) (epsilion exp2))
    | Test be -> be
    | While (be, exp) -> BExp.b_not be

  (** The derivative of a expression: δ ∈ exp -> (BExp ↛ exp × Σ)
  
  This uses the map representation of the derivative for the ease of implementation,
  and primitive action is encoded as a string *)

  let combine_BE_with_a (be: BExp.t)(m: (BExp.t_, Exp.t * string) Hmap.t):(BExp.t_, Exp.t * string) Hmap.t=
      let to_list = Hmap.to_seq m in 
      let to_seq=Seq.map (fun (a,b) -> (BExp.b_and (a) (be),b) ) to_list in
      Hmap.of_seq to_seq
  
  let rec derivative (exp : Exp.t) : (BExp.t_, Exp.t * string) Hmap.t = 
    match exp.node with
    |Test _ -> Hmap.empty
    |Pact p -> Hmap.singleton(BExp.one)(Exp.test(BExp.one),p)
    |If (be, exp1, exp2) -> Hmap.union(combine_BE_with_a (be) (derivative exp1) )(combine_BE_with_a (be) (derivative exp2) )
    |_-> _
end

module Equiv = struct
  (** This module is DEPRECATED! Please disregard  *****)
  module LiveExps (Size : sig
    val size : int
    (** the size of all the expressions needing to check.
        
    This value is used to optmize hash table implementation*)
  end) : sig
    val is_live : Exp.t -> bool
  end = struct
    (** Modules for computing live expressions. 
    This module performs a modified Tarjan's algorithm to find live states.
    
    This is a seperate module, since it contains internal states.*)

    open Derivatives
    open Size
    module HSet = Hashcons.Hset

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

    (** tables mapping each expression to its info
        
    TODO: use the expression size to compute the reachable expressions, instead of a fixed number.*)
    let info_tbl : expInfo ExpTbl.t = ExpTbl.create Size.size

    (* Whether a expression transitions to a live scc

       Notice that if a expression is in the set, then exp is necessarily live,
       but if it is not, exp is not necessarily dead.
       This only keeps track of the expression on the stack,
       expressions not on the stack but explored are already collected as scc,
       hence should use `live_scc` instead.*)
    let to_live_scc : ExpHSet.t = ExpHSet.create size

    (* all the currently discovered live scc,
       each scc is marked by its "representing expression" in the union-find object.
       for a expression `e`, the representing expression for its scc
       can be computed by `rep_{scc} e`.*)
    let live_scc : ExpHSet.t = ExpHSet.create size

    (** get the info of a expression, will fail if the expression hasn't been explored*)
    let info_of (e : Exp.t) : expInfo = ExpTbl.find info_tbl e

    (** return whether `e` has been explored *)
    let explored (e : Exp.t) : bool = ExpTbl.mem info_tbl e

    (** visit the predecessor of e
    
    this will set the info of e to the correct value 
    and compute the `detected_liveness` of `e`.
    **this function assumes `e` is in the `info_of` table.** *)
    let rec visit_predecessor_of (e : Exp.t) (info_of_e : expInfo) : unit =
      let e_to_live_scc : bool ref = ref false in
      (* visit the predecessor `e'` of `e`.*)
      let visit_single_predecessor (e' : Exp.t) : unit =
        (* f hasn't been explored, then explore f *)
        if not @@ explored e' then (
          visit e';
          info_of_e.low_link <- min info_of_e.low_link (info_of e').low_link)
        else
          let info_of_e' = info_of e' in
          if info_of_e'.on_stack then
            (* if f has been explored, and on stack, then it is in the scc of e
               Thus we update the `low_link` of `e`*)
            info_of_e.low_link <- min info_of_e.low_link info_of_e'.low_link
          else
            (* if f explored but not on stack.
                This means that f is part of an explored scc.
               We will update the `e_to_live_scc` value *)
            e_to_live_scc :=
              !e_to_live_scc || ExpHSet.mem (rep info_of_e') live_scc
      in
      Hashcons.Hmap.iter
        (fun _bexp (e', _p) -> visit_single_predecessor e')
        (derivative e)

    and construct_scc_of e : unit =
      (* pop until `e` is reached, and output all the elements in a set *)
      let rec pop_until_e () : Exp.t_ HSet.t =
        let f = Stack.pop stack in
        let info_of_f = info_of f in
        info_of_f.on_stack <- false;
        if f == e then HSet.singleton f
        else
          let s = pop_until_e () in
          HSet.add f s
      in
      let popped = pop_until_e () in
      (* whether the scc is live *)
      let is_live =
        (* whether the scc has a transition to live *)
        HSet.exists (fun e -> ExpHSet.mem e to_live_scc) popped
        (* whether the scc has an accepting transition *)
        || HSet.exists (fun e -> not @@ BExp.is_false @@ epsilion e) popped
      in
      let info_of_e = info_of e in
      (* union all the popped expression into a *)
      if is_live then (
        (* for each element in popped,
           add it to the scc using union,
           and remove it from `to_live_scc` to save memory*)
        HSet.iter
          (fun f ->
            ignore @@ UnionFind.union (info_of f).elem info_of_e.elem;
            ExpHSet.remove f to_live_scc)
          popped;
        (* add the representative of `e` to `live_scc`*)
        ExpHSet.add (rep info_of_e) live_scc)
      else
        (* remove all the popped value from `to_live_scc` to save memory*)
        HSet.iter (fun f -> ExpHSet.remove f to_live_scc) popped

    (** Construct union find object that classifies the scc from `e`

    This function is based on Tarjan's SCC algorithm;
    it will iterate through all the reachable expressions from `e`,
    and should only be called when e has not been explored.
    *)
    and visit (e : Exp.t) : unit =
      (* init*)
      Stack.push e stack;
      let init_e_info =
        {
          idx = !cur_idx;
          elem = UnionFind.make e;
          low_link = !cur_idx;
          on_stack = true;
        }
      in
      ExpTbl.add info_tbl e init_e_info;
      cur_idx := !cur_idx + 1;

      (* visit all the reachable expressions recursively *)
      visit_predecessor_of e init_e_info;

      (* the computed info of e*)
      let info_of_e = info_of e in

      (* collect scc if all the scc is explored *)
      if info_of_e.low_link = info_of_e.idx then construct_scc_of e

    let is_live (e : Exp.t) : bool =
      match ExpTbl.find_opt info_tbl e with
      (* `e` has not been explored, visit `e` first.*)
      | None ->
          visit e;
          ExpHSet.mem (rep @@ info_of e) live_scc
      (* `e` has been explored *)
      | Some info_of_e -> ExpHSet.mem (rep info_of_e) live_scc
  end

end