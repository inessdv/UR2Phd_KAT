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

  (** Test if two boolean expressions is semantically equivelant. *)
  let equiv (b1 : t) (b2 : t) : bool =
    let solver = Z3.Solver.mk_solver z3_empty_ctx None in
    let iff_exp = Z3.Boolean.mk_iff z3_empty_ctx (to_z3 b1) (to_z3 b2) in
    let not_iff_exp = Z3.Boolean.mk_not z3_empty_ctx iff_exp in
    (* if ¬ (b1 ↔ b2) is unsatisfiable, then b1 ↔ b2 is a tautology,
       thus b1 and b2 are semantically equivalent.*)
    match Z3.Solver.check solver [ not_iff_exp ] with
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

  module HSet = Hashcons.Hset
  (** a fast immutable map for hashconsed key *)

  (** The epsilon of the expression,
      
  The boolean expression consists of all the atoms 
  that is accepted by the expression *)
  module ExpTbl = Hashtbl.Make (struct
    type t = Exp.t

    let hash (e : t) = e.hkey
    let equal e1 e2 = e1 == e2
  end)

  module ExpHSet = struct
    type t = unit ExpTbl.t

    let create : int -> t = ExpTbl.create
    let add (exp : Exp.t) (s : t) : unit = ExpTbl.add s exp ()
    let remove (exp : Exp.t) (s : t) : unit = ExpTbl.remove s exp

    let mem (exp : Exp.t) (s : t) : bool =
      Option.is_some @@ ExpTbl.find_opt s exp

    let add_to_fst (hset1 : t) (hset2 : Exp.t list) : unit =
      List.iter (fun exp -> add exp hset1) hset2
  end

  let rec epsilon (exp : Exp.t) : BExp.t =
    match exp.node with
    | Pact _ -> BExp.zero
    | Seq (e, f) -> BExp.b_and (epsilon e) (epsilon f)
    | If (be, e, f) ->
        BExp.b_or
          (BExp.b_and be (epsilon e))
          (BExp.b_and (BExp.b_not be) (epsilon f))
    | Test be -> be
    | While (be, _) -> BExp.b_not be

  (** The derivative of a expression: δ ∈ exp -> (BExp ↛ exp × Σ)
  This uses the map representation of the derivative for the ease of implementation,
  and primitive action is encoded as a string *)

  let combine_BE_with_a (be : BExp.t) (m : (BExp.t * (Exp.t * string)) list) :
  (BExp.t * (Exp.t * string)) list =
   List.map (fun (a, b) -> (BExp.b_and a be, b)) m

  let while_helper (be : BExp.t) (exp : Exp.t)
      (m : (BExp.t * (Exp.t * string)) list) : (BExp.t * (Exp.t * string)) list
      =
      List.map
        (fun (a, (e', p)) ->
          (BExp.b_and a be, (Exp.seq e' (Exp.while_do be exp), p))) m

  let sequence_helper_without_epsilon (exp2 : Exp.t)
      (m : (BExp.t * (Exp.t * string)) list) : (BExp.t * (Exp.t * string)) list
      =
      List.map (fun (b, (e', p)) -> (b, (Exp.seq e' exp2, p))) m

  let sequence_helper_with_epsilon (eps : BExp.t)
      (m : (BExp.t * (Exp.t * string)) list) : (BExp.t * (Exp.t * string)) list
      =
      List.map (fun (b, pair) -> (BExp.b_and b eps, pair)) m

  let rec derivative (exp : Exp.t) : (BExp.t * (Exp.t * string)) list =
    match exp.node with
    | Test _ -> []
    | Pact p -> [BExp.one,( Exp.test(BExp.one) , p)]
    | If (be, exp1, exp2) ->
        (** get rid of repetitions**)
        (combine_BE_with_a be (derivative exp1)) @
        (combine_BE_with_a be (derivative exp2))
    | Seq (e, f) ->
        let eps_of_e = epsilon e in
        let derivative_of_exp1 = derivative e in
        let derivative_of_exp2 = derivative f in
        (sequence_helper_without_epsilon f derivative_of_exp1) @
        (sequence_helper_with_epsilon eps_of_e derivative_of_exp2)
    | While (be, e) ->
        let derive_e = derivative e in
        while_helper be e derive_e

  (* let rec dfs_for_check_dead(exp:Exp.t):(Exp.t_)HSet.t=
      match exp.node with
      | Test _ -> HSet.empty
      | _ ->
      let explored= HSet.singleton exp in
      let deriv = Hmap.bindings (derivative exp) in
      List.fold_left (fun (acc)(_,(exp',_))-> HSet.union (dfs_for_check_dead exp') (acc)) explored deriv *)

  (* let explored : ExpHSet.t=ExpHSet.create 251 *)

  let rec check_dead_many (explored : Exp.t_ HSet.t) (exps : Exp.t list) :
      Exp.t_ HSet.t option =
    match exps with
    | [] -> Some explored
    | x1 :: xs -> (
        match check_dead explored x1 with
        | None -> None
        | Some states -> check_dead_many (HSet.union explored states) xs)

  and check_dead (explored : Exp.t_ HSet.t) (exp : Exp.t) : Exp.t_ HSet.t option
      =
    if HSet.mem exp explored then Some explored
    else
      let explored = HSet.add exp explored in
      if BExp.is_false @@ epsilon exp then
        let deriv = derivative exp in
        let next_exps = List.map (fun (_, (exp, _)) -> exp) deriv in
        check_dead_many explored next_exps
      else None

  let dead_states : ExpHSet.t = ExpHSet.create 251 (* what size??*)

  let is_dead (exp : Exp.t) : bool =
    if ExpHSet.mem exp dead_states then true
    else
      match check_dead HSet.empty exp with
      (* | Some(s)-> let dead_states = ExpHSet.add s  *)
      | Some s ->
          let exp_list = HSet.elements s in
          ExpHSet.add_to_fst dead_states exp_list;
          true
      | None -> false

  let hash_table = ExpTbl.create 251

  (** Add expression to hash table if it has not yet been added **)
  let exp_ele (exp : Exp.t) : Exp.t UnionFind.elem =
    match ExpTbl.find_opt hash_table exp with
    | Some exp_ele -> exp_ele
    | None ->
        let exp_ele = UnionFind.make exp in
        ExpTbl.add hash_table exp exp_ele;
        exp_ele

let product (psi_e:(BExp.t_ Hashcons.hash_consed * (Exp.t * string)) list) (psi_f:(BExp.t_ Hashcons.hash_consed * (Exp.t * string)) list): ((BExp.t_ Hashcons.hash_consed * (Exp.t * string)) * (BExp.t_ Hashcons.hash_consed * (Exp.t * string))) list =
  List.rev
    (List.fold_left
       (fun x a -> List.fold_left (fun y b -> (a, b) :: y) x psi_f)
       [] psi_e)
       
  (** p(e) fucntion ρ(e) = ¬ ϵ(e) ∧ ¬ (⋁_{ψ ↦ (e', p) ∈ δ(e)} ψ)**)
  let rec reject (exp : Exp.t) : BExp.t =
    let exp_derivatives = derivative exp in
    let epsilon = epsilon exp in
    let transitions = List.fold_left (fun acc (be,(_,_)) -> BExp.b_or acc be ) BExp.zero exp_derivatives in
      BExp.b_and (BExp.b_not epsilon) (BExp.b_not transitions)


  (**cshould we call reject beforehand? if so:
      let rec equiv_helper (exp1 : Exp.t) (exp2 : Exp.t) : bool =
        let r1 = reject exp1 in
        let r2 = reject exp2 in
        equiv exp1 exp2 r1 r2
        (change input of equiv to include r1 and r2)
        **)
  let rec equiv (exp1 : Exp.t) (exp2 : Exp.t) : bool =
          let exp1_ele = exp_ele exp1 in
          let exp2_ele = exp_ele exp2 in
      
          (** Check if the expressions have already been marked as equiv **)
          if UnionFind.eq exp1_ele exp2_ele then true else
      
          (** if both are dead, then they are equivalent **)
          if ExpHSet.mem exp1 dead_states then is_dead exp2 else
          if ExpHSet.mem exp2 dead_states then is_dead exp1 else
          
          (**  assert ϵ(e) = ϵ(f)   assert and try catch  design custom exception **)
            if not (BExp.equiv (epsilon exp1) (epsilon exp2)) then false else
              let reject_atoms_of_exp1 = reject exp1 in 
              let reject_atoms_of_exp2 = reject exp2 in 
              let f_derivatives = derivative exp2 in
              let e_derivatives = derivative exp1 in
              (**ASSERT**)
              List.for_all (fun(be,(exp,_))-> 
                is_dead exp  || BExp.is_false (BExp.b_and reject_atoms_of_exp1 be))  f_derivatives
              &&
              List.for_all (fun(be,(exp,_))-> 
                is_dead exp  || BExp.is_false (BExp.b_and reject_atoms_of_exp2 be))  e_derivatives
              &&
              
              let cross_product = product e_derivatives f_derivatives in 
              let rec check_disjoint (cross_product: 
                ((BExp.t_ Hashcons.hash_consed * (Exp.t * string))
                * (BExp.t_ Hashcons.hash_consed * (Exp.t * string)))
                list): bool =
              match cross_product with
              | [] -> true
              | ((be1,(next_exp1,p)),(be2,(next_exp2,q)))::xs -> BExp.is_false (BExp.b_and be1 be2) ||
                if p == q then (ignore @@UnionFind.union exp1_ele exp2_ele;
                if equiv next_exp1 next_exp2 then check_disjoint xs else false)
              else 
                (if (is_dead(next_exp1) && is_dead(next_exp2)) then check_disjoint xs else false) in
               check_disjoint cross_product
              
      end