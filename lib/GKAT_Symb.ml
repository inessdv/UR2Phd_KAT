module BExp = struct
  (** Module for working with boolean expressions *)
  type t_node = t_  (*check t_ type*)
  
  and t = t_node Hashcons.hash_consed
  (** The type for a hashconsed boolean expression *)

  (* The internal type of the boolean expression*)
  and t_ =
    | Zero
    | One
    | PBool of int
    | Or of t * t
    | And of t * t
    | Not of t

  module T_node = struct
    type t = t_node

    let equal (t1) (t2) =
      match (t1, t2) with
      | Zero, Zero -> true
      | One, One -> true
      | PBool i, PBool j -> i == j
      | Or (x1, y1), Or (x2, y2) -> x1 == x2 && y1 == y2
      | And (x1, y1), And (x2, y2) -> x1 == x2 && y1 == y2
      | Not x1, Not x2 -> x1 == x2
      | _ -> false

    let hash (t) =
      match t with
      | Zero -> Hashtbl.hash `Zero
      | One -> Hashtbl.hash `One
      | PBool i -> Hashtbl.hash (`PBool i)
      | Or (x, y) -> Hashtbl.hash (`Or (x.hkey, y.hkey))
      | And (x, y) -> Hashtbl.hash (`And (x.hkey, y.hkey))
      | Not x -> Hashtbl.hash (`Not x.hkey)
  end

  module HashT = Hashcons.Make(T_node)
  (*** table used for hash consing 
    notice because of hash consing, we can build ***)
  let tbl = HashT.create 251

  (*let empty_ctx = S.mk_context*)
  let hashcons = HashT.hashcons tbl
  let zero : t = hashcons @@ Zero
  let one : t = hashcons @@ One

  let pBool (num : int) : t =
    hashcons @@ PBool (Hashtbl.hash num)

  let b_not (b1 : t) : t =
    if b1 == one then zero
    else if b1 == zero then one
    else hashcons @@ Not b1
      (*let _, b1_ = b1.node in
      hashcons @@ (Not b1, S.mk_not empty_ctx b1_)*)

  let b_or (b1 : t) (b2 : t) : t =
    if b1 == one then one
    else if b2 == one then one
    else if b1 == zero then b2
    else if b2 == zero then b1
    else if b1 == b2 then b1
    else if b1 == b_not b2 then one
    else hashcons @@ Or(b1, b2)
      (*let _, b1_ = b1.node in
      let _, b2_ = b2.node in
      hashcons @@ (Or (b1, b2), S.mk_or empty_ctx b1_ b2_)*)
      (*hashcons @@ (Or (b1, b2), MLBDD.dor b1_ b2_)*)


  let b_and (b1 : t) (b2 : t) : t =
    if b1 == one then b2
    else if b2 == one then b1
    else if b1 == zero then zero
    else if b2 == zero then zero
    else if b1 == b2 then b1
    else if b1 == b_not b2 then zero
    else
      hashcons @@ And (b1, b2)
    
      let rec pprint_bexp_with_p (bexp : t_) =
        match bexp with
        | Zero -> ("0", 0)
        | One -> ("1", 0)
        | PBool b -> ("b"^(string_of_int b), 0)
        | Or (b1, b2) ->
          let str1, prec1 = pprint_bexp_with_p b1.node in
          let str2, prec2 = pprint_bexp_with_p b2.node in
          let str1' = if prec1 > 2 then "(" ^ str1 ^ ")" else str1 in
          let str2' = if prec2 > 2 then "(" ^ str2 ^ ")" else str2 in
          (str1' ^ " or " ^ str2', 3)
        | And (b1, b2) ->
          let str1, prec1 = pprint_bexp_with_p b1.node in
          let str2, prec2 = pprint_bexp_with_p b2.node in
          let str1' = if prec1 > 2 then "(" ^ str1 ^ ")" else str1 in
          let str2' = if prec2 > 2 then "(" ^ str2 ^ ")" else str2 in
          (str1' ^ " and " ^ str2', 3)
        | Not b ->
          let str, prec = pprint_bexp_with_p b.node in
    
          if prec > 0 then ("~(" ^ str ^ ")", 1) else ("~" ^ str, 1)
        
        (* Print bexp without precedence number *)
        let pprint (bexp : t_) =
        let str, _ = pprint_bexp_with_p bexp in
        str

end


module Exp = struct

  type t = t_ Hashcons.hash_consed
  (** hashconsed GKAT expression*)

  and t_ =
    | Pact of string * int
    | Seq of t * t
    | If of BExp.t * t * t
    | Test of BExp.t
    | While of BExp.t * t

  module T_node = struct
    type t = t_

    let equal t1 t2 =
      match (t1, t2) with
      | Pact (_, i), Pact (_, j) -> i == j
      | Seq (x1, y1), Seq (x2, y2) -> x1 == x2 && y1 == y2
      | If (b1, x1, y1), If (b2, x2, y2) -> b1 == b2 && x1 == x2 && y1 == y2
      | Test b1, Test b2 -> b1 == b2
      | While (b1, t1), While (b2, t2) -> b1 == b2 && t1 == t2
      | _ -> false

    let hash t =
      match t with
      | Pact (_, i) -> Hashtbl.hash (`Pact i)
      | Seq (x, y) -> Hashtbl.hash (`Seq (x.hkey, y.hkey))
      | If (b, x, y) -> Hashtbl.hash (`If (b.hkey, x.hkey, y.hkey))
      | Test b -> Hashtbl.hash (`Text b.hkey)
      | While (b, x) -> Hashtbl.hash (`While (b.hkey, x.hkey))
  end

  module HashT = Hashcons.Make (T_node)

  (** table used for hash consing 
  notice because of hash consing, we can build *)
  let tbl = HashT.create 251

  let hashcons : t_ -> t = HashT.hashcons tbl
  let p_act (p : string) : t = hashcons @@ Pact (p, Hashtbl.hash p)
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
    else if f == fail then seq (test b) e
    else hashcons @@ If (b, e, f)

  let while_do (b :BExp.t) (e : t) : t = hashcons @@ While (b, e)
    (* if b == BExp.zero then skip
    else if b == BExp.one then fail
    else if e == skip || e == fail then test @@ BExp.b_not b 
    else  *)

    (** Return the number of primitive actions in the expression*)
    let rec num_pact (e : t) =
      match e.node with
      | Pact _ -> 1
      | Seq (e1, e2) -> num_pact e1 + num_pact e2
      | If (_, e1, e2) -> num_pact e1 + num_pact e2
      | Test _ -> 0
      | While (_, e1) -> num_pact e1
  
    (** Return the number of test expression in the expression*)
    let rec num_bexp (e : t) =
      match e.node with
      | Pact _ -> 0
      | Seq (e1, e2) -> num_bexp e1 + num_bexp e2
      | If (_, e1, e2) -> 1 + num_bexp e1 + num_bexp e2
      | Test _ -> 1
      | While (_, e1) -> 1 + num_bexp e1
  
    (** number of sequencing operation in the input expression *)
    let rec num_seq (e : t) =
      match e.node with
      | Pact _ -> 0
      | Seq (e1, e2) -> 1 + num_seq e1 + num_seq e2
      | If (_, e1, e2) -> num_seq e1 + num_seq e2
      | Test _ -> 0
      | While (_, e1) -> num_seq e1
  
    (** number of if statements in the input expression *)
    let rec num_if (e : t) =
      match e.node with
      | Pact _ -> 0
      | Seq (e1, e2) -> num_if e1 + num_if e2
      | If (_, e1, e2) -> 1 + num_if e1 + num_if e2
      | Test _ -> 0
      | While (_, e1) -> num_if e1
  
    (** number of while loop in the input expression *)
    let rec num_while (e : t) =
      match e.node with
      | Pact _ -> 0
      | Seq (e1, e2) -> num_while e1 + num_while e2
      | If (_, e1, e2) -> num_while e1 + num_while e2
      | Test _ -> 0
      | While (_, e1) -> 1 + num_while e1
  
    let pprint (exp : t) =
      let rec helper (exp : t) : string * int =
        match exp.node with
        | Pact (p, _) -> (p, 0)
        | Seq (e1, e2) ->
            let s1, p1 = helper e1 in
            let s2, p2 = helper e2 in
            let s1' = if p1 < 2 then s1 else "(" ^ s1 ^ ")" in
            let s2' = if p2 < 2 then s2 else "(" ^ s2 ^ ")" in
            (s1' ^ " ; " ^ s2', 2)
        | If (b, e1, e2) ->
            let bs = BExp.pprint b.node in
            let s1, p1 = helper e1 in
            let s2, p2 = helper e2 in
            let s1' = if p1 <= 3 then s1 else "(" ^ s1 ^ ")" in
            let s2' = if p2 < 3 then s2 else "(" ^ s2 ^ ")" in
            ("if " ^ bs ^ " then " ^ s1' ^ " else " ^ s2', 3)
        | Test b ->
            let bs = BExp.pprint b.node in
            (bs, 1)
        | While (b, e) ->
            let bs = BExp.pprint b.node in
            let s, p = helper e in
            let s' = if p <= 1 then s else "(" ^ s ^ ")" in
            ("while " ^ bs ^ " do " ^ s' ^ " done", 1)
      in
      fst @@ helper exp
end



(***** Solver functor *****)
module type Solver = sig
  (*functor for solvers*)
  val is_false: BExp.t_ -> bool
  val equiv: BExp.t_ -> BExp.t_ -> bool

end


module Z3_solver: Solver = struct

  let ctx = Z3.mk_context []
  let rec to_solver (b: BExp.t_): Z3.Expr.expr = 
    match b with
    | Zero -> Z3.Boolean.mk_false ctx
    | One -> Z3.Boolean.mk_true ctx
    | PBool b -> let s_num = string_of_int b in
        Z3.Boolean.mk_const_s ctx ("b"^s_num)
    | Or (b1,b2) -> Z3.Boolean.mk_or ctx [ (to_solver b1.node); (to_solver b2.node) ]
    | And (b1,b2) -> Z3.Boolean.mk_and ctx [ (to_solver b1.node); (to_solver b2.node) ]
    | Not b1 -> Z3.Boolean.mk_not ctx (to_solver b1.node)

  let is_false (b1: BExp.t_): bool =
    match Z3.Solver.check (Z3.Solver.mk_solver ctx None) [ to_solver b1] with
  | Z3.Solver.UNSATISFIABLE -> true
  | _ -> false

  let equiv (b1: BExp.t_) (b2: BExp.t_) : bool =
    let iff_exp = Z3.Boolean.mk_iff ctx (to_solver b1) (to_solver b2) in
    let not_iff_exp = Z3.Boolean.mk_not ctx iff_exp in 
    (* if ¬ (b1 ↔ b2) is unsatisfiable, then b1 ↔ b2 is a tautology,
      thus b1 and b2 are semantically equivalent.*)
    match Z3.Solver.check (Z3.Solver.mk_solver ctx None) [ not_iff_exp ] with
    | Z3.Solver.UNSATISFIABLE -> true
    | _ -> false

end

module Mlbdd_solver(): Solver = struct
  let ctx = MLBDD.init ()
  let rec to_solver (b: BExp.t_): MLBDD.t =
    match b with
    | Zero -> MLBDD.dfalse ctx
    | One -> MLBDD.dtrue ctx
    | PBool b1 -> MLBDD.ithvar ctx b1
    | Or (b1,b2) -> MLBDD.dor (to_solver b1.node) (to_solver b2.node)
    | And (b1,b2) -> MLBDD.dand (to_solver b1.node) (to_solver b2.node)
    | Not b1 -> MLBDD.dnot (to_solver b1.node)

  let is_false (b1: BExp.t_): bool =
    MLBDD.is_false (to_solver b1)

  let equiv (b1: BExp.t_) (b2: BExp.t_) : bool =
    MLBDD.equal (to_solver b1) (to_solver b2)
end


module Derivatives(S:Solver) = struct
  let b_is_false (b : BExp.t) : bool = S.is_false b.node
  let b_equiv (b1 : BExp.t) (b2 : BExp.t) : bool = S.equiv b1.node b2.node


  (** defines derivatives *)
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

    let add_to_fst (hset1 : t) (hset2 : Exp.t_ HSet.t) : unit =
      HSet.iter (fun exp -> add exp hset1) hset2

    let clear = ExpTbl.clear
    let length = ExpTbl.length
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

  let combine_BE_with_a (be : BExp.t) (m : (BExp.t * (Exp.t * int)) list) :
      (BExp.t * (Exp.t * int)) list =
    List.map (fun (a, b) -> (BExp.b_and a be, b)) m

  let while_helper (be : BExp.t) (exp : Exp.t)
      (m : (BExp.t * (Exp.t * int)) list) : (BExp.t * (Exp.t * int)) list =
    List.map
      (fun (a, (e', p)) ->
        (BExp.b_and a be, (Exp.seq e' (Exp.while_do be exp), p)))
      m

  let sequence_helper_without_epsilon (exp2 : Exp.t)
      (m : (BExp.t * (Exp.t * int)) list) : (BExp.t * (Exp.t * int)) list =
    List.map (fun (b, (e', p)) -> (b, (Exp.seq e' exp2, p))) m

  let sequence_helper_with_epsilon (eps : BExp.t)
      (m : (BExp.t * (Exp.t * int)) list) : (BExp.t * (Exp.t * int)) list =
    List.map (fun (b, pair) -> (BExp.b_and b eps, pair)) m

  let rec derivative (exp : Exp.t) : (BExp.t * (Exp.t * int)) list =
    match exp.node with
    | Test _ -> []
    | Pact (_, p) -> [ (BExp.one, (Exp.test BExp.one, p)) ]
    | If (be, exp1, exp2) ->
        (* get rid of repetitions--> do List.sort_uniq**)
        combine_BE_with_a be (derivative exp1)
        @ combine_BE_with_a (BExp.b_not be) (derivative exp2)
    | Seq (e, f) ->
        let eps_of_e = epsilon e in
        let derivative_of_exp1 = derivative e in
        let derivative_of_exp2 = derivative f in
        sequence_helper_without_epsilon f derivative_of_exp1
        @ sequence_helper_with_epsilon eps_of_e derivative_of_exp2
    | While (be, e) ->
        let derive_e = derivative e in
        while_helper be e derive_e

  let pprint_deriv (deriv : (BExp.t_ * (Exp.t * int)) list) =
    String.concat "\n"
    @@ List.map
         (fun (bexp, (der, p_act)) ->
          BExp.pprint bexp ^ " -> " ^ Exp.pprint der ^ ", "
           ^ string_of_int p_act)
         deriv

  module DeadExps : sig
    val is_dead : Exp.t -> bool
    val known_dead : Exp.t -> bool
    val clear_dead : unit
    val length : int
  end = struct
    (** The module to encapsolate the logic to check dead*)

    (** states (expressions) that are known to be dead
  
    its size 251 is a magic number, as a place holder*)
    let dead_states : ExpHSet.t = ExpHSet.create 251

    (** Detect whether an expression is *known* to be dead.
    
    A fast alternative to `is_dead`, 
    when it returns `false`, the expression is not necessarily live.*)
    let known_dead exp = ExpHSet.mem exp dead_states

    let clear_dead = ExpHSet.clear dead_states
    let length = ExpHSet.length dead_states

    type visitRes =
      | KnownDead
          (** the visited expression is *known* to be dead, i.e. in `dead_states`*)
      | Live
          (** the visited node is live, i.e. accepting state is found in the visit *)
      | Unknown of Exp.t_ HSet.t
          (** the visited node is unknown to be dead or live, 
          the arugument is all the explored expressions while visiting that node*)

    (** helper to `visit`, visit all the decedents of an expression, return a visit result
  
    - return `Live` if any of them is returning live, 
    - return `Dead` if all of them are returning dead, 
    - return `Unknown` otherwise *)
    let rec visit_decedents (explored : Exp.t_ HSet.t) (exps : Exp.t list) :
        visitRes =
      match exps with
      | [] -> Unknown explored
      | x1 :: xs -> (
          match visit explored x1 with
          | Live -> Live
          | KnownDead -> visit_decedents (HSet.add x1 explored) xs
          | Unknown states -> visit_decedents (HSet.union explored states) xs)

    (** visit a single expression, *)
    and visit (explored : Exp.t_ HSet.t) (exp : Exp.t) : visitRes =
      (* print_endline ("visiting "^Exp.pprint exp); *)
      if known_dead exp then KnownDead
      else if HSet.mem exp explored then Unknown explored
      else
        (* explore the current *)
        let explored = HSet.add exp explored in
        if b_is_false @@ epsilon exp then
          (* expression is not accepting*)
          let deriv = derivative exp in
          (* computing the next step, notice we need to filter out the unreachable expression,
             where the symbolic derivative `b_exp` is false *)
          let next_exps =
            List.filter_map
              (fun (b_exp, (exp, _)) ->
                if b_is_false b_exp then None else Some exp)
              deriv
          in
          visit_decedents explored next_exps
        else (* expression is accepting*)
          Live

    (** Check whether an expression is dead.
    
    When it returns false, the expression is necessarily live.*)
    let is_dead (exp : Exp.t) : bool =
      (* print_endline ("checking whether exp "^Exp.pprint exp^" is dead");  *)
      match visit HSet.empty exp with
      (* if it is unknown wether it is dead
         after exploring all of its reachable state,
         then it cannot reach any accepting states,
         hence the state `s` is dead*)
      | Unknown all_explored ->
          (* print_endline ("final result, unknown, hence dead"); *)
          ExpHSet.add_to_fst dead_states all_explored;
          true
      | Live ->
          (* print_endline "final result, live";  *)
          false
      | KnownDead ->
          (* print_endline "final result, known dead";  *)
          true
  end

  (** A table that maps the the expression to its union find element *)
  let union_find_tbl = ExpTbl.create 251

  (** Add expression to hash table if it has not yet been added **)
  let exp_ele (exp : Exp.t) : Exp.t UnionFind.elem =
    match ExpTbl.find_opt union_find_tbl exp with
    | Some exp_ele -> exp_ele
    | None ->
        let exp_ele = UnionFind.make exp in
        ExpTbl.add union_find_tbl exp exp_ele;
        exp_ele

  let print_tuple tup =
    let s, i = tup in
    Printf.printf "(%s, %d)\n" s i

  (** get the reject expression 
  
  logically, the expression can be written as follows: 
  ¬ ϵ(e) ∧ ¬ (⋁_{ψ ↦ (e', p) ∈ δ(e)} ψ) *)
  let reject (exp : Exp.t) : BExp.t =
    let exp_derivatives = derivative exp in
    let epsilon = epsilon exp in
    let transitions =
      List.fold_left
        (fun acc (be, (_, _)) -> BExp.b_or acc be)
        BExp.zero exp_derivatives
    in
    (*print_endline ("Checking reject for ");
      print_string (Print2.pprint (dehashcons_gkat exp));
      print_newline ();
      print_tuple (Print2.pprint_bexp (dehashcons_bexp epsilon));
      print_newline ();*)
    let result = BExp.b_and (BExp.b_not epsilon) (BExp.b_not transitions) in
    (*let result_dehash = dehashcons_bexp result in
      print_tuple (Print2.pprint_bexp  result_dehash);*)
    result

  let rec equiv_helper (exp1 : Exp.t) (exp2 : Exp.t) : bool =
    let reject1 = reject exp1 in
    let reject2 = reject exp2 in

    (* print_newline ();
       print_endline ("Exp 1: " ^ Exp.pprint exp1);
       print_endline ("Exp 2: " ^ Exp.pprint exp2); *)
    let exp1_ele = exp_ele exp1 in
    let exp2_ele = exp_ele exp2 in

    (* Check if the expressions have already been marked as equiv **)
    if UnionFind.eq exp1_ele exp2_ele then true
    else if
      (* if both are dead, then they are equivalent **)
      DeadExps.known_dead exp1
    then (* print_endline ("exp1 is dead"); *)
      DeadExps.is_dead exp2
    else if DeadExps.known_dead exp2 then
      (* print_endline ("exp2 is dead");
         print_endline ("is exp1 dead?" ^ string_of_bool @@ DeadExps.is_dead exp1); *)
      DeadExps.is_dead exp1
    else
      (*  Logical connection here instead of if **)
      (*USE SOLVER IN EQUIV*)
      let epsilon_assert = b_equiv (epsilon exp1) (epsilon exp2) in
      (* print_endline "Checking same espilon: ";
         print_endline (string_of_bool epsilon_assert); *)
      epsilon_assert
      &&
      let e_derivatives = derivative exp1 in
      let f_derivatives = derivative exp2 in

      (* print_endline "exp1 deriv";
         print_endline @@ pprint_deriv e_derivatives;
         print_endline "exp2 deriv";
         print_endline @@ pprint_deriv f_derivatives; *)
      (let assert_rej1 =
         List.for_all
           (fun (be, (exp, _)) ->
             (b_is_false @@ BExp.b_and reject1 be) || DeadExps.is_dead exp)
           f_derivatives
       in
       (* print_endline ("Exp 1: " ^ Exp.pprint exp1);
          print_endline ("Exp 2: " ^ Exp.pprint exp2);
          print_endline "comparing the transition of exp2 to rejection of exp1: ";
          print_endline
            "forall ψ_f ↦ (f', q) ∈ δ(f), ( ρ(e) ∧ ψ_f = 0 || is_dead(f'))";
          print_endline (string_of_bool assert_rej1); *)
       assert_rej1)
      && (let assert_rej2 =
            List.for_all
              (fun (be, (exp, _)) ->
                (b_is_false @@ BExp.b_and reject2 be) || DeadExps.is_dead exp)
              e_derivatives
          in
          (* print_endline ("Exp 1: " ^ Exp.pprint exp1);
             print_endline ("Exp 2: " ^ Exp.pprint exp2);
             print_endline
               "comparing the transition of exp2 to rejection of exp1: ";
             print_endline
               "assertion2 for: forall ψ_e ↦ (e', q) ∈ δ(f), ( ρ(f) ∧ ψ_f = 0 || \
                is_dead(e')) ";
             print_endline (string_of_bool assert_rej2); *)
          assert_rej2)
      &&
      let assert_trans =
        List.for_all
          (fun ((be1, (next_exp1, p)), (be2, (next_exp2, q))) ->
            (* `be1` `be2` disjoint, then skip*)
            (b_is_false @@ BExp.b_and be1 be2)
            ||
            (* `p` and `q` are the same, then recurse*)
            if p = q then (
              ignore @@ UnionFind.union exp1_ele exp2_ele;
              equiv_helper next_exp1 next_exp2
              (* `p` and `q` are not the same, then both need to be dead*))
            else DeadExps.is_dead next_exp1 && DeadExps.is_dead next_exp2)
          (Common.list_prod e_derivatives f_derivatives)
      in
      (* print_endline ("Exp 1: " ^ Exp.pprint exp1);
         print_endline ("Exp 2: " ^ Exp.pprint exp2);
         print_endline
           "assertion3 for: forall ψ_e ↦ (e', p) ∈ δ(e), ψ_f ↦ (f', q) ∈ δ(f) ";
         print_endline (string_of_bool assert_trans); *)
      assert_trans

  let equiv (exp1 : Exp.t) (exp2 : Exp.t) : bool =
    let equiv = equiv_helper exp1 exp2 in
    (* clean the union-find table,
       as they can incorrectly link unequal expression when equiv_res if false*)
    if not equiv then ExpTbl.clear union_find_tbl;
    equiv

  (*let rec equiv (exp1 : S_Exp.t) (exp2 : S_Exp.t) : bool =
    let reject1 = reject exp1 in
    let reject2 = reject exp2 in
      equiv_helper exp1 exp2 reject1 reject2 *)

  (**Testing purposes**)
  (*b1 * (p0 * (if b2 then p0 else p0))*)
  (*
       let from_hash_to_GKAT(exp: (BS_Exp.t * (S_Exp.t * string)) list):(bExp * (gkat * string)) list =
        List.map(fun (be,(next_exp,p))->(dehashcons_bexp be,(dehashcons_gkat next_exp,p))) exp

       let from_product_to_GKAT(exp)= List.map(fun ((be1,(next_exp1,p)),(be2,(next_exp2,q))) ->
         (dehashcons_bexp be1,(dehashcons_gkat next_exp1,p)),(dehashcons_bexp be2,(dehashcons_gkat next_exp2,q))) (exp) *)

  let example1 =
    Exp.seq
      (Exp.test (BExp.pBool 1))
      (Exp.seq (Exp.p_act "p0")
         (Exp.if_then_else (BExp.pBool 2) (Exp.p_act "p0") (Exp.p_act "p0")))

  (*(b1 * p0) * p0*)
  let example2 =
    Exp.seq
      (Exp.seq (Exp.test (BExp.pBool 1)) (Exp.p_act "p0"))
      (Exp.p_act "p0")

  let example3 =
    Exp.seq (Exp.p_act "p0")
      (Exp.if_then_else (BExp.pBool 2) (Exp.p_act "p0") (Exp.p_act "p0"))

  let example5 =
    Exp.if_then_else (BExp.pBool 2) (Exp.p_act "p0") (Exp.p_act "p0")

  let example4 = Exp.test (BExp.pBool 1)

  let second_example1 =
    Exp.if_then_else (BExp.pBool 2) (Exp.p_act "p0") (Exp.p_act "p0")

  let second_example2 = Exp.p_act "p0"

  (*b1 * (p0 * (if b2 then p0 else p0))*)
  let third1 =
    Exp.seq
      (Exp.test (BExp.pBool 1))
      (Exp.seq (Exp.p_act "p0")
         (Exp.if_then_else (BExp.pBool 2) (Exp.p_act "p0") (Exp.p_act "p0")))

  (* (b1 * p0) * p0 *)
  let third2 =
    Exp.seq
      (Exp.seq (Exp.test (BExp.pBool 1)) (Exp.p_act "p0"))
      (Exp.p_act "p0")

  let third3 =
    Exp.seq
      (Exp.seq (Exp.p_act "p0") (Exp.test (BExp.pBool 1)))
      (Exp.p_act "p0")


let gkat_exampl1 =
  Exp.while_do
    (BExp.b_or (BExp.pBool 1) (BExp.b_or (BExp.pBool 1) (BExp.pBool 2)))
    (Exp.if_then_else (BExp.pBool 1)
       (Exp.test (BExp.pBool 1))
       (Exp.test (BExp.pBool 1)))
let gkat_example2 =
  Exp.while_do
    (BExp.b_or (BExp.b_or (BExp.pBool 1) (BExp.pBool 1)) (BExp.pBool 2))
    (Exp.seq (Exp.test (BExp.pBool 1)) (Exp.test (BExp.pBool 1)))
end

