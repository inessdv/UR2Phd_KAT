open GKAT_2

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

  (*Function to convert hashtype to bExp*)
  let rec dehashcons (hc_bexp : t) : bExp =
    match hc_bexp.node with
    | Zero -> Zero
    | One -> One
    | PBool be ->  PBool be
    | Or (be1,be2) -> Or (dehashcons be1, dehashcons be2)
    | And (be1,be2) -> And (dehashcons be1, dehashcons be2)
    | Not be -> Not (dehashcons be)

  let pprint e = GKAT_2.Print2.pprint_bexp @@ dehashcons e
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
    else if f == fail then seq (test b) e
    else hashcons @@ If (b, e, f)

  let while_do (b : BExp.t) (e : t) : t = hashcons @@ While (b, e)

  (*Function to convert hashtype to gkat*)
  let rec dehashcons (hc_exp : t): gkat =
    match hc_exp.node with
    | Pact p -> Pact p
    | Seq (e, f) ->  Seq (dehashcons e, dehashcons f)
    | If (be, e, f) -> If (BExp.dehashcons be, dehashcons e, dehashcons f)
    | Test be -> Test (BExp.dehashcons be)
    | While (be, e) -> While (BExp.dehashcons be, dehashcons e)

  let pprint e = GKAT_2.Print2.pprint @@ dehashcons e
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
        (** get rid of repetitions--> do List.sort_uniq**)
        (combine_BE_with_a be (derivative exp1)) @
        (combine_BE_with_a (BExp.b_not be) (derivative exp2))
    | Seq (e, f) ->
        let eps_of_e = epsilon e in
        let derivative_of_exp1 = derivative e in
        let derivative_of_exp2 = derivative f in
        (sequence_helper_without_epsilon f derivative_of_exp1) @
        (sequence_helper_with_epsilon eps_of_e derivative_of_exp2)
    | While (be, e) ->
        let derive_e = derivative e in
        while_helper be e derive_e

  module DeadExps: sig
    val is_dead: Exp.t -> bool  
    val known_dead: Exp.t -> bool
  end= struct
  (** The module to encapsolate the logic to check dead*)

  (** states (expressions) that are known to be dead
  
  its size 251 is a magic number, as a place holder*)
  let dead_states : ExpHSet.t = ExpHSet.create 251 
  

  (** Detect whether an expression is *known* to be dead.
    
  A fast alternative to `is_dead`, 
  when it returns `false`, the expression is not necessarily live.*)
  let known_dead (exp) = ExpHSet.mem exp dead_states


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
  let rec visit_decedents (explored : Exp.t_ HSet.t) (exps : Exp.t list) : visitRes =
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
      if known_dead exp then KnownDead else 
      if HSet.mem exp explored then Unknown explored else
      (* explore the current *)
      let explored = HSet.add exp explored in
      if BExp.is_false @@ epsilon exp then
        (* expression is not accepting*)
        let deriv = derivative exp in
        (* computing the next step, notice we need to filter out the unreachable expression,
        where the symbolic derivative `b_exp` is false *)
        let next_exps = List.filter_map 
          (fun (b_exp, (exp, _)) -> if BExp.is_false b_exp then None else Some exp) 
          deriv 
        in
        visit_decedents explored next_exps
      else 
        (* expression is accepting*)
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
      | Unknown s ->
          (* print_endline ("final result, unknown, hence dead"); *)
          let exp_list = HSet.elements s in
          ExpHSet.add_to_fst dead_states exp_list;
          true
      | Live -> 
        (* print_endline "final result, live";  *)
        false
      | KnownDead -> 
        (* print_endline "final result, known dead";  *)
        true
  end

  
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

  let print_tuple tup =
    let (s, i) = tup in
    Printf.printf "(%s, %d)\n" s i;;

  (** p(e) fucntion ρ(e) = ¬ ϵ(e) ∧ ¬ (⋁_{ψ ↦ (e', p) ∈ δ(e)} ψ)**)

  let reject (exp : Exp.t) : BExp.t =
    let exp_derivatives = derivative exp in
    let epsilon = epsilon exp in
    let transitions = List.fold_left (fun acc (be,(_,_)) -> BExp.b_or acc be ) BExp.zero exp_derivatives in
    (*print_endline ("Checking reject for ");
    print_string (Print2.pprint (dehashcons_gkat exp));
    print_newline ();
    print_tuple (Print2.pprint_bexp (dehashcons_bexp epsilon));
    print_newline ();*)
    let result = (BExp.b_and (BExp.b_not epsilon) (BExp.b_not transitions)) in
    (*let result_dehash = dehashcons_bexp result in
    print_tuple (Print2.pprint_bexp  result_dehash);*)
    result

  let rec equiv_helper (exp1 : Exp.t) (exp2 : Exp.t) : bool =
    let reject1 = reject exp1 in
    let reject2 = reject exp2 in

    (* print_endline ( "Exp 1: " ^Exp.pprint exp1);
    print_endline ( "Exp 2: " ^Exp.pprint exp2); *)

    let exp1_ele = exp_ele exp1 in
    let exp2_ele = exp_ele exp2 in

    (** Check if the expressions have already been marked as equiv **)
    if UnionFind.eq exp1_ele exp2_ele then true else

    (** if both are dead, then they are equivalent **)
    if DeadExps.known_dead exp1 then (
      (* print_endline ("exp1 is dead"); *)
      DeadExps.is_dead exp2) else
    if DeadExps.known_dead exp2 then (
      (* print_endline ("exp2 is dead");
      print_endline ("is exp1 dead?" ^ string_of_bool @@ DeadExps.is_dead exp1);   *)
      DeadExps.is_dead exp1) else

    (**  Logical connection here instead of if **)
      let epsilon_assert = (BExp.equiv (epsilon exp1) (epsilon exp2)) in
      (* print_endline ("Checking same espilon: ");
      print_endline (string_of_bool epsilon_assert); *)
      epsilon_assert &&

        let f_derivatives = derivative exp2 in
        let e_derivatives = derivative exp1 in

        (let assert1 = List.for_all (fun(be,(exp,_)) -> 
          BExp.is_false (BExp.b_and reject1 be) || DeadExps.is_dead exp)  f_derivatives
        in
        (* print_endline ( "Exp 1: " ^Exp.pprint exp1);
        print_endline ( "Exp 2: " ^Exp.pprint exp2);
        print_endline ("assertion1 for: forall ψ_f ↦ (f', q) ∈ δ(f), ( ρ(e) ∧ ψ_f = 0 || is_dead(f')) ");
        print_endline (string_of_bool assert1); *)
        assert1 )

        &&
        (let assert2 = (List.for_all (fun(be,(exp,_))-> 
          BExp.is_false (BExp.b_and reject2 be) || DeadExps.is_dead exp )  e_derivatives) 
        in
        (* print_endline ( "Exp 1: " ^Exp.pprint exp1);
        print_endline ( "Exp 2: " ^Exp.pprint exp2);
        print_endline ("assertion2 for: forall ψ_e ↦ (e', q) ∈ δ(f), ( ρ(f) ∧ ψ_f = 0 || is_dead(e')) ");
        print_endline (string_of_bool assert2);               *)
        assert2)
        &&
        
        (let assert3 = (
          List.for_all(fun ((be1,(next_exp1,p)),(be2,(next_exp2,q)))->
            (* `be1` `be2` disjoint, then skip*)
            BExp.is_false (BExp.b_and be1 be2) ||
            (* `p` and `q` are the same, then recurse*)
            if p = q then 
              (ignore @@UnionFind.union exp1_ele exp2_ele; 
              equiv_helper next_exp1 next_exp2) 
            (* `p` and `q` are not the same, then both need to be dead*)
            else 
              (DeadExps.is_dead next_exp1 && DeadExps.is_dead next_exp2)
          ) 
          (Common.list_prod e_derivatives f_derivatives)) 
        in
        (* print_endline ("Exp 1: " ^Exp.pprint exp1);
        print_endline ("Exp 2: " ^Exp.pprint exp2);
        print_endline ("assertion3 for: forall ψ_e ↦ (e', p) ∈ δ(e), ψ_f ↦ (f', q) ∈ δ(f) ") ;
        print_endline (string_of_bool assert3);  *)
        assert3)
  
  (*let rec equiv (exp1 : Exp.t) (exp2 : Exp.t) : bool =
    let reject1 = reject exp1 in
    let reject2 = reject exp2 in
      equiv_helper exp1 exp2 reject1 reject2 *)

  
  (**Testing purposes**)
      (*b1 * (p0 * (if b2 then p0 else p0))*)
(*     
    let from_hash_to_GKAT(exp: (BExp.t * (Exp.t * string)) list):(bExp * (gkat * string)) list =
     List.map(fun (be,(next_exp,p))->(dehashcons_bexp be,(dehashcons_gkat next_exp,p))) exp

    let from_product_to_GKAT(exp)= List.map(fun ((be1,(next_exp1,p)),(be2,(next_exp2,q))) ->
      (dehashcons_bexp be1,(dehashcons_gkat next_exp1,p)),(dehashcons_bexp be2,(dehashcons_gkat next_exp2,q))) (exp) *)

    let example1 = Exp.seq (Exp.test (BExp.pBool "b1") )
    (Exp.seq (Exp.p_act "p0")(Exp.if_then_else (BExp.pBool "b2")(Exp.p_act "p0")(Exp.p_act "p0")))
  
    (*(b1 * p0) * p0*)
    let example2 = Exp.seq (Exp.seq (Exp.test (BExp.pBool "b1"))(Exp.p_act "p0"))((Exp.p_act "p0"))

    let example3 = (Exp.seq (Exp.p_act "p0")(Exp.if_then_else (BExp.pBool "b2")(Exp.p_act "p0")(Exp.p_act "p0")))

    let example5 = Exp.if_then_else (BExp.pBool "b2")(Exp.p_act "p0")(Exp.p_act "p0")
    let example4 = Exp.test (BExp.pBool "b1")
  
    let second_example1=Exp.if_then_else (BExp.pBool "b2")(Exp.p_act "p0")(Exp.p_act "p0")
    let second_example2= Exp.p_act "p0"

    (*b1 * (p0 * (if b2 then p0 else p0))*)
    let third1 = Exp.seq (Exp.test (BExp.pBool "b1")) (Exp.seq (Exp.p_act "p0") (Exp.if_then_else (BExp.pBool "b2") (Exp.p_act "p0") (Exp.p_act "p0"))) 
    
    (* (b1 * p0) * p0 *)
    let third2 = Exp.seq (Exp.seq (Exp.test (BExp.pBool "b1")) (Exp.p_act "p0")) (Exp.p_act "p0")
    let third3=   Exp.seq (Exp.seq (Exp.p_act "p0") (Exp.test (BExp.pBool "b1"))) (Exp.p_act "p0")
    
    (*
    let debug (exp1 : gkat): bool =
      let e1 = from_GKAT_to_KAT exp1 in
      
      (** checking if conversion is correct**)
      print_string "GKAT expression! = ";
      print_string (Print2.pprint exp1);
      print_endline "KAT expression! = ";
      print_string (Print2.pprint e1);
      
      let e2 = from_GKAT_to_KAT exp2 in
      print_string "GKAT expression! = ";
      print_string (Print2.pprint exp2);
      print_endline "KAT expression! = ";
      print_string (pprint e2);
      equiv e1 e2
*)
  end


(* let rec equiv_helper (exp1 : Exp.t) (exp2 : Exp.t) (reject1: BExp.t) (reject2: BExp.t) : bool =
          let exp1_ele = exp_ele exp1 in
          let exp2_ele = exp_ele exp2 in
      
          (** Check if the expressions have already been marked as equiv **)
          if UnionFind.eq exp1_ele exp2_ele then true else
      
          (** if both are dead, then they are equivalent **)
          if ExpHSet.mem exp1 dead_states then is_dead exp2 else
          if ExpHSet.mem exp2 dead_states then is_dead exp1 else
  
          (**  Logical connection here instead of if **)
            (BExp.equiv (epsilon exp1) (epsilon exp2)) &&

              let f_derivatives = derivative exp2 in
              let e_derivatives = derivative exp1 in
              
              List.for_all (fun(be,(exp,_))-> 
                is_dead exp  || BExp.is_false (BExp.b_and reject1 be))  f_derivatives
              &&
              List.for_all (fun(be,(exp,_))-> 
                is_dead exp  || BExp.is_false (BExp.b_and reject2 be))  e_derivatives
              &&

              List.for_all(fun ((be1,(next_exp1,p)),(be2,(next_exp2,q)))->
                BExp.is_false (BExp.b_and be1 be2) ||
                if p = q then (ignore @@UnionFind.union exp1_ele exp2_ele;
                if equiv_helper next_exp1 next_exp2 reject1 reject2 then true else false)
              else 
                (if (is_dead(next_exp1) && is_dead(next_exp2)) then true else false)) (product e_derivatives f_derivatives)
  let rec equiv (exp1 : Exp.t) (exp2 : Exp.t) : bool =
    let reject1 = reject exp1 in
    let reject2 = reject exp2 in
      equiv_helper exp1 exp2 reject1 reject2
*)