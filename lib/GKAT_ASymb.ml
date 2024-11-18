open Common
open PointedCoprod
module PActSet = Set.Make (String)

module BExp = struct
  type t_node = t_ * Z3.Expr.expr
  (** Module for working with boolean expressions *)

  and t = t_node Hashcons.hash_consed
  (** The type for a hashconsed boolean expression *)

  (* The internal type of the boolean expression*)
  and t_ =
    | Zero
    | One
    | PBool of string * int
    | Or of t * t
    | And of t * t
    | Not of t

  module T_node = struct
    type t = t_node

    let equal (t1, _) (t2, _) =
      match (t1, t2) with
      | Zero, Zero -> true
      | One, One -> true
      | PBool (_, i), PBool (_, j) -> i == j
      | Or (x1, y1), Or (x2, y2) -> x1 == x2 && y1 == y2
      | And (x1, y1), And (x2, y2) -> x1 == x2 && y1 == y2
      | Not x1, Not x2 -> x1 == x2
      | _ -> false

    let hash (t, _) =
      match t with
      | Zero -> Hashtbl.hash `Zero
      | One -> Hashtbl.hash `One
      | PBool (_, i) -> Hashtbl.hash (`PBool i)
      | Or (x, y) -> Hashtbl.hash (`Or (x.hkey, y.hkey))
      | And (x, y) -> Hashtbl.hash (`And (x.hkey, y.hkey))
      | Not x -> Hashtbl.hash (`Not x.hkey)
  end

  module HashT = Hashcons.Make (T_node)

  (** table used for hash consing 
    notice because of hash consing, we can build *)
  let tbl = HashT.create 251

  let z3_empty_ctx = Z3.mk_context []
  let hashcons = HashT.hashcons tbl
  let zero : t = hashcons @@ (Zero, Z3.Boolean.mk_false z3_empty_ctx)
  let one : t = hashcons @@ (One, Z3.Boolean.mk_true z3_empty_ctx)

  let pBool (str : string) : t =
    hashcons
    @@ (PBool (str, Hashtbl.hash str), Z3.Boolean.mk_const_s z3_empty_ctx str)

  let b_not (b1 : t) : t =
    if b1 == one then zero
    else if b1 == zero then one
    else
      let _, b1_ = b1.node in
      hashcons @@ (Not b1, Z3.Boolean.mk_not z3_empty_ctx b1_)

  let b_or (b1 : t) (b2 : t) : t =
    if b1 == one then one
    else if b2 == one then one
    else if b1 == zero then b2
    else if b2 == zero then b1
    else if b1 == b2 then b1
    else if b1 == b_not b2 then one
    else
      let _, b1_ = b1.node in
      let _, b2_ = b2.node in
      hashcons @@ (Or (b1, b2), Z3.Boolean.mk_or z3_empty_ctx [ b1_; b2_ ])

  let b_and (b1 : t) (b2 : t) : t =
    if b1 == one then b2
    else if b2 == one then b1
    else if b1 == zero then zero
    else if b2 == zero then zero
    else if b1 == b2 then b1
    else if b1 == b_not b2 then zero
    else
      let _, b1_ = b1.node in
      let _, b2_ = b2.node in
      hashcons @@ (And (b1, b2), Z3.Boolean.mk_and z3_empty_ctx [ b1_; b2_ ])

  (** convert a boolean expression to z3 expression *)
  let to_z3 (b : t) : Z3.Expr.expr = snd b.node

  let solver = Z3.Solver.mk_solver z3_empty_ctx None

  (** test if a boolean expression is constant false

  In other word, whether it is unsatisfiable. *)
  let is_false (b : t) : bool =
    match Z3.Solver.check solver [ to_z3 b ] with
    | Z3.Solver.UNSATISFIABLE -> true
    | _ -> false

  (** Test if two boolean expressions is semantically equivelant. *)
  let equiv (b1 : t) (b2 : t) : bool =
    let iff_exp = Z3.Boolean.mk_iff z3_empty_ctx (to_z3 b1) (to_z3 b2) in
    let not_iff_exp = Z3.Boolean.mk_not z3_empty_ctx iff_exp in
    (* if ¬ (b1 ↔ b2) is unsatisfiable, then b1 ↔ b2 is a tautology,
       thus b1 and b2 are semantically equivalent.*)
    match Z3.Solver.check solver [ not_iff_exp ] with
    | Z3.Solver.UNSATISFIABLE -> true
    | _ -> false

  let pprint e = Z3.Expr.to_string @@ to_z3 e
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

  let while_do (b : BExp.t) (e : t) : t = hashcons @@ While (b, e)
  (* if b == BExp.zero then skip
     else if b == BExp.one then fail
     else if e == skip || e == fail then test @@ BExp.b_not b
     else *)

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
          let bs = BExp.pprint b in
          let s1, p1 = helper e1 in
          let s2, p2 = helper e2 in
          let s1' = if p1 <= 3 then s1 else "(" ^ s1 ^ ")" in
          let s2' = if p2 < 3 then s2 else "(" ^ s2 ^ ")" in
          ("if " ^ bs ^ " then " ^ s1' ^ " else " ^ s2', 3)
      | Test b ->
          let bs = BExp.pprint b in
          (bs, 1)
      | While (b, e) ->
          let bs = BExp.pprint b in
          let s, p = helper e in
          let s' = if p <= 1 then s else "(" ^ s ^ ")" in
          ("while " ^ bs ^ " do " ^ s' ^ " done", 1)
    in
    fst @@ helper exp
end

module Derivatives = struct
  type res = To of State.t * int (*changed from Pact*)
  type trans = State.t -> BExp.t -> res
  type be_res_map = BExp.t * res

  type automaton = {
    accept : State.t -> BExp.t;
    (*  ϵ̂ *)
    (*all the atoms that the input state accepts*)
    states : State.Set.t;
    trans : State.t -> be_res_map list;
        (* δ̂ all the atoms that will transition to a certain result*)
    start : State.t;
  }

  type pAutomaton = {
    p_accept : BExp.t; (* ϵ* : The overall boolean expression accept *)
    accept : State.t -> BExp.t;
    (*  ϵ̂ *)
    (*all the atoms that the input state accepts*)
    states : State.Set.t;
    trans : State.t -> be_res_map list;
        (* δ̂ all the atoms that will transition to a certain result*)
    p_trans : be_res_map list;
        (* δ* set of (BExp.t , (s,p))  when compare, compare the tag of BE let compare b1 b2 = compare b1.tag b2.tag*)
  }

  module StateMap = Map.Make (State)

  type epsilonTrans = State.t -> res

  module DeadStates : sig
    type state_status_map_t = bool StateMap.t

    val is_dead :
      State.t -> automaton -> state_status_map_t -> bool * state_status_map_t

    val known_dead : State.t -> state_status_map_t -> bool
    val clear_dead : state_status_map_t

    val length :
      state_status_map_t -> int (*Is this necessary??? testing purposes?*)
  end = struct
    type state_status_map_t = bool StateMap.t

    let known_dead state state_status_map =
      match StateMap.find_opt state state_status_map with
      | Some true -> true
      | _ -> false

    let clear_dead = StateMap.empty
    let length state_status_map = StateMap.cardinal state_status_map

    type visitRes =
      | KnownDead
          (** The visited state is *known* to be dead, i.e., in `state_status_map` *)
      | Live
          (** The visited state is live, i.e., it can reach an accepting state *)
      | Unknown of State.t list
          (** The visited state is unknown to be dead or live. 
            The argument is all the explored states while visiting that state. *)

    (** Helper to `visit`, visit all the descendants of a state, return a visit result *)

    let rec visit_descendants (explored : State.t list) (states : State.t list)
        (automaton : automaton) (state_status_map : state_status_map_t) :
        visitRes * state_status_map_t =
      match states with
      | [] -> (Unknown explored, state_status_map)
      | s :: rest -> (
          let result, state_status_map =
            visit explored s automaton state_status_map
          in
          match result with
          | Live -> (Live, state_status_map)
          | KnownDead ->
              visit_descendants (s :: explored) rest automaton state_status_map
          | Unknown more_states ->
              visit_descendants
                (List.append explored more_states)
                rest automaton state_status_map)

    (** Visit a single state *)
    and visit (explored : State.t list) (state : State.t) (auto : automaton)
        (state_status_map : state_status_map_t) : visitRes * state_status_map_t
        =
      if known_dead state state_status_map then (KnownDead, state_status_map)
      else if List.mem state explored then (Unknown explored, state_status_map)
      else
        (* Explore the current state *)
        let explored = state :: explored in
        if not (BExp.is_false (auto.accept state)) then
          (Live, StateMap.add state false state_status_map)
        else
          (* Get the next reachable states from transitions *)
          let transitions = auto.trans state in
          let next_states =
            List.filter_map
              (fun (cond, To (next_state, _)) ->
                if BExp.is_false cond then None else Some next_state)
              transitions
          in
          let result, state_status_map =
            visit_descendants explored next_states auto state_status_map
          in
          match result with
          | Live -> (Live, StateMap.add state false state_status_map)
          | KnownDead -> (KnownDead, StateMap.add state true state_status_map)
          | Unknown _ -> (KnownDead, StateMap.add state true state_status_map)
    (*final result, unknown, hence dead!*)

    (** Check whether a state is dead.
      When it returns false, the state is necessarily live. *)

    let is_dead (state : State.t) (auto : automaton)
        (state_status_map : state_status_map_t) : bool * state_status_map_t =
      let result, state_status_map = visit [] state auto state_status_map in
      match result with
      | Live -> (false, state_status_map)
      | KnownDead -> (true, state_status_map)
      | Unknown _ -> (true, state_status_map)
  end

  let res_to_left (r : be_res_map list) (coprod : MakePosInt.coprodRes) :
      be_res_map list =
    List.map
      (fun (boolean_expression, To (state, action)) ->
        (boolean_expression, To (coprod.to_left state, action)))
      r

  let res_to_right (r : be_res_map list) (coprod : MakePosInt.coprodRes) :
      be_res_map list =
    List.map
      (fun (boolean_expression, To (state, action)) ->
        (boolean_expression, To (coprod.to_right state, action)))
      r

  let reject (trans : be_res_map list) (acc : BExp.t) : BExp.t =
    let res = BExp.b_not acc in
    List.fold_left (fun acc (be, _) -> BExp.b_and (BExp.b_not be) acc) res trans

  (* let rec satisfy (at : BExp.t) (iota : BExp.t) : bool =
     match iota.node with
     | Zero -> false
     | BExp.One -> true
     | PBool b -> Atom.mem b at
     | Or (i, b) -> satisfy at i || satisfy at b
     | And (i, b) -> satisfy at i && satisfy at b
     | Not b -> not (satisfy at b)
  *)

  let rec thompson_construct (exp : Exp.t) : pAutomaton =
    match exp.node with
    | Test b ->
        {
          p_accept = b;
          (* ϵ* : The overall boolean expression *)
          accept = (fun _ -> BExp.one);
          (*  ϵ̂ *)
          states = State.Set.empty;
          (* S *)
          trans = (fun _ -> []);
          (* δ̂ all the atoms that will transition to a certain result*)
          p_trans = [];
          (* δ*  ???*)
        }
    | Pact (_, p) ->
        {
          p_accept = BExp.zero;
          (* ϵ* : The overall boolean expression *)
          accept = (fun _ -> BExp.one);
          (*  ϵ̂ *)
          states = State.Set.singleton State.elem;
          (* S *)
          trans = (fun _ -> []);
          (* why it is empty? *)
          p_trans = [ (BExp.one, To (State.elem, p)) ];
          (* δ*  ???*)
        }
    | If (b, exp1, exp2) ->
        let auto1 = thompson_construct exp1 in
        let auto2 = thompson_construct exp2 in
        let coprod, all_states =
          State.coprod_with_dom auto1.states auto2.states
        in
        {
          states = all_states;
          p_accept =
            BExp.b_or
              (BExp.b_and b auto1.p_accept)
              (BExp.b_and (BExp.b_not b) auto2.p_accept);
          accept =
            (fun s ->
              match coprod.from_coprod s with
              | Right state -> auto2.accept state
              | Left state -> auto1.accept state);
          p_trans = List.append auto1.p_trans auto2.p_trans;
          trans =
            (fun s ->
              match coprod.from_coprod s with
              | Right state -> res_to_right (auto2.trans state) coprod
              | Left state -> res_to_left (auto1.trans state) coprod);
        }
    | Seq (exp1, exp2) ->
        let auto1 = thompson_construct exp1 in
        let auto2 = thompson_construct exp2 in
        let coprod, all_states =
          State.coprod_with_dom auto1.states auto2.states
        in
        {
          states = all_states;
          p_accept = BExp.b_and auto1.p_accept auto2.p_accept;
          accept =
            (fun s ->
              match coprod.from_coprod s with
              | Right state -> auto2.accept state
              | Left state -> BExp.b_and (auto1.accept state) auto2.p_accept);
          (*?*)
          p_trans =
            List.append auto1.p_trans
              (List.map
                 (fun (boolean_expression, To (state, action)) ->
                   ( BExp.b_and boolean_expression auto1.p_accept,
                     To (state, action) ))
                 auto2.p_trans);
          trans =
            (fun s ->
              match coprod.from_coprod s with
              | Right state -> res_to_right (auto2.trans state) coprod
              | Left state ->
                  List.append
                    (res_to_left (auto1.trans state) coprod)
                    (res_to_right
                       (List.map
                          (fun (boolean_expression, To (state, action)) ->
                            ( BExp.b_and boolean_expression (auto1.accept state),
                              To (state, action) ))
                          auto2.p_trans)
                       coprod));
        }
    | While (be, exp) ->
        let auto = thompson_construct exp in
        {
          states = auto.states;
          p_accept = BExp.b_or (BExp.b_not be) auto.p_accept;
          accept = (fun state -> BExp.b_or (BExp.b_not be) (auto.accept state));
          p_trans =
            List.map
              (fun (boolean_expression, To (state, action)) ->
                (BExp.b_and boolean_expression be, To (state, action)))
              auto.p_trans;
          trans =
            (fun s ->
              let set = auto.trans s in
              List.map
                (fun (boolean_expression, To (state, action)) ->
                  ( BExp.b_and (BExp.b_and boolean_expression be) (auto.accept s),
                    To (state, action) ))
                set);
        }

  let convert (p_auto : pAutomaton) : automaton =
    let newStart = State.fresh p_auto.states in
    {
      states = State.Set.add newStart p_auto.states;
      accept =
        (fun state ->
          match state == newStart with
          | true -> p_auto.p_accept
          | false -> p_auto.accept state);
      trans =
        (fun state ->
          match state == newStart with
          | true -> p_auto.p_trans
          | false -> p_auto.trans state);
      start = newStart;
    }

  let union_find_maps (auto1 : automaton) (auto2 : automaton) :
      int UnionFind.elem StateMap.t * int UnionFind.elem StateMap.t =
    let uf_map1 =
      List.map
        (fun s -> (s, UnionFind.make s))
        (auto1.states |> State.Set.to_list)
      |> StateMap.of_list
    in
    (* print_endline
       ("the Statemap of a1's states is "
       ^ AutomatonPrinter.statemap_printer uf_map1); *)
    let uf_map2 =
      List.map
        (fun s -> (s, UnionFind.make s))
        (auto2.states |> State.Set.to_list)
      |> StateMap.of_list
    in
    (* print_endline
       ("the Statemap of a2's states is "
       ^ AutomatonPrinter.statemap_printer uf_map2); *)
    (uf_map1, uf_map2)

  let assert_rej (reject : BExp.t) (auto_transition : be_res_map list) : bool =
    List.for_all
      (fun (be, To (_, _)) -> BExp.is_false @@ BExp.b_and reject be)
      auto_transition

  let equiv_help (auto1 : automaton) (auto2 : automaton) : bool =
    (*create dead maps to keep track of dead states*)
    let auto1_deadmap = DeadStates.clear_dead in
    let auto2_deadmap = DeadStates.clear_dead in

    (* get union find maps for each auto*)
    let uf_map1, uf_map2 = union_find_maps auto1 auto2 in
    (* get union find element of automatons*)
    let get_elem1 s = StateMap.find s uf_map1 in
    let get_elem2 s = StateMap.find s uf_map2 in

    (*Main equivalent function*)
    let rec helper (todo : StatePairSet.t)
        (auto1_deadmap : DeadStates.state_status_map_t)
        (auto2_deadmap : DeadStates.state_status_map_t) :
        bool * DeadStates.state_status_map_t * DeadStates.state_status_map_t =
      match StatePairSet.choose_opt todo with
      | None ->
          (true, auto1_deadmap, auto2_deadmap)
          (* print_endline "";
             print_endline "Equiv asserted";
             print_endline ""; *)
      | Some (s1, s2) ->
          if
            (* if they are already marked bisimilar *)
            (* print_endline
               ("The s1 is " ^ string_of_int s1 ^ " The s2 is " ^ string_of_int s2); *)
            UnionFind.eq (get_elem1 s1) (get_elem2 s2)
          then
            let new_todo =
              (StatePairSet.remove (s1, s2)) todo (*remove checked from todo*)
            in
            helper new_todo auto1_deadmap auto2_deadmap
            (*Edited: Should not return true, should filter and continue*)
          else
            (*checking for dead states on the fly*)
            let s1_is_dead, auto1_deadmap =
              DeadStates.is_dead s1 auto1 auto1_deadmap
            in
            let s2_is_dead, auto2_deadmap =
              DeadStates.is_dead s2 auto2 auto2_deadmap
            in
            if s1_is_dead then (s2_is_dead, auto1_deadmap, auto2_deadmap)
            else if s2_is_dead then (s1_is_dead, auto1_deadmap, auto2_deadmap)
            else
              let reject1 = reject (auto1.trans s1) (auto1.accept s1) in
              let reject2 = reject (auto2.trans s2) (auto2.accept s2) in
              let auto1_transition = auto1.trans s1 in
              let auto2_transition = auto2.trans s2 in

              (*Check assertions one by one or calculate and at once ???*)
              let epsilon_assert =
                BExp.equiv (auto1.accept s1) (auto2.accept s2)
              in
              let assert_rej1 = assert_rej reject1 auto1_transition in
              let assert_rej2 = assert_rej reject2 auto2_transition in

              if epsilon_assert && assert_rej1 && assert_rej2 then
                (*if first 3 assertions are true, move to assert_trans*)
                let assert_trans, auto1_deadmap, auto2_deadmap =
                  List.fold_left2
                    (fun (acc, deadm1, deadm2) (be1, To (next_state1, p))
                         (be2, To (next_state2, q)) ->
                      if not acc then (false, deadm1, deadm2)
                        (* If already false, stop early *)
                      else if BExp.is_false @@ BExp.b_and be1 be2 then
                        (acc, deadm1, deadm2) (* Skip disjoint *)
                      else if p = q then
                        (*ignore @@ UnionFind.union exp1_ele exp2_ele;???*)
                        let new_todo =
                          StatePairSet.singleton (next_state1, next_state2)
                        in
                        let result, deadm1, deadm2 =
                          helper new_todo deadm1 deadm2
                        in
                        (acc && result, deadm1, deadm2)
                        (* Update the result and maps: all result should be true!*)
                      else (false, deadm1, deadm2))
                      (* Fails if `p` and `q` don't match *)
                    (true, auto1_deadmap, auto2_deadmap)
                    (* first argument for fold_left2: acc = true to begin with *)
                    auto1_transition auto2_transition
                  (*the two lists taken by the fold: transitions from both autos (be_res_map list*)
                in

                (assert_trans, auto1_deadmap, auto2_deadmap)
              else (false, auto1_deadmap, auto2_deadmap)
    in
    let start_pair = StatePairSet.singleton (auto1.start, auto2.start) in
    let result, _, _ = helper start_pair auto1_deadmap auto2_deadmap in
    result
end
