open Common
open PointedCoprod
module PActSet = Set.Make (String)

module BExp = struct
  type t_node = t_
  (** Module for working with boolean expressions *)

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

  (** table used for hash consing 
    notice because of hash consing, we can build *)
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

  let b_or (b1 : t) (b2 : t) : t =
    if b1 == one then one
    else if b2 == one then one
    else if b1 == zero then b2
    else if b2 == zero then b1
    else if b1 == b2 then b1
    else if b1 == b_not b2 then one
    else hashcons @@ Or(b1, b2)

  let b_and (b1 : t) (b2 : t) : t =
    if b1 == one then b2
    else if b2 == one then b1
    else if b1 == zero then zero
    else if b2 == zero then zero
    else if b1 == b2 then b1
    else if b1 == b_not b2 then zero
    else hashcons @@ And (b1, b2)
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
  (* let p_act (p : string) : t = hashcons @@ Pact (p, Hashtbl.hash p) *)
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

type res = To of State.t * int (*changed from Pact*)
type trans = State.t -> BExp.t -> res
type be_res_map = BExp.t * res

module Automaton = struct
  type t = {
    accept : State.t -> BExp.t;
    (*  ϵ̂ *)
    (*all the atoms that the input state accepts*)
    states : State.Set.t;
    trans : State.t -> be_res_map list;
        (* δ̂ all the atoms that will transition to a certain result*)
    start : State.t;
  }
end

module PAutomaton = struct
  type t = {
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
end

module StateTbl = Hashtbl.Make (struct
  type t = State.t
  let equal s1 s2 = s1 == s2
  let hash = Int.hash
end)

module StateHSet = struct
  type t = unit StateTbl.t

  let create : int -> t = StateTbl.create
  let add (state : State.t) (s : t) : unit = StateTbl.add s state ()
  let remove (state : State.t) (s : t) : unit = StateTbl.remove s state

  let mem (state : State.t) (s : t) : bool =
    Option.is_some @@ StateTbl.find_opt s state

  let add_to_fst (hset1 : t) (hset2 : t) : unit =
    StateTbl.iter (fun state _ -> add state hset1) hset2

  let clear = StateTbl.clear
  let length = StateTbl.length
end

module type DeadStates = sig
  val is_dead : State.t -> Automaton.t -> bool
  val known_dead : State.t -> bool
  val clear_dead : unit -> unit
end

module MakeDeadStateHash (S:Solver) : DeadStates = struct
  let b_is_false (b : BExp.t) : bool = S.is_false b.node

  let dead_states : StateHSet.t = StateHSet.create 251
  let known_dead (state : State.t) : bool = StateHSet.mem state dead_states
  let clear_dead () = StateHSet.clear dead_states

  type visitRes =
    | KnownDead
        (** The visited state is *known* to be dead, i.e., in `state_status_map` *)
    | Live
        (** The visited state is live, i.e., it can reach an accepting state *)
    | Unknown of StateHSet.t
        (** The visited state is unknown to be dead or live. 
            The argument is all the explored states while visiting that state. *)

  (** Helper to `visit`, visit all the descendants of a state, return a visit result *)

  let rec visit_descendants (explored : StateHSet.t) (states : State.t list)
      (auto : Automaton.t) : visitRes =
    match states with
    | [] -> Unknown explored
    | s :: rest -> (
        match visit explored s auto with
        | Live -> Live
        | KnownDead ->
            StateHSet.add s explored;
            visit_descendants explored rest auto
        | Unknown unknown_states ->
            StateHSet.add_to_fst explored unknown_states;
            visit_descendants explored rest auto)

  (** Visit a single state *)
  and visit (explored : StateHSet.t) (state : State.t) (auto : Automaton.t) :
      visitRes =
    if known_dead state then KnownDead
    else if StateHSet.mem state explored then Unknown explored
    else (
      (* Explore the current state *)
      StateHSet.add state explored;
      (* Check acceptance of the state *)
      if not (b_is_false (auto.accept state)) then Live
      else
        (* Get the next reachable states from transitions *)
        let transitions = auto.trans state in
        let next_states =
          List.filter_map
            (fun (cond, To (next_state, _)) ->
              if b_is_false cond then None else Some next_state)
            transitions
        in
        visit_descendants explored next_states auto)

  (** Check whether a state is dead.
      When it returns false, the state is necessarily live. *)

  let is_dead (state : State.t) (auto : Automaton.t) : bool =
    match visit (StateHSet.create 251) state auto with
    | Live -> false
    | KnownDead -> true
    | Unknown all_explored ->
        (*ADD TO FIRST*)
        StateHSet.add_to_fst dead_states all_explored;
        true
end

module Derivatives (S:Solver) = struct
  let b_is_false (b : BExp.t) : bool = S.is_false b.node
  let b_equiv (b1 : BExp.t) (b2 : BExp.t) : bool = S.equiv b1.node b2.node
  let pprint_be_res_map (be_res_map : be_res_map) =
    let bexp, res = be_res_map in
    let bexp_str = BExp.pprint bexp.node in
    match res with
    | To (state, int_val) ->
        Printf.sprintf "(%s -> To(State %d, p%d))" bexp_str state int_val

  let pprint_state (state : State.t) = Printf.sprintf "State %d" state
  let pprint_states (states : MakePosInt.Set.t) =
    states
    |> MakePosInt.Set.elements
    |> List.map pprint_state    
    |> String.concat ", "       

  let pprint_transitions (trans : State.t -> be_res_map list)
      (states : State.Set.t) =
    State.Set.fold
      (fun state acc ->
        let transitions = trans state in
        let transition_str =
          List.map pprint_be_res_map transitions |> String.concat ", "
        in
        acc ^ Printf.sprintf "\n  %s: [%s]" (pprint_state state) transition_str)
      states ""

  let pprint_automaton (automaton : Automaton.t) =
    let accept_str =
      State.Set.fold
        (fun state acc ->
          let accept_bexp = automaton.accept state in
          acc
          ^ Printf.sprintf "\n  %s: %s" (pprint_state state)
              (BExp.pprint accept_bexp.node))
        automaton.states ""
    in
    let transitions_str = pprint_transitions automaton.trans automaton.states in
    Printf.sprintf
      "Automaton:\n\
       States:\n\
       %s\n\
       Start State: %s\n\
       Accept Conditions:%s\n\
       Transitions:%s"
      (State.Set.fold
         (fun state acc -> acc ^ Printf.sprintf "\n  %s" (pprint_state state))
         automaton.states "")
      (pprint_state automaton.start)
      accept_str transitions_str

  let pprint_pautomaton (pautomaton : PAutomaton.t) =
    let accept_str =
      State.Set.fold
        (fun state acc ->
          let accept_bexp = pautomaton.accept state in
          acc
          ^ Printf.sprintf "\n  %s: %s" (pprint_state state)
              (BExp.pprint accept_bexp.node))
        pautomaton.states ""
    in
    let transitions_str =
      pprint_transitions pautomaton.trans pautomaton.states
    in
    let p_trans_str =
      List.map pprint_be_res_map pautomaton.p_trans |> String.concat "\n  "
    in
    Printf.sprintf
      "PAutomaton:\n\
       States:\n\
       %s\n\
       Accept Conditions:%s\n\
       p_accept: %s\n\
       Transitions:%s\n\
       p_trans:\n\
      \  %s"
      (State.Set.fold
         (fun state acc -> acc ^ Printf.sprintf "\n  %s" (pprint_state state))
         pautomaton.states "")
      accept_str
      (BExp.pprint pautomaton.p_accept.node)
      transitions_str p_trans_str

  module StateMap = Map.Make (State)

  let res_to_left (r : be_res_map list) (coprod : MakePosInt.coprodRes) :
      be_res_map list =
      print_endline("goint to res_toleft");
    List.map
      (fun (boolean_expression, To (state, action)) ->
        (boolean_expression, To (coprod.to_left state, action)))
      r

  let res_to_right (r : be_res_map list) (coprod : MakePosInt.coprodRes) :
      be_res_map list =
      print_endline("goint to res_toright");

    List.map
      (fun (boolean_expression, To (state, action)) ->
        (boolean_expression, To ((coprod.to_right state), action)))
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
    
  let rec thompson_construct (exp : Exp.t) : PAutomaton.t =
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
        print_endline("P auto for exp1 in if "^pprint_pautomaton auto1);
        let auto2 = thompson_construct exp2 in
        print_endline("P auto for exp2 in if "^pprint_pautomaton auto2);
        let coprod, all_states =
          State.coprod_with_dom auto1.states auto2.states in 
        let update_p_trans1= (List.map
        (fun (boolean_expression, To (state, action)) ->
          ( BExp.b_and boolean_expression b,
            To (state, action) ))
        auto1.p_trans) in 
        let update_p_trans2=(List.map
        (fun (boolean_expression, To (state, action)) ->
          ( BExp.b_and (boolean_expression) (BExp.b_not(b))),
            To (state, action) )
        auto2.p_trans)
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
          p_trans = List.append (res_to_left(update_p_trans1)(coprod)) (res_to_right(update_p_trans2)(coprod));
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
          accept = (fun state -> BExp.b_and (BExp.b_not be) (auto.accept state)); (*and?*)
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

  let convert (p_auto : PAutomaton.t) : Automaton.t =
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

  let union_find_maps (auto1 : Automaton.t) (auto2 : Automaton.t) :
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
      (fun (be, To (_, _)) -> b_is_false @@ BExp.b_and reject be)
      auto_transition

    
  let equiv_help (auto1 : Automaton.t) (auto2 : Automaton.t) : bool =
    (* get union find maps for each auto*)
    let uf_map1, uf_map2 = union_find_maps auto1 auto2 in
    (* get union find element of automatons*)
    let get_elem1 s = StateMap.find s uf_map1 in
    let get_elem2 s = StateMap.find s uf_map2 in
    let module DeadStateHash1 = MakeDeadStateHash (S) in
    let module DeadStateHash2 = MakeDeadStateHash (S) in
    (*Main equivalent function*)
    let rec helper (todo : StatePairSet.t) : bool =
      match StatePairSet.choose_opt todo with
      | None ->
          true
          (* print_endline "";
             print_endline "Equiv asserted";
             print_endline ""; *)
      | Some (s1, s2) ->
        print_endline("comparing state");
        print_int(s1);
        print_int(s2);
        print_newline();
          if
            (* if they are already marked bisimilar *)
            (* print_endline
               ("The s1 is " ^ string_of_int s1 ^ " The s2 is " ^ string_of_int s2); *)
            UnionFind.eq (get_elem1 s1) (get_elem2 s2)
          then
            let new_todo =
              (StatePairSet.remove (s1, s2)) todo (*remove checked from todo*)
            in
            helper new_todo
            (*Edited: Should not return true, should filter and continue*)
          else if
            (*checking for dead states on the fly*)
            DeadStateHash1.known_dead s1
          then 
            DeadStateHash2.is_dead s2 auto2
          else if DeadStateHash2.known_dead s2 then
            DeadStateHash1.is_dead s1 auto1
          else
            let reject1 = reject (auto1.trans s1) (auto1.accept s1) in
            let reject2 = reject (auto2.trans s2) (auto2.accept s2) in
            let auto1_transition = auto1.trans s1 in
            let auto2_transition = auto2.trans s2 in
            print_endline(List.map pprint_be_res_map auto1_transition|> String.concat ", ");
            print_endline(List.map pprint_be_res_map auto2_transition|> String.concat ", ");
            let epsilon_assert =
              b_equiv (auto1.accept s1) (auto2.accept s2)
            in
            print_endline "Checking same espilon: ";
            print_endline (string_of_bool epsilon_assert);
            epsilon_assert
            && (let assert_rej1 =
                  List.for_all
                    (fun (be, To (state, _)) ->
                      (b_is_false @@ BExp.b_and reject1 be)
                      || DeadStateHash1.is_dead state auto2)
                    auto2_transition
                in
                print_endline("forall ψ_f ↦ (f', q) ∈ δ(f), ( ρ(e) ∧ ψ_f = 0 || is_dead(f'))");
          print_endline (string_of_bool assert_rej1);
                assert_rej1)
            && (let assert_rej2 =
                  List.for_all
                    (fun (be, To (state, _)) ->
                      (b_is_false @@ BExp.b_and reject2 be)
                      || DeadStateHash2.is_dead state auto1)
                    auto1_transition
                in
                print_endline
               "assertion2 for: forall ψ_e ↦ (e', q) ∈ δ(f), ( ρ(f) ∧ ψ_f = 0 || \
                is_dead(e')) ";
             print_endline (string_of_bool assert_rej2); 
                assert_rej2)
            &&
            (*if first 3 assertions are true, move to assert_trans*)
            (* let fitered_trans1= List.filter (fun t -> t <> []) auto1_transition in  *)
            let assert_trans =
              List.for_all
                (fun ((be1, To (next_state1, p)), (be2, To (next_state2, q))) ->
                  (* `be1` `be2` disjoint, then skip*)
                  print_string("the is false function return");
                  print_endline(string_of_bool(b_is_false @@ BExp.b_and be1 be2));
                  (b_is_false @@ BExp.b_and be1 be2)
                  ||
                  (* `p` and `q` are the same, then recurse*)
                  if p = q then (
                    ignore @@ UnionFind.union (get_elem1 s1) (get_elem2 s2);
                    helper (StatePairSet.singleton (next_state1, next_state2))
                    (* `p` and `q` are not the same, then both need to be dead*)
                    (* else DeadExps.is_dead next_exp1 && DeadExps.is_dead next_exp2) *))
                  else
                    let res =
                    DeadStateHash1.is_dead next_state1 auto1 
                    && DeadStateHash2.is_dead next_state2 auto2 in 
                    print_string("checking deadstate we got");
                    print_endline(string_of_bool res);res)
                (Common.list_prod auto1_transition auto2_transition)
                (*If two states are not dead, but the don't have the same P_act, does it make the two expression not equivalent?*)
            in
            print_endline
            "assertion3 for: forall ψ_e ↦ (e', p) ∈ δ(e), ψ_f ↦ (f', q) ∈ δ(f) ";
          print_endline (string_of_bool assert_trans); 
            assert_trans
    in
    let start_pair = StatePairSet.singleton (auto1.start, auto2.start) in
    helper start_pair

  
  let equiv (exp1 : Exp.t) (exp2 : Exp.t) : bool =
    let pauto1 = thompson_construct exp1 in
    let pauto2 = thompson_construct exp2 in
    let auto1 = convert(pauto1) in 
    let auto2 = convert (pauto2) in 
    print_endline "The auto1's Pautomaton is ";
   print_endline(pprint_pautomaton pauto1) ;
   print_endline "The auto2's Pautomaton is ";
   print_endline(pprint_pautomaton pauto2) ;
   print_endline "The auto1 is ";
   print_endline(pprint_automaton auto1) ;
   print_endline "The auto2 is ";
   print_endline(pprint_automaton auto2) ;
    equiv_help auto1 auto2

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
  let example3 = Exp.if_then_else(BExp.b_and(BExp.pBool(1))(BExp.pBool(1))) (Exp.p_act("0")) (Exp.p_act("1"))
  let example4= (Exp.p_act("0"))
  let gkat_example1 =
    Exp.seq
      (Exp.seq (Exp.p_act "p7")
         (Exp.if_then_else (BExp.pBool 2) (Exp.p_act "p6")
            (Exp.seq
               (Exp.test (BExp.b_not (BExp.pBool 2)))
               (Exp.test (BExp.b_not (BExp.pBool 1))))))
      (Exp.test (BExp.b_not (BExp.pBool 1)))

  let gkat_example2 = Exp.seq (Exp.p_act "p7") (Exp.p_act "p5")

  (*EXP1: if b2 and b1 then p1 else p0*)
  let ex1 =
    Exp.if_then_else
      (BExp.b_and (BExp.pBool 2) (BExp.pBool 1))
      (Exp.p_act "p1") (Exp.p_act "p0")
  
  let ex =
        Exp.if_then_else
          ((BExp.pBool 2))
          (Exp.p_act "p1") (Exp.p_act "p0")
  

  (*EXP2: if ~(b2 and b1) then p0 else p1*)
  let ex2 =
    Exp.if_then_else
      (BExp.b_not (BExp.b_and (BExp.pBool 2) (BExp.pBool 1)))
      (Exp.p_act "p0") (Exp.p_act "p1")

  
  let testwhile = Exp.while_do (BExp.b_and (BExp.pBool 2) (BExp.pBool 1)) (Exp.p_act "p1")

  (*for manual test purposes of :  
  EXP1: while b1 do (if b2 then b1 else 1) done 
  and 
  EXP2: while b1 do (b2 * b1) done
  *)

  (*EXP1: while b1 do (if b2 then b1 else 1) done *)
  let counter_ex1 = Exp.while_do (BExp.pBool 1) (Exp.if_then_else (BExp.pBool 2) (Exp.test (BExp.pBool 1)) (Exp.test BExp.one))

  (*EXP2: while b1 do (b2 * b1) done*)
  let counter_ex2 = Exp.while_do (BExp.pBool 1) (Exp.test (BExp.b_and (BExp.pBool 2) (BExp.pBool 1)))
  
end
