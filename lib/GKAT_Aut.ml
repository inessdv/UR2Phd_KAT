open Common
open GKAT_2
open PointedCoprod
module PActSet = Set.Make (String)

type res = Accept | Reject | To of State.t * pAct
type trans = State.t -> Atom.t -> res

module Automaton = struct
  type t = {
    p_tests : PBoolSet.t;
    p_acts : PActSet.t;
    states : State.Set.t;
    trans : trans;
    start : State.t;
  }
end

module PAutomaton = struct
  type t = {
    p_tests : PBoolSet.t;
    p_acts : PActSet.t;
    states : State.Set.t;
    trans : trans;
    p_start : Atom.t -> res;
  }
end

let res_to_left (r : res) (coprod : MakePosInt.coprodRes) : res =
  match r with
  | Accept -> Accept
  | Reject -> Reject
  | To (s, p_act) -> To (coprod.to_left s, p_act)

let res_to_right (r : res) (coprod : MakePosInt.coprodRes) : res =
  match r with
  | Accept -> Accept
  | Reject -> Reject
  | To (s, p_act) -> To (coprod.to_right s, p_act)

let rec satisfy (at : Atom.t) (iota : bExp) : bool =
  match iota with
  | Zero -> false
  | One -> true
  | PBool b -> Atom.mem b at
  | Or (i, b) -> satisfy at i || satisfy at b
  | And (i, b) -> satisfy at i && satisfy at b
  | Not b -> not (satisfy at b)

(* let seq_transit_helper (state:State.Set.t)(at:Atom.t): res{

   } *)

let rec thompson_construct (exp : gkat) (p_act : PActSet.t)
    (p_test : PBoolSet.t) : PAutomaton.t =
  match exp with
  | Pact p ->
      {
        p_tests = p_test;
        p_acts = p_act;
        states = State.Set.singleton State.elem;
        trans = (fun _ _ -> Accept);
        p_start = (fun _ -> To (State.elem, p));
      }
  | Seq (exp1, exp2) ->
      let auto1 = thompson_construct exp1 p_act p_test in
      let auto2 = thompson_construct exp2 p_act p_test in
      let coprod, all_states =
        State.coprod_with_dom auto1.states auto2.states
      in
      {
        p_tests = p_test;
        p_acts = p_act;
        states = all_states;
        trans =
          (fun state atom ->
            match coprod.from_coprod state with
            | Right s -> res_to_right (auto2.trans s atom) coprod
            | Left s -> (
                match auto1.trans s atom with
                | Accept -> res_to_right (auto2.p_start p_test) coprod
                | r -> res_to_left r coprod));
        p_start =
          (fun at ->
            match auto1.p_start at with Accept -> auto2.p_start at | r -> r);
      }
  | If (bexp, exp1, exp2) ->
      let auto1 = thompson_construct exp1 p_act p_test in
      let auto2 = thompson_construct exp2 p_act p_test in
      let coprod, all_states =
        State.coprod_with_dom auto1.states auto2.states
      in
      {
        p_tests = p_test;
        p_acts = p_act;
        states = all_states;
        trans =
          (fun state atom ->
            match coprod.from_coprod state with
            | Right s -> res_to_right (auto2.trans s atom) coprod
            | Left s -> res_to_left (auto1.trans s atom) coprod);
        p_start =
          (fun atom ->
            if satisfy atom bexp then res_to_left (auto1.p_start atom) coprod
            else res_to_right (auto2.p_start atom) coprod);
      }
  | Test b ->
      {
        p_tests = p_test;
        p_acts = p_act;
        states = State.Set.empty;
        trans = (fun _ -> failwith "no result");
        p_start = (fun at -> if satisfy at b then Accept else Reject);
      }
  | While (bexp, exp) ->
      let auto1 = thompson_construct exp p_act p_test in
      let iota_e atom =
        if satisfy atom bexp then
          match auto1.p_start atom with
          | Accept -> Reject
          | _ -> auto1.p_start atom
        else Accept
      in

      {
        p_tests = p_test;
        p_acts = p_act;
        states = auto1.states;
        trans =
          (fun state atom ->
            match auto1.trans state atom with Accept -> iota_e atom | r -> r);
        p_start = iota_e;
      }

let convert (pauto : PAutomaton.t) : Automaton.t =
  let newStart = State.fresh pauto.states in
  {
    p_tests = pauto.p_tests;
    p_acts = pauto.p_acts;
    states = State.Set.add newStart pauto.states ;
    trans =
      (fun state atom ->
        match state==newStart with    (*If statement*)
        | true -> pauto.p_start atom
        | false -> pauto.trans state atom);
    start = newStart;
  }

let check_res (res1 : res) (res2 : res) : StatePairSet.t option =
  match (res1, res2) with
  | Accept, Accept -> Some StatePairSet.empty
  | Reject, Reject -> Some StatePairSet.empty
  | To (s1, p1), To (s2, p2) ->
      let s_pair = StatePairSet.singleton (s1, s2) in
      if p1 = p2 then Some s_pair else None
  | _ -> None

let rec check_atoms ((s1, s2) : State.t * State.t)
(atoms_toCheck : PActSet.t list) (a1 : Automaton.t) (a2 : Automaton.t) :
    StatePairSet.t option =
  match atoms_toCheck with
  | [] -> Some StatePairSet.empty
  | atom :: rest -> (
      match check_res (a1.trans s1 atom) (a2.trans s2 atom) with
      | None -> None
      | Some s_pairs -> (
          match check_atoms (s1, s2) rest a1 a2 with
          | None -> None
          | Some s_pairs1 -> Some (StatePairSet.union s_pairs s_pairs1)))

let rec bisim (a1 : Automaton.t) (a2 : Automaton.t) : bool =
  assert (a1.p_tests = a2.p_tests);
  let atoms = Atom.of_p_bools a1.p_tests in
  let rec help (todo : StatePairSet.t) (checked : StatePairSet.t) : bool =
    match StatePairSet.choose_opt todo with
    | None -> true
    | Some (s1, s2) -> (
        (* add check_atoms inside function to avoid passing a1 and a2??*)
        match check_atoms (s1, s2) atoms a1 a2 with
        | None -> false
        | Some to_check ->
            help
              (StatePairSet.union to_check todo)
              (StatePairSet.union checked (StatePairSet.singleton (s1, s2))))
  in

  let start_pair = StatePairSet.singleton (a1.start, a2.start) in
  help start_pair StatePairSet.empty

(*bisim with check_atoms as an inside function!*)
let rec bisim (a1 : Automaton.t) (a2 : Automaton.t) : bool =
  assert (a1.p_tests = a2.p_tests);
  let atoms = Atom.of_p_bools a1.p_tests in       (*Declare check_atoms after here*)
  let rec help (todo : StatePairSet.t) (checked : StatePairSet.t) : bool =
    match StatePairSet.choose_opt todo with
    | None -> true
    | Some (s1, s2) -> (
        let rec check_atoms ((s1, s2) : State.t * State.t)
            (atoms_toCheck : PActSet.t list) : StatePairSet.t option =
          match atoms_toCheck with
          | [] -> Some StatePairSet.empty
          | atom :: rest -> (
              match check_res (a1.trans s1 atom) (a2.trans s2 atom) with
              | None -> None
              | Some s_pairs -> (
                  match check_atoms (s1, s2) rest with
                  | None -> None
                  | Some s_pairs_rest -> Some (StatePairSet.union s_pairs s_pairs_rest))
              )
        in
        match check_atoms (s1, s2) atoms with
        | None -> false
        | Some to_check ->
          let checked = StatePairSet.add  (s1,s2) checked   in
          let to_check = StatePairSet.diff to_check checked in
          let todo = StatePairSet.diff todo checked in
            help
              (StatePairSet.union to_check todo)
              checked )
  in

  let start_pair = StatePairSet.singleton (a1.start, a2.start) in
  help start_pair StatePairSet.empty

(* do we need to code a bisim for PAutomaton?*)
