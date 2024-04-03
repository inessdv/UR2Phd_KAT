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

let res_to_left (r: res) ( coprod: MakePosInt.coprodRes): res=
  match r with
  | Accept -> Accept
  | Reject -> Reject
  | To (s, p_act) -> To (coprod.to_left s, p_act)

let res_to_right (r: res) ( coprod: MakePosInt.coprodRes): res =
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
      let coprod, all_states = State.coprod_with_dom auto1.states auto2.states in
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
      let coprod, all_states = State.coprod_with_dom auto1.states auto2.states in
      {
        p_tests = p_test;
        p_acts = p_act;
        states = all_states;
        trans = (fun state atom ->
          match coprod.from_coprod state with
          | Right s -> res_to_right (auto2.trans s atom) coprod
          | Left s -> res_to_left (auto1.trans s atom) coprod);
        p_start = (fun atom -> if satisfy atom bexp then res_to_left (auto1.p_start atom) coprod
         else res_to_right (auto2.p_start atom) coprod);
      }

  | Test b ->
      {
        p_tests = p_test;
        p_acts = p_act;
        states = State.Set.empty;
        trans =
          (fun _ ->
            failwith "no result");
            p_start = fun at -> if satisfy at b then Accept else Reject;
      }
  | While(bexp,exp) -> 
    let auto1 = thompson_construct exp p_act p_test in
    { p_tests = p_test; p_acts = p_act; states = auto1.states; 
    trans = (fun state atom -> match auto1.trans state atom with 
    | Accept -> p_start atom
    | r -> r); 
    p_start = (fun atom -> if satisfy atom bexp then auto1.p_start atom else Accept);}
