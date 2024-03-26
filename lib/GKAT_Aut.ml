open Common
open GKAT_2

module PActSet = Set.Make (String)

type res = Accept | Rejeject | To of State.t * pAct
type trans = State.t -> Atom.t -> res

module StateSet = Set.Make (String)

module Automaton = struct

  type t = {
    p_tests: PBoolSet.t;
    p_acts: PActSet.t;
    states: StateSet.t;
    trans: trans;
    start: State.t;
  }
   
end

module PAutomaton = struct

  type t = {
    p_tests: PBoolSet.t;
    p_acts: PActSet.t;
    states: StateSet.t;
    trans: trans;
    start: State.t;
    p_start: Atom.t -> res;
  }
end


let rec satisfy (at: Atom.t)(iota: bExp): bool =
  match iota with
  
  |Zero -> false
  |One -> true
  |PBool b -> Atom.mem b at
  |Or (i,b) -> satisfy at i || satisfy at b
  |And (i,b) -> satisfy at i && satisfy at b
  |Not b -> not (satisfy at b)

let thompson_construct (exp:gkat)(p_act: PActSet.t)(p_test: PBoolSet.t): PAutomaton.t =
  match exp with 
  | Pact p -> {
    p_tests = p_test;
    p_acts = p_act;
    states = StateSet.singleton ;
    trans = fun _ _ -> Accept;
    p_start = fun at -> To(State.elem, p);
  }
  | Seq -> {
    p_tests = ;
    p_acts = ;
    states =  ;
    trans = ;
    p_start = ;
  } 
  | If -> {
    p_tests = ;
    p_acts = ;
    states =  ;
    trans = ;
    p_start = ;
  } 
  | Test b -> {
    p_tests = p_test;
    p_acts = p_act;
    states = StateSet.empty ;
    trans = fun _ -> failwith "no result";
    p_start = fun at -> if satisfy at b then Accept else Reject ;
  }
  | While -> {
    p_tests = ;
    p_acts = ;
    states =  ;
    trans = ;
    p_start = ;
  }