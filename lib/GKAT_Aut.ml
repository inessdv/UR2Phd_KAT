open Common
open GKAT_2
open PointedCoprod
module PActSet = Set.Make (String)

type res = Accept | Rejeject | To of State.t * pAct
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
  | Seq (ex1, ex2) ->
      let s1 = thompson_construct ex1 p_act p_test in
      let s2 = thompson_construct ex2 p_act p_test in
      let coprod, all_states = State.coprod_with_dom s1.states s2.states in
      let res_to_left r =
        match r with
        | Accept -> Accept
        | Rejeject -> Rejeject
        | To (s, p_act) -> To (coprod.to_left s, p_act)
      in

      let res_to_right r =
        match r with
        | Accept -> Accept
        | Rejeject -> Rejeject
        | To (s, p_act) -> To (coprod.to_right s, p_act)
      in
      (* let right_states =State.Set.map coprod.to_right s2.states in  *)
      {
        p_tests = p_test;
        p_acts = p_act;
        states = all_states;
        trans =
          (fun state atom ->
            match coprod.from_coprod state with
            | Right s -> s2.trans s atom |> res_to_right
            | Left s -> (
                match s1.trans s atom with
                | Accept ->
                    s2.p_start p_test |> res_to_right (*Not important input*)
                | r -> r |> res_to_left));
        p_start =
          (fun at ->
            match s1.p_start at with Accept -> s2.p_start at | r -> r);
      }
  | If (bexp, exp1, exp2) ->
      let s1 = thompson_construct exp1 p_act p_test in
      let s2 = thompson_construct exp2 p_act p_test in
      let temp = Test bexp in
      let coprod, all_states = State.coprod_with_dom s1.states s2.states in
      let res_to_left r =
        match r with
        | Accept -> Accept
        | Rejeject -> Rejeject
        | To (s, p_act) -> To (coprod.to_left s, p_act)
      in

      let res_to_right r =
        match r with
        | Accept -> Accept
        | Rejeject -> Rejeject
        | To (s, p_act) -> To (coprod.to_right s, p_act) in
      {
        p_tests = p_test;
        p_acts = p_act;
        states = all_states;
        trans = (fun state atom ->
          match coprod.from_coprod state with
          | Right s -> s2.trans s atom |> res_to_right
          | Left s -> s1.trans s atom |> res_to_left);
        p_start = (fun atom -> if satisfy atom bexp then s1.p_start atom |> res_to_left else s2.p_start atom |> res_to_right);
      }
  (* let right_states =State.Set.map coprod.to_right s2.states in
     let bauto= thompson_construct temp p_act p_test in

       let s1_s2_state= State.Set.union s1.states right_states; in
       let atom= Atom.of_p_bools p_test in
       if satisfy atom bexp then
     bauto.states=State.Set.union s1.states right_states
     else s1 *)
  (* if satisfy p_test bexp then
         {
         p_tests = p_test;
         p_acts = p_act;
         states = State.Set.union s1.states right_states ;
         trans = s1.trans;
         p_start = s1.p_start;
       }
     else {
       p_tests = p_test;
       p_acts = p_act;
       states = State.Set.union s1.states right_states ;
       trans = s2.trans;
       p_start = s2.p_start;
     } *)
  | Test b ->
      {
        p_tests = p_test;
        p_acts = p_act;
        states = State.Set.empty;
        trans =
          (fun _ ->
            failwith "no result");
            p_start = fun at -> if satisfy at b then Accept else Rejeject;
      }
  | While -> _
