open Common

module PActSet = Set.Make (String)

type res = Accept | Rejeject | To of State.t * pAct
type trans = State.t -> Atom.t -> res

module Automaton = struct

  type t = 
    |P_tests of PBoolSet.t
    |P_acts of PActSet.t
    |States of StateSet.t
    |Trans of trans
    |Start of State.t
   

end

module PAutomaton = struct

  type pState = Atom.t -> res
  type t = 
    |P_tests of PBoolSet.t
    |P_acts of PActSet.t
    |States of StateSet.t
    |Trans of trans
    |Start of pState
   

end