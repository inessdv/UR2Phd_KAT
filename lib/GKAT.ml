(** Like powerset but for list
  All the elements in the resulting sub lists maintains their original order
    
  the function will enumerate all the sublist starting with current head,
  and once that doesn't start with the current head.*)
let rec power_list (l: 'a list): 'a list list = 
  match l with
  | [] -> [[]] 
  | h :: tail -> 
      let power_tail = power_list tail in 
      (power_tail |> List.map (fun sub_tail -> h :: sub_tail)) 
      @ power_tail
     
(** Given a "recursive function" that compute the one result,
    compute all of the result for each 'a, and arrange in a list, 
    the result is in the order of `inp`.
    
    The first argument of `comp_one_rec` is itself for recursion,
    except the first argument can return None, indicating a finite recursion.
    This function will cache the result of each computation to speed up recursion*)
let compute_map
    (comp_one_rec: ('a -> 'b option) ->'a -> 'b) 
    (inps: 'a list): ('a * 'b) list = 
  (* the value is marked None, when we are in the process of computing  *)
  let memo_tbl: ('a, 'b option) Hashtbl.t = Hashtbl.create (List.length inps) in 
  let rec comp_one_opt inp = 
    match Hashtbl.find_opt memo_tbl inp with 
    | Some res -> res 
    | None -> 
      (* Mark that we are currently computing results for `inp`*)
      let () = Hashtbl.add memo_tbl inp None in 
      (* recursion *)
      let res = comp_one_rec comp_one_opt inp in 
      let () = Hashtbl.replace memo_tbl inp (Some res) in
      Some res in
  (* function to compute one result *)
  let compute_one = comp_one_rec comp_one_opt in 
  List.map (fun inp -> (inp, compute_one inp)) inps


(** Primitive Booleans or Primitive Tests*)
type pBools = string 

(** Primitive Actions*)
type pAct = string 

module PBoolSet = Set.Make(String)

(** Atom is a set of pBools
    all the pBools that is in the set is regarded as positive
    and ones that are not in the set is regarded as negative*)
module Atom = Set.Make(String)
module AtomSet = Set.Make(Atom)

module Automaton = struct

  (** States for GKAT automaton *)
  type state = int64
  module StateSet = Set.Make(Int64)
  (** Possible results of GKAT automata transitions
      Rejection is implicit, by not present in the transition map*)
  type transRes = Accept | To of state * pAct
  (** Map correponding to transition function*)
  module StateAtomMap = Map.Make(struct
    type t = state * Atom.t 
    let compare = compare
  end)
  type transMap = transRes StateAtomMap.t

  (** GKAT automaton
      all the "non-trivial" states of the automaton are keys of the transMap,
      other states are implicitly transitioned to reject,
      regardless of the input atom.
      
      We do not check wether the transMap is valid, 
      it is up to the user to only use the primitive tests avalible in pBools*)
  type t = {
    p_bools: PBoolSet.t;
    start: state;
    trans_map: transMap;
  }

  let get_states (automaton: t): state list = 
    automaton.trans_map 
    |> StateAtomMap.to_list
    |> List.map (fun ((state, _), _) -> state)
    (* get the unique elements *)
    |> List.sort_uniq compare

  (** Get all the atoms for a GKAT automaton*)
  let atoms_of (automaton: t): Atom.t list = 
    let p_bools = automaton.p_bools in 
    Atom.to_list p_bools |> power_list 
    (* Converts each sublist into set *)
    |> List.map Atom.of_list

  (** Get all the live states of a input automaton*)
  let get_live_states (automaton: t): StateSet.t =  
    let atoms = atoms_of automaton in 
    let trans_map = automaton.trans_map in
    (** Non-trivial states of the automaton*)
    let states = get_states automaton in 
    (** a state is a live state when _any_ of its transition is live *)
    let is_live_rec (is_live_opt: state -> bool option) (s: state) = 
      List.exists (fun atom -> 
        match StateAtomMap.find_opt  (s, atom) trans_map with 
        | None -> false
        | Some Accept -> true 
        | Some To (s', _) -> 
          (* recurse *)
          match is_live_opt s' with
          (* infinite loop encountered *)
          | None -> false 
          | Some res -> res
      ) atoms in
    (** pairs where the first is state, the second is whether that state is live*)
    let is_live_map = compute_map is_live_rec states in 
    (** Keep all the states that is live *)
    List.filter_map 
      (fun (s, s_is_live) -> if s_is_live then Some s else None) 
      is_live_map
    |> StateSet.of_list

  (** Normalize will remove all the non-live state in the automaton*)
  let normalize (automaton: t): t = 
    let live_states = get_live_states automaton in 
    {automaton with 
      trans_map = 
        StateAtomMap.filter 
          (fun (s, _) _ -> StateSet.mem s live_states) 
          automaton.trans_map}

end