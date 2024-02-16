open Common

module Automaton = struct

  (** States for GKAT automaton *)
  type state = int64
  module StateSet = Set.Make(Int64)
  module StatePairSet = Set.Make(struct
    type t = state * state 
    let compare = compare
  end)
  (* Possible results of GKAT automata transitions
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
    (* Non-trivial states of the automaton*)
    let states = get_states automaton in 
    (* a state is a live state when _any_ of its transition is live *)
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
    (* pairs where the first is state, the second is whether that state is live*)
    let is_live_map = compute_map is_live_rec states in 
    (* Keep all the states that is live *)
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

  (** Return the next results of s1 and s2 for each atom as a list of pairs*)
  let next_res_pairs ((s1, a1): state * t) ((s2, a2): state * t): (transRes option * transRes option) list = 
    if a1.p_bools <> a2.p_bools then raise (Invalid_argument "cannot compare two automaton with different pBools");
    (*since *)
    let atoms = atoms_of a1 in
    let trans_map1 = a1.trans_map in 
    let trans_map2 = a2.trans_map in
    List.map 
      (fun atom -> (StateAtomMap.find_opt (s1, atom) trans_map1, 
                    StateAtomMap.find_opt (s2, atom) trans_map2)) 
      atoms

  (** check one pair of trans results, 
      return True if success and nothing left to check
      return False if there is a mismatch
      return a pair of state the results matched, and need to check the pair of states next*)
  let check_res_pair ((res1, res2): transRes option * transRes option): (bool, (state * state)) Either.t = 
    match res1, res2 with
    | None, None -> Either.left true 
    | Some Accept, Some Accept -> Either.left true
    | Some To (s1, p1), Some To (s2, p2) -> 
      if p1 = p2 then Either.right (s1, s2) else Either.left false 
    | _ -> Either.left false

  (** Check all the possible transition results from states s1 and s2, with all atoms.
     if any result doesn't match, then return nothing,
      otherwise, return a list of states to check*)
  let check_res ((s1, a1): state * t) ((s2, a2): state * t): (state * state) list option = 
    let res_pairs = next_res_pairs (s1, a1) (s2, a2) in 
    let checks = List.map check_res_pair res_pairs in 
    if List.mem (Either.left false) checks 
      (* failed *)
      then None 
      else Option.some @@ 
        List.filter_map 
        (fun check -> match check with Either.Left _ -> None | Either.Right s_pair-> Some s_pair) 
        checks

  (** Check whether two automaton are bisimular *)
  let bisim (a1: t) (a2: t): bool =
    let todo = Queue.create () in 
    Queue.push (a1.start, a2.start) todo;
    let rec bisim_help (): bool = 
      match Queue.take_opt todo with 
      (* If the todo is empty, then they are bisimular *)
      | None -> true
      | Some (s1, s2) -> 
        let s1_u = UnionFind.make s1 in 
        let s2_u = UnionFind.make s2 in 
        if UnionFind.eq s1_u s2_u 
          (* already equal *)
          then true
          else 
            match check_res (s1, a1) (s2, a2) with 
            | None -> false
            | Some to_check -> 
              ignore @@ UnionFind.union s1_u s2_u; 
              queue_push_list todo to_check;
              bisim_help ()
    in  
    bisim_help ()

  (** Check equivalence, normolize and check bisimularity*)
  let equiv (a1: t) (a2: t): bool = 
    let a1_n = normalize a1 in 
    let a2_n = normalize a2 in 
    bisim a1_n a2_n

end