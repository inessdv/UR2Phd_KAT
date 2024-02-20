open Common

module Trans = struct
  (** Defines the transition structure of GKAT automaton *)

  (* Possible results of GKAT automata transitions
      Rejection is implicit, by not present in the transition map*)
  type res = Accept | To of State.t * pAct

  let pprint_res (res : res) : string =
    match res with Accept -> "Accept" | To (s, p) -> State.pprint s ^ ", " ^ p

  type map = res AtomMap.t StateMap.t

  let atom_map_of (s : State.t) (trans_map : map) : res AtomMap.t option =
    StateMap.find_opt s trans_map

  let res_of (s : State.t) (at : Atom.t) (trans_map : map) : res option =
    let ( let* ) = Option.bind in
    let* at_map = atom_map_of s trans_map in
    AtomMap.find_opt at at_map

  (** Convert a transition map into a flattened list*)
  let map_to_flat_list (trans_map : map) : (State.t * Atom.t * res) list =
    let ( let* ) l f = List.concat_map f l in
    let* s, at_map = StateMap.to_list trans_map in
    let* at, res = AtomMap.to_list at_map in
    [ (s, at, res) ]

  (** A reasonable equality for transition maps *)
  let map_equal (map1 : map) (map2 : map) : bool =
    StateMap.equal (AtomMap.equal ( = )) map1 map2

  (** Convert a list into a transiton map*)
  let map_of_list (lst : (State.t * (Atom.t * res) list) list) : map =
    lst
    |> List.map (fun (s, at_list) -> (s, AtomMap.of_list at_list))
    |> StateMap.of_list

  let map_of_flat_list (lst : (State.t * Atom.t * res) list) : map =
    List.fold_left
      (fun acc (s, at, res) ->
        StateMap.update s
          (fun at_map_opt ->
            match at_map_opt with
            | None -> Option.some @@ AtomMap.singleton at res
            | Some at_map -> Option.some @@ AtomMap.add at res at_map)
          acc)
      StateMap.empty lst

  let pprint_map_flat (trans_map : map) : string =
    trans_map |> map_to_flat_list
    (* print each transition *)
    |> List.map (fun (s, at, res) ->
           "s" ^ string_of_int s ^ ", " ^ Atom.pprint at ^ " ----> "
           ^ pprint_res res)
    |> String.concat "\n"

  let pprint_map (trans_map : map) : string =
    StateMap.to_list trans_map
    |> List.map (fun (s, at_map) ->
           State.pprint s ^ "--> \n"
           ^ (AtomMap.to_list at_map
             |> List.map (fun (at, res) ->
                    Atom.pprint at ^ " ----> " ^ pprint_res res)
             |> String.concat "\n"))
    |> String.concat "\n"
end

module Automaton = struct
  type t = { start : State.t; trans_map : Trans.map }
  (** GKAT automaton
      all the "non-trivial" states of the automaton are keys of the transMap,
      other states are implicitly transitioned to reject,
      regardless of the input atom.
      
      We do not check wether the transMap is valid, 
      it is up to the user to only use the primitive tests avalible in pBools*)

  let pprint (automata : t) : string =
    "{ NOTE: transition to rejection is implicit\nstart state:"
    ^ State.pprint automata.start
    ^ "\n"
    ^ Trans.pprint_map automata.trans_map
    ^ "\n}"

  (** Get all the states __with transitions__ 
      
    states that always reject will be omitted*)
  let get_nontrivial_states (automaton : t) : State.t list =
    automaton.trans_map |> StateMap.to_list
    |> List.map (fun (state, _) -> state)

  (** Get all the live states of a input automaton*)
  let get_live_states (automaton : t) : StateSet.t =
    let trans_map = automaton.trans_map in
    (* Non-trivial states of the automaton*)
    let states = get_nontrivial_states automaton in
    (* a state is a live state when _any_ of its transition is live *)
    let is_live_rec (is_live_opt : State.t -> bool option) (s : State.t) =
      match StateMap.find_opt s trans_map with
      | None -> false
      | Some at_map ->
          AtomMap.to_list at_map
          (* a state is live when there exists a transition that is live *)
          |> List.exists (fun (_at, res) ->
                 match res with
                 | Trans.Accept -> true
                 | Trans.To (s, _) -> (
                     match is_live_opt s with
                     (* infinite loop, not live *)
                     | None -> false
                     | Some is_live -> is_live))
    in
    (* pairs where the first is state, the second is whether that state is live*)
    let is_live_map = compute_map_rec is_live_rec states in
    (* Keep all the states that is live *)
    List.filter_map
      (fun (s, s_is_live) -> if s_is_live then Some s else None)
      is_live_map
    |> StateSet.of_list

  (** Normalize will remove all the transition to dead state*)
  let normalize (automaton : t) : t =
    let live_states = get_live_states automaton in
    let atom_map_normalize at_map =
      AtomMap.filter
        (fun _at res ->
          match res with
          | Trans.To (s, _) -> StateSet.mem s live_states
          | _ -> true)
        at_map
    in
    {
      start = automaton.start;
      trans_map =
        automaton.trans_map
        (* remove empty atom map*)
        |> StateMap.filter_map (fun _ at_map ->
               let at_map = atom_map_normalize at_map in
               if AtomMap.is_empty at_map then None else Some at_map);
    }

  (** Check all the possible transition results from states s1 and s2, with all atoms.
     if any result doesn't match, then return nothing,
      otherwise, return a list of states to check*)
  let check_res ((s1, a1) : State.t * t) ((s2, a2) : State.t * t) :
      (State.t * State.t) list option =
    let ( let* ) = Option.bind in
    let* at_map1 = StateMap.find_opt s1 a1.trans_map in
    let* at_map2 = StateMap.find_opt s2 a2.trans_map in
    let atoms1 = AtomMap.keys at_map1 in
    let atoms2 = AtomMap.keys at_map2 in
    (* if there exists some atom that rejects in map1 and not in map2, then fail,
       otherwise get the pair*)
    if atoms1 <> atoms2 then None
    else
      AtomSet.to_list atoms1
      (*We can use `find` in this step, because `atoms` is the key of these two `at_map`.*)
      |> list_filter_map_m_opt (fun atom ->
             match (AtomMap.find atom at_map1, AtomMap.find atom at_map2) with
             (* success, but do not produce additional states to check*)
             | Accept, Accept -> Some None
             (* success, produce additional states to check *)
             | To (s1', p1), To (s2', p2) ->
                 if p1 = p2 then Some (Some (s1', s2')) else None
             (* fail *)
             | _ -> None)

  (** Check whether two automaton are bisimular *)
  let bisim (a1 : t) (a2 : t) : bool =
    (* __IMPURE__, each run will return different result,
       use with caution.
       generate a map that maps each state to the union find elem *)
    let make_elem_map automaton =
      get_nontrivial_states automaton
      |> List.map (fun s -> (s, UnionFind.make s))
      |> StateMap.of_list
    in
    (* CANNOT inline, `make_elem_map` is not pure *)
    let to_elem_map1 = make_elem_map a1 in
    let to_elem_map2 = make_elem_map a2 in
    (*to_elem will return None only when the state is always rejecting*)
    let to_elem1_opt s = StateMap.find_opt s to_elem_map1 in
    let to_elem2_opt s = StateMap.find_opt s to_elem_map2 in

    let todo = Queue.create () in
    Queue.push (a1.start, a2.start) todo;

    let rec bisim_help () : bool =
      match Queue.take_opt todo with
      (* If the todo is empty, then they are bisimular *)
      | None -> true
      | Some (s1, s2) -> (
          let s1_elem_opt = to_elem1_opt s1 in
          let s2_elem_opt = to_elem2_opt s2 in
          (*return is none when the state is always rejecting*)
          match (s1_elem_opt, s2_elem_opt) with
          | None, None -> bisim_help ()
          | Some _, None -> false
          | None, Some _ -> false
          | Some s1_elem, Some s2_elem -> (
              if UnionFind.eq s1_elem s2_elem (* already equal *) then true
              else
                match check_res (s1, a1) (s2, a2) with
                (* mismatch exists in the results of (s1, s2) *)
                | None -> false
                (* mismatch doesn't exist, have states `to_check` to check*)
                | Some to_check ->
                    (* mark s1 and s2 as equal *)
                    ignore @@ UnionFind.union s1_elem s2_elem;
                    (* remove all the states that has already been marked equal*)
                    let to_check =
                      List.filter
                        (fun (s1', s2') ->
                          not @@ uf_eq_opt (to_elem1_opt s1') (to_elem2_opt s2'))
                        to_check
                    in
                    queue_push_list todo to_check;
                    bisim_help ()))
    in
    bisim_help ()

  (** Check equivalence, normolize and check bisimularity*)
  let equiv (a1 : t) (a2 : t) : bool =
    let a1_n = normalize a1 in
    let a2_n = normalize a2 in
    bisim a1_n a2_n
end
