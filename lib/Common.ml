type pBool = string
(** Primitive Booleans or Primitive Tests*)

type pAct = string
(** Primitive Actions*)

module PBoolSet = Set.Make (String)

module Atom = Set.Make (String)
(** Atom is a set of pBools
    all the pBools that is in the set is regarded as positive
    and ones that are not in the set is regarded as negative*)

module AtomSet = Set.Make (Atom)

(** Like powerset but for list
    All the elements in the resulting sub lists maintains their original order

    the function will enumerate all the sublist starting with current head,
    and once that doesn't start with the current head.*)
let rec power_list (l : 'a list) : 'a list list =
  match l with
  | [] -> [ [] ]
  | h :: tail ->
      let power_tail = power_list tail in
      (power_tail |> List.map (fun sub_tail -> h :: sub_tail)) @ power_tail

(** Given a "recursive function" that compute the one result,
    compute all of the result for each 'a, and arrange in a list,
    the result is in the order of `inp`.

    The first argument of `comp_one_rec` is itself for recursion,
    except the first argument can return None, indicating a finite recursion.
    This function will cache the result of each computation to speed up recursion*)
let compute_map (comp_one_rec : ('a -> 'b option) -> 'a -> 'b) (inps : 'a list)
    : ('a * 'b) list =
  (* the value is marked None, when we are in the process of computing *)
  let memo_tbl : ('a, 'b option) Hashtbl.t =
    Hashtbl.create (List.length inps)
  in
  let rec comp_one_opt inp =
    match Hashtbl.find_opt memo_tbl inp with
    | Some res -> res
    | None ->
        (* Mark that we are currently computing results for `inp`*)
        let () = Hashtbl.add memo_tbl inp None in
        (* recursion *)
        let res = comp_one_rec comp_one_opt inp in
        let () = Hashtbl.replace memo_tbl inp (Some res) in
        Some res
  in
  (* function to compute one result *)
  let compute_one = comp_one_rec comp_one_opt in
  List.map (fun inp -> (inp, compute_one inp)) inps

(** __IMPURE__, like all the queue functions
    Convert a list into a queue*)
let queue_push_list (queue : 'a Queue.t) (l : 'a list) : unit =
  List.iter (fun elem -> Queue.push elem queue) l

(** Helper function to compare two union find elements in options*)
let uf_eq_opt (elem1_opt : 'a UnionFind.elem option)
    (elem2_opt : 'a UnionFind.elem option) =
  match (elem1_opt, elem2_opt) with
  | None, None -> true
  | Some elem1, Some elem2 -> UnionFind.eq elem1 elem2
  | _ -> false
