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