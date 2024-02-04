(** a kleene datatype, represents regular expressions **)
(* type 'a test=
  | Zero       
  | One
  | Prim of 'a
  | And of 'a test * 'a test
  | Or of 'a test * 'a test
  | Not of 'a test *)

type katI =
  | Zero
  | One
  | Value of string
  | PBool of string
  | Union of katI *  katI
  | Conc of  katI * katI
  | Star of katI
  | Not of katI

type katSort =
  |BExp
  |NBExp     (*Not a boolean expression*)

type kat= katI * katSort
let zero:kat = Zero,BExp
let union(e1:kat) (e2: kat):kat=
    match (e1,e2) with
    |(Zero,_),_-> e2
    |_,(Zero,_)-> e1
    | (k1,BExp),(k2,BExp) -> Union(k1,k2),BExp
    |(k1,_),(k2,_)-> Union(k1,k2),NBExp


let not(e1:kat):kat=
  match e1 with
  |(k1,BExp)-> Not k1,BExp 
  |_-> raise (Invalid_argument "Invalid argument to not")
  
(**examples to type check /tests**)
module StringSet = Set.Make(String)
let rec pBoolOf(k:katI):StringSet.t=
  match k with
  |One -> StringSet.empty
  |PBool b-> StringSet.singleton b
  |Conc(a,b)-> StringSet.union (pBoolOf a) (pBoolOf b)
  |Not(b) -> pBoolOf b
  (*TODO: Just to surpress the warning for now, remove when finished*)
  | _ -> failwith "Unimplemented"
