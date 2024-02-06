(** a kleene datatype, represents regular expressions **)
(* type 'a test=
  | Zero       
  | One
  | Prim of 'a
  | And of 'a test * 'a test
  | Or of 'a test * 'a test
  | Not of 'a test *)

  (* type katI =
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
 *)

type kat =
  | Zero
  | One
  | Value of string
  | PBool of string
  | Union of kat *  kat
  | Conc of  kat * kat
  | Star of kat
  | Not of kat

type katI= kat * bool  (*True when expression is boolean, false when expression is KAT*)
let zero = (Zero,true) (*is this a constructor?*)

let union(e1:katI) (e2: katI):katI=
    match (e1,e2) with
    |(Zero,_),_-> e2
    |_,(Zero,_)-> e1
    | (k1,true),(k2,true) -> Union(k1,k2),true
    |(k1,_),(k2,_)-> Union(k1,k2),false

let conc(e1:katI) (e2:katI):katI= (** would it be better to use (kat*bool) pairs as input???**)
  match (e1,e2) with
    |(Zero,true),_-> Zero,true
    |_,(Zero,true)-> Zero,true
    |(Zero,false),_-> Zero,false
    |_,(Zero,false)->Zero,false
    |(One,_),_-> e2
    |_,(One,_)-> e1
    |(k1,true),(k2,true) -> Conc(k1,k2),true        (*if k1==One and k2==One then One,true  else Zero,true*)
    |(k1,false),(k2,false) -> Conc(k1,k2),false
    |(_,_),(_,_) -> raise (Invalid_argument "conc only works in same type expression")


let not ((exp, expIsBExp): kat * bool) = 
    if expIsBExp then (Not exp, true) else raise (Invalid_argument "negation only takes boolean expressions")

let star((exp, expIsBExp): kat * bool)=
if expIsBExp==false then (Star(exp), false) else raise (Invalid_argument "star only takes KAT expressions")

module KATSet = Set.Make(struct
type t = kat (**would this be katI???**)
let compare = compare
end)

module KATISet = Set.Make(struct
type t = katI (**would this be katI???**)
let compare = compare
end)
  
(**examples to type check /tests**)
module StringSet = Set.Make(String)
let rec pBoolOf((exp, expIsBExp): kat * bool):StringSet.t =
  if expIsBExp then 
    match exp with           (*At*)
    |One -> StringSet.empty          
    |PBool b-> StringSet.singleton b
    |Conc(a,b)-> StringSet.union (pBoolOf (a,true)) (pBoolOf (b,true))      
    |Union(a,b)-> StringSet.union (pBoolOf (a,true)) (pBoolOf (b,true))           
    |Not(b) -> pBoolOf (b,true)
    (*TODO: Just to surpress the warning for now, remove when finished*)
    | _ -> failwith "We want boolean expressions but KA expression is given"
else raise (Invalid_argument "pBool only takes bool expressions")


let rec pBoolOf(exp:katI):StringSet.t =
  match exp with           (*At*)
  |(_,false) -> StringSet.empty (** or error message?**)
  |(bExp,true)-> 
    match bExp with
    |One -> StringSet.empty          
    |PBool b-> StringSet.singleton b
    |Conc(a,b)-> StringSet.union (pBoolOf (a,true)) (pBoolOf (b,true))     
    |Union(a,b)-> StringSet.union (pBoolOf (a,true)) (pBoolOf (b,true))           
    |Not(b) -> pBoolOf (b,true)
    |_ -> StringSet.empty


(** new type of set, set of string set to be produce power sets**)
module SStringSet=Set.Make(StringSet)

(** function to get the atoms of the primitive bools through power set**)
let atOf(primitive_boolset:StringSet.t):SStringSet.t =
  StringSet.fold (fun x ps -> SStringSet.fold 
    (fun ss-> SStringSet.add (StringSet.add x ss)) ps ps) primitive_boolset 
    (SStringSet.singleton StringSet.empty)



(**similar question to pBool**)
let rec epsilon ((exp, expIsBExp): kat * bool): bool = 
if (expIsBExp== false) then 
match exp with
| Zero -> false
| One -> true
| Value _ -> false
| Union(a,b) -> epsilon (a,false) || epsilon (b,false)
| Conc(a,b) -> epsilon (a,false) && epsilon (b,false)
| Star _ -> true
| _ -> false
else raise (Invalid_argument "epsilon only takes KA expressions")

(** empty word for KAT expressions**)
let eps (sum: KATISet.t): bool =
  KATISet.exists (fun exp -> epsilon exp) sum


(* existence of atom in R, set of KAT**)
let existance ((exp,expIsBExp):kat * bool) (rSet:KATISet.t): bool = (*??**)
  if expIsBExp then KATISet.mem (exp,true) rSet else raise (Invalid_argument "epsilon only takes Bexp expressions")

(** function to extract p?
**)

(** derivative function: we need a and p and a KAT Exp
let deriv (a:kat(* bexp atom **))(p:kat (*primitive action **))(exp:kat): KATSet.t =
**)

(*examples*)

let example1=StringSet.of_list ["b";"c";"d"]
let example1= atOf example1 

let example2=SStringSet.to_list