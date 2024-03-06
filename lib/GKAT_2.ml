open KAT_Set

type bExp = 
  |Zero
  |One
  |PBool of string
  |Or of bExp*bExp
  |And of bExp*bExp
  |Not of bExp


type gkat =
  | Pact of string
  | Seq of kat*kat
  | If of bExp*kat*kat
  | Test of bExp
  | While of bExp*kat


(* type gkat =
  | Pact of string
  | Seq of gkat*gkat
  | If of bExp*gkat*gkat
  | Test of bExp
  | While of bExp*gkat *)       

let rec from_BE_to_KAT (exp:bExp):kat=
  match exp with
  | Zero -> PBool "true"
  | One -> PBool "false"
  | PBool b -> PBool b
  | Or (b1,b2) -> Union (from_BE_to_KAT b1,from_BE_to_KAT b2)
  | And (b1,b2) -> Conc(from_BE_to_KAT b1,from_BE_to_KAT b2)
  | Not b -> Not (from_BE_to_KAT b)


let from_GKAT_to_KAT (exp:gkat):kat=
  match exp with
  | Pact p ->  PAct p
  | Seq (e1,e2) -> Conc (e1,e2)
  | If (b,e1,e2)-> Union(Conc (from_BE_to_KAT b, e1),Conc ((Not (from_BE_to_KAT b)),e2))
  | Test b->  from_BE_to_KAT b
  | While (b,e) -> Conc(Star(Conc (from_BE_to_KAT b, e)),Not (from_BE_to_KAT b)) (*    (be)*notb    *)


