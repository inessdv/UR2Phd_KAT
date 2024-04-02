open KAT_Set

type bExp =
  | Zero
  | One
  | PBool of string
  | Or of bExp * bExp
  | And of bExp * bExp
  | Not of bExp

type gkat =
  | Pact of string
  | Seq of gkat * gkat
  | If of bExp * gkat * gkat
  | Test of bExp
  | While of bExp * gkat

let rec from_BE_to_KAT (exp : bExp) : kat =
  match exp with
  | Zero -> Zero
  | One -> One
  | PBool b -> PBool b
  | Or (b1, b2) -> Union (from_BE_to_KAT b1, from_BE_to_KAT b2)
  | And (b1, b2) -> Conc (from_BE_to_KAT b1, from_BE_to_KAT b2)
  | Not b -> Not (from_BE_to_KAT b)

let rec from_GKAT_to_KAT (exp : gkat) : kat =
  match exp with
  | Pact p -> PAct p
  | Seq (e1, e2) -> Conc (from_GKAT_to_KAT e1, from_GKAT_to_KAT e2)
  | If (b, e1, e2) ->
      Union
        ( Conc (from_BE_to_KAT b, from_GKAT_to_KAT e1),
          Conc (Not (from_BE_to_KAT b), from_GKAT_to_KAT e2) )
  | Test b -> from_BE_to_KAT b
  | While (b, e) ->
      Conc
        ( Star (Conc (from_BE_to_KAT b, from_GKAT_to_KAT e)),
          Not (from_BE_to_KAT b) )
(*(be)*notb*)

let gKat_equiv (exp1 : gkat) (exp2 : gkat) : bool =
  let e1 = from_GKAT_to_KAT exp1 in
  let e2 = from_GKAT_to_KAT exp2 in
  equiv e1 e2
