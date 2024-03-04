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




