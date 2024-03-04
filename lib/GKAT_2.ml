open KAT_Set

type bExp = 
  |PBool of string*bExp*bExp (* confused here*)

type gkat =
  | Pact of string
  | Seq of kat*kat
  | Test of bExp
  | While of bExp*kat


