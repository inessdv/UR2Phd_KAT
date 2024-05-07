open KAT_Set
open KA_equiv.KAT_Set.Print

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

module Print1 = struct
  let gpprint (exp : gkat): string =
    let kat_exp = from_GKAT_to_KAT exp in
      pprint kat_exp

end

module Print2 = struct

  (*Printer helper function for bexp expressions*)
  let rec pprint_bexp (bexp : bExp) : string * int =
    match bexp with
    | Zero -> ("0", 0)
    | One -> ("1", 0)
    | PBool b -> (b, 0)
    | Or (b1, b2) ->
      let str1, prec1 = pprint_bexp b1 in
      let str2, prec2 = pprint_bexp b2 in
      let str1' = if prec1 > 2 then "(" ^ str1 ^ ")" else str1 in
      let str2' = if prec2 > 2 then "(" ^ str2 ^ ")" else str2 in
      (str1' ^ " or " ^ str2', 3)
    | And (b1, b2) ->
      let str1, prec1 = pprint_bexp b1 in
      let str2, prec2 = pprint_bexp b2 in
      let str1' = if prec1 > 2 then "(" ^ str1 ^ ")" else str1 in
      let str2' = if prec2 > 2 then "(" ^ str2 ^ ")" else str2 in
      (str1' ^ " and " ^ str2', 3)
    | Not b ->
      let str, prec = pprint_bexp b in
      if prec > 0 then ("~(" ^ str ^ ")", 1) else ("~" ^ str, 1)

      (*pretty printer for gkat*)
  let pprint (exp : gkat) =
    let rec helper (exp : gkat) : string * int =
      match exp with
      | Pact p -> (p, 0)
      | Seq (e1, e2) ->
        let s1, p1 = helper e1 in
        let s2, p2 = helper e2 in
        let s1' = if p1 < 2 then s1 else "(" ^ s1 ^ ")" in
        let s2' = if p2 < 2 then s2 else "(" ^ s2 ^ ")" in
        (s1' ^ " * " ^ s2', 2)
      | If (b, e1, e2) ->
        let bs, _ = pprint_bexp b in
        let s1, p1 = helper e1 in
        let s2, p2 = helper e2 in
        let s1' = if p1 <= 3 then s1 else "(" ^ s1 ^ ")" in
        let s2' = if p2 < 3 then s2 else "(" ^ s2 ^ ")" in
        ("if " ^ bs ^ " then " ^ s1' ^ " else " ^ s2', 3)
      | Test b ->
        let bs, _ = pprint_bexp b in
        (bs, 1)
      | While (b, e) ->
        let bs, _ = pprint_bexp b in
        let s, p = helper e in
        let s' = if p <= 1 then s else "(" ^ s ^ ")" in
        ("while " ^ bs ^ " do " ^ s' ^ " done", 1)
    in

    let str, _ = helper exp in
    str
end



(*
  let pprint (exp : gkat) =
    (*helper method, takes a expression, output the string,
          and **the precedence of the outer most expression** *)
    let rec helper (exp : gkat) : string * int =
      match exp with
      | Pact p -> (p, 0)
      | Seq (exp1,exp2) -> 
        let str1, precedence1 = helper exp1 in
          let str2, precedence2 = helper exp2 in
          let str1' = if precedence1 <= 2 then str1 else "(" ^ str1 ^ ")" in
          let str2' = if precedence2 < 2 then str2 else "(" ^ str2 ^ ")" in
          (str1' ^ "*" ^ str2', 2)
      | If (bexp, exp1, exp2) -> 
        let str1, precedence1 = helper exp1 in
          let str2, precedence2 = helper exp2 in
          let str3, precedence3 = 
            match bexp with
            | Zero -> ("0", 0)
            | One -> ("1", 0)
            | PBool b -> (b, 0)
            | Or (bexp1, bexp2) -> 
              let b1, precedence1 = helper (from_BE_to_KAT bexp1) in
              let b2, precedence2 = helper (from_BE_to_KAT bexp2) in
              let b1' = if precedence1 <= 2 then str1 else "(" ^ b1 ^ ")" in
              let b2' = if precedence2 < 2 then str2 else "(" ^ b2 ^ ")" in
              (b1' ^ " or " ^ b2', 3)
            | And (bexp1, bexp2)->
              let b1, precedence1 = helper (from_BE_to_KAT bexp1) in
              let b2, precedence2 = helper (from_BE_to_KAT bexp2) in
              let b1' = if precedence1 <= 2 then str1 else "(" ^ b1 ^ ")" in
              let b2' = if precedence2 < 2 then str2 else "(" ^ b2 ^ ")" in
              (b1' ^ " and " ^ b2', 3)
            | Not bexp1 -> 
              let str, precedence = helper (from_BE_to_KAT bexp1) in
              if precedence <= 1 then ("~" ^ str, 1) else ("~(" ^ str ^ ")", 1)
        in
          let str1' = if precedence1 <= 3 then str1 else "(" ^ str1 ^ ")" in
          let str2' = if precedence2 < 3 then str2 else "(" ^ str2 ^ ")" in
          (str1' ^ " + " ^str3^ str2', 3)
      | Test bexp -> 
        let str, precedence3 = 
            match bexp with
            | Zero -> ("0", 0)
            | One -> ("1", 0)
            | PBool b -> (b, 0)
            | Or (bexp1, bexp2) -> 
              let b1, precedence1 = helper (from_BE_to_KAT bexp1) in
              let b2, precedence2 = helper (from_BE_to_KAT bexp2) in
              let b1' = if precedence1 <= 2 then b1 else "(" ^ b1 ^ ")" in
              let b2' = if precedence2 < 2 then b2 else "(" ^ b2 ^ ")" in
              (b1' ^ " or " ^ b2', 3)
            | And (bexp1, bexp2)->
              let b1, precedence1 = helper (from_BE_to_KAT bexp1) in
              let b2, precedence2 = helper (from_BE_to_KAT bexp2) in
              let b1' = if precedence1 <= 2 then b1 else "(" ^ b1 ^ ")" in
              let b2' = if precedence2 < 2 then b2 else "(" ^ b2 ^ ")" in
              (b1' ^ " and " ^ b2', 3)
            | Not bexp1 -> 
              let str, precedence = helper (from_BE_to_KAT bexp1) in
              if precedence <= 1 then ("~" ^ str, 1) else ("~(" ^ str ^ ")", 1) in
              ( str, 1)
      | While (bexp, exp) -> failwith ""
            in failwith ""
    (*let pprint_sum (expset : KATSet.t) : string =
      let exp_list = KATSet.to_list expset in
      (*I can do pipeline here*)
      let string_list = List.map pprint exp_list in
      String.concat " " string_list 
    in *)
  end *)