(** a kleene datatype, represents regular expressions **)
type 'a kleene =
  | Zero
  | One
  | Value of 'a
  | Union of 'a kleene * 'a kleene
  | Conc of 'a kleene * 'a kleene
  | Star of 'a kleene

(**examples to type check /tests**)
let example1 = Union(Conc(Conc(One,Value('a')),Value('b')), Value('a'))

let example2 = Star(Conc(Star(Conc(Value('a'),Value('b'))),Value('c')))

let example3= Conc(Value '1', Value '8')

let example4 = Union((Conc(Value 'a',Star(Zero))),One)
let example5= Union(Value 'c',Union(Conc(One, Conc(Union(Zero,Value 'a'), Value 'b')), Star(One)))
(**helper funtion to change string to a kleene and kleene to string!**)


(** epsilon funtion to capture whether the regular expression r contains the empty word**)
let rec epsilon (r: 'a kleene): bool = match r with
  | One -> true
  | Zero -> false
  | Value p -> false
  | Union(r1,r2) -> epsilon r1 || epsilon r2
  | Conc(r1,r2) -> epsilon r1 && epsilon r2
  | Star(r1) -> true

  let rec optimize r = match r  with
  | Zero -> Zero
  | One -> One
  | Value p -> Value p
  | Union (Zero, r2) -> optimize r2
  | Union (r1,Zero) -> optimize r1
  | Union (r1,r2) -> let r1 = optimize r1 in let r2 = optimize r2 in 
    (match r1,r2 with 
    | Zero,r2 -> r2
    | r1,Zero -> r1
    | r1,r2 -> if r1 == r2 then r1 else Union(r1,r2) )
  | Conc(Zero,r2) -> Zero
  | Conc(r1,Zero) -> Zero
  | Conc(One,r2) -> optimize r2
  | Conc (r1,One) -> optimize r1
  | Conc (r1,r2) -> let r1= optimize r1 in let r2= optimize r2 in 
    (match (r1,r2) with 
    | Zero,r2 -> Zero
    | r1,Zero -> Zero
    | One , r2 -> r2
    | r1, One -> r1
    | r1, r2 -> if r1 == Star(r1) && r2 == Star(r1) then Star(r1) else Conc(r1,r2) ) (**checking for r*r*->r* **)
  | Star(One) -> One
  | Star (Zero) -> One
  | Star (r1) -> let r1=optimize r1 in 
  match r1 with
  | One -> One
  | Zero -> Zero
  | r1 -> Star(r1)


(** Brzozowski's derivative of regular expression r respect to a symbol p **)
let rec deriv p r = match r with
  | Zero -> Zero
  | One -> Zero
  | Value(p') -> if p' == p then One else Zero
  | Union(r1,r2) -> Union(deriv p r1, deriv p r2)
  | Conc(r1,r2) -> 
      if (epsilon(r1) = true) then Union(Conc(deriv p r1, r2), deriv p r2)
      else Conc(deriv p r1, r2)
  | Star(r1) -> Conc(deriv p r1, Star(r1))

  let string_to_list str =
    let rec convert_to_list index acc =
      if index < 0 then acc
      else convert_to_list (index - 1)(str.[index]::acc)
    in
    convert_to_list(String.length str - 1) []
  
  
  
  let rec reverse_list (lst: char list):char list = 
    match lst with
    | [] -> []
    | hd :: tl -> (reverse_list tl) @ [hd]
    
  
  let rec deriv_word_list w r =
    match w with
    | [] -> r (**base case**)
    | p::rest -> deriv p (deriv_word_list rest r)
  
  let rec deriv_w w r = 
    let  w_rev = reverse_list (string_to_list(w)) in 
    deriv_word_list w_rev r


(** Check if there is duplicate when adding an element or adding a list, true if nothing duplicate, false if duplicate **)
let rec duplicateChecker list value= match list with
 |[] -> true
 |x1::xs -> if (x1==value) then false 
  else duplicateChecker xs value

(*Add element which is not duuplicate into alist*)
let rec listDuplicateChecker alist blist = 
match blist with
|[] -> alist
|x1::xs -> 
match x1 with
| Zero -> 
  if (duplicateChecker alist Zero) then listDuplicateChecker (alist@[Zero]) xs
else listDuplicateChecker alist xs
| One -> 
  if (duplicateChecker alist One) then listDuplicateChecker (alist@[One]) xs
else listDuplicateChecker alist xs
| Value(p) -> 
  if (duplicateChecker alist (Value(p))) then listDuplicateChecker (alist@[Value(p)]) xs
else listDuplicateChecker alist xs
| Union(r1,r2) -> 
  if (duplicateChecker alist (Union(r1,r2))) then listDuplicateChecker (alist@[Union(r1,r2)]) xs
else listDuplicateChecker alist xs
| Conc(r1,r2) -> 
  if (duplicateChecker alist (Conc(r1,r2))) then listDuplicateChecker (alist@[Conc(r1,r2)]) xs
  else listDuplicateChecker alist xs
| Star(r1) -> 
  if (duplicateChecker alist (Star(r1))) then listDuplicateChecker (alist@[Star(r1)]) xs
else listDuplicateChecker alist xs
  


let rec conc_list (list_r1: 'a kleene list ) (r2: 'a kleene): 'a kleene list= 
match list_r1 with
|[] -> []
|r1::rs -> (Conc(r1,r2))::(conc_list rs r2)

(*partial derivative function*)

let rec partialDeriv (re: 'a kleene ) (p: 'a): 'a kleene list = match re with
  | Zero -> []
  | One -> []
  | Value(p') -> if p' == p then [One] else []
  | Union(r1,r2) -> listDuplicateChecker (partialDeriv r1 p) (partialDeriv r2 p)
  | Conc(r1,r2) -> 
      if (epsilon r1 = true) then listDuplicateChecker (conc_list (partialDeriv r1 p) r2) (partialDeriv r2 p)
      else
     conc_list (partialDeriv r1 p) r2 
  | Star(r1) -> conc_list (partialDeriv r1 p) (Star r1)

  
(**
let rec partialDeriv re p = match re with
  | Zero -> []
  | One -> []
  | Value(p') -> if p' == p then [One] else []
  | Union(r1,r2) -> 
    let d1 = partialDeriv r1 p in let d2= partialDeriv r2 p in listDuplicateChecker d1 d2 
  | Conc(r1,r2) -> 
      if (epsilon(r1) = true) then listDuplicateChecker(conc_list(partialDeriv r1 p, r2), partialDeriv r2 p)
      else 
        conc_list(partialDeriv r1 p, [r2])
  | Star(r1) -> conc_list(partialDeriv r1 p, Star(r1))

**)



let rec tos s = match s with
  | Zero -> "0"
  | One -> "1"
  | Value(r1) -> String.make 1 r1
  | Union(r1,r2) -> "(" ^ tos(r1) ^ "+" ^ tos(r2) ^ ")"
  | Conc(r1, r2) -> "(" ^ tos(r1) ^ "^" ^ tos(r2) ^")"
  | Star (Value(r1)) ->"(" ^ String.make 1 r1 ^ ")" ^"*"
  | Star r1 -> "(" ^ tos r1 ^ ")" ^ "*"

  let pprint (exp: char kleene) = 
    (*helper method, takes a expression, output the string, 
       and **the precedence of the outer most expression** *)
    let rec helper (exp: char kleene): string * int = 
      match exp with
      | One -> ("1", 0)
      | Zero -> ("0", 0)
      | Value(c) -> (String.make 1 c, 0)
      | Star(r) -> 
        let (str, precedence) = helper r in 
        if precedence <= 0 then (str^"*", 0) else ("("^str^")*", 0)
      | Conc(r1, r2) ->
        let (str1, precedence1) = helper r1 in 
        let (str2, precedence2) = helper r2 in 
        let str1' = if precedence1 <= 1 then str1 else "("^str1^")" in 
        let str2' = if precedence2 < 1 then str2 else "("^str2^")" in 
        (str1' ^ " " ^ str2', 1)
      | Union(r1, r2) ->
        let (str1, precedence1) = helper r1 in 
        let (str2, precedence2) = helper r2 in 
        let str1' = if precedence1 <= 2 then str1 else "("^str1^")" in 
        let str2' = if precedence2 < 2 then str2 else "("^str2^")" in 
        (str1' ^ " + " ^ str2', 2) 
    in
    let (str, _) = helper exp in str 


