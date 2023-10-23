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

  | Union (r1,r2) -> let r1 = optimize r1 in let r2 = optimize r2 in 
    (match r1,r2 with 
    (*r1 + (r3 + r4) => (r1 + r3) + r4*)
    | r1, Union (r3, r4) -> 
        Union (Union (optimize r1, optimize r3), optimize r4)
    (*0 + r => r *)
    | Zero,r2 -> r2
    (*r + 0 => r *)
    | r1,Zero -> r1
    (*r + r => r *)
    | r1,r2 -> if r1 == r2 then r1 else Union(r1,r2) )

  | Conc (r1,r2) -> let r1= optimize r1 in let r2= optimize r2 in 
    (match (r1,r2) with 
    (*r1 . (r3 . r4) => (r1 . r3) . r4 *)
    | r1, Conc (r3, r4) -> 
      Conc (Conc (optimize r1, optimize r3), optimize r4)
    (*0 . r => r *)
    | Zero,r2 -> Zero
    (*r . 0 => r *)
    | r1,Zero -> Zero
    (*1 . r => r *)
    | One , r2 -> r2
    (*r . 1 => r *)
    | r1, One -> r1
    (* r* r* => r* *)
    | Star(r1), Star(r2) -> if r1 = r2 then Star(r1) else Conc(r1,r2)
    (* no optimization *)
    | r1, r2 -> Conc(r1,r2) )

  | Star (r1) -> let r1=optimize r1 in 
    (match r1 with
    (* 1* => 1 *)
    | One -> One
    (* 0* => 0 *)
    | Zero -> Zero
    (* no optimization *)
    | r1 -> Star(r1))


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
let rec duplicateChecker list value = match list with
 |[] -> true
 |x1::xs -> if (x1==value) then false 
  else duplicateChecker xs value

(*Add element which is not duuplicate into alist*) (** optimize function! check membership function List.mem, library**)
let rec union_list (r1_list: 'a kleene list) (r2_list: 'a kleene list): 'a kleene list = 
match r2_list with
|[] -> r1_list
|x1::xs -> 
match x1 with
| Zero -> 
  if (List.mem Zero r1_list ) then union_list (r1_list@[Zero]) xs
else union_list r1_list xs
| One -> 
  if (List.mem One r1_list ) then union_list (r1_list@[One]) xs
else union_list r1_list xs
| Value p -> 
  if (List.mem (Value p) r1_list ) then union_list (r1_list@[Value p ]) xs
else union_list r1_list xs
| Union(r1,r2) -> 
  if (List.mem (Union(r1,r2)) r1_list ) then union_list (r1_list@[Union(r1,r2)]) xs
else union_list r1_list xs
| Conc(r1,r2) -> 
  if (List.mem (Conc(r1,r2)) r1_list ) then union_list (r1_list@[Conc(r1,r2)]) xs
  else union_list r1_list xs
| Star(r1) -> 
  if (List.mem (Star(r1)) r1_list ) then union_list (r1_list@[Star(r1)]) xs
else union_list r1_list xs
  


let rec conc_list (list_r1: 'a kleene list ) (r2: 'a kleene): 'a kleene list= 
match list_r1 with
|[] -> []
|r1::rs -> (Conc(r1,r2))::(conc_list rs r2)

(*partial derivative function*)

let rec partialDeriv (re: 'a kleene ) (p: 'a): 'a kleene list = match re with
  | Zero -> []
  | One -> []
  | Value(p') -> if p' == p then [One] else []
  | Union(r1,r2) -> union_list (partialDeriv r1 p) (partialDeriv r2 p)
  | Conc(r1,r2) -> 
      if (epsilon r1 = true) then union_list (conc_list (partialDeriv r1 p) r2) (partialDeriv r2 p)
      else
     conc_list (partialDeriv r1 p) r2 
  | Star(r1) -> conc_list (partialDeriv r1 p) (Star r1)

(**partial derivatives extension to words**)

let rec partialDeriv_word_list (u: 'a list) (r: 'a kleene): 'a kleene list = 
  match u with
        | [] -> [r]
        | p::rest -> let l = partialDeriv_word_list rest r in
          let l' = List.map (fun x -> partialDeriv x  p ) l in
            List.fold_right union_list l' []




(** checking for duplicates and creating union of a set of linear regular expressions**)


let rec unionList_tuple (r1_linear: ('a * 'b kleene) list) (r2_linear: ('a * 'b kleene) list): ('a * 'b kleene) list  = 
match r2_linear with
|[] -> r1_linear
|(p,r)::rs -> 
if (List.mem (p,r) r1_linear == false ) then unionList_tuple (r1_linear@[(p,r)]) rs else unionList_tuple r1_linear rs

let rec concList_tuple (r_linear: ('a kleene * 'b kleene) list) (r: 'a kleene): ('a kleene * 'b kleene) list = 
  match r_linear with
  | []->[]
  |(r1,r2)::rs -> (Conc(r1,r),Conc(r2,r))::concList_tuple rs r



(** do i need a helper function to find head p for r?**)
(**linearization function returning a list of tuples of the head p of regular expression r1 (p,r1)**)
let rec linearization (r: 'a kleene): ('a kleene* 'b kleene) list = match r with
  | Zero-> []
  | One -> []
  | Value p -> [(Value p,One)]
  | Union(r1,r2) -> unionList_tuple (linearization r1) (linearization r2) (** how do i find the head p**)
  (** four concatnation cases**)
  | Conc(Value p,r') -> [(Value p,r')]
  | Conc((Star(r1)),r2) -> unionList_tuple (concList_tuple(concList_tuple (linearization r1) (Star(r1))) (r2)) (linearization r2)
  | Conc((Union(r1,r2)),r3) -> unionList_tuple (linearization (Conc(r1,r2))) (linearization (Conc(r2,r3))) 
  | Conc(Conc(r1,r2),r3) -> linearization (Conc(r1,Conc(r2,r3)))
  | Conc(One,r') -> linearization r'
  | Conc(Zero,r') -> []
  | Star(r') -> concList_tuple (linearization r') (Star(r'))

(** **)


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

  (* pretty printing with equational theory *)
  let eqpprint (exp: char kleene) = pprint (optimize exp)
