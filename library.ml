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



let rec optimize r = match r  with
| Zero -> Zero
| One -> One
| Value p -> Value p
| Union (Zero, r2) -> optimize r2
| Union (r1,Zero) -> optimize r1
| Union (r1,r2) -> let r1= optimize r1 in let r2= optimize r2 in 
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



let rec tos s = match s with
  | Zero -> "0"
  | One -> "1"
  | Value(r1) -> String.make 1 r1
  | Union(r1,r2) -> "(" ^ tos(r1) ^ "+" ^ tos(r2) ^ ")"
  | Conc(r1, r2) -> "(" ^ tos(r1) ^ "^" ^ tos(r2) ^")"
  | Star (Value(r1)) ->"(" ^ String.make 1 r1 ^ ")" ^"*"
  | Star r1 -> "(" ^ tos r1 ^ ")" ^ "*"

