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

(**helper funtion to change string to a kleene and kleene to string!**)


(** epsilon funtion to capture whether the regular expression r contains the empty word**)
let rec epsilon (r: 'a kleene): bool = match r with
  | One -> true
  | Zero -> false
  | Value p -> false
  | Union(a, b) -> epsilon a || epsilon b
  | Conc(a,b) -> epsilon a && epsilon b
  | Star(a) -> true


(** Brzozowski's derivative of regular expression r respect to a symbol p **)
let rec deriv p r = match r with
  | Zero -> Zero
  | One -> Zero
  | Value(p') -> if p' == p then One else Zero
  | Union(a, b) -> Union(deriv p a, deriv p b)
  | Conc(a,b) -> 
      if (epsilon(a) = true) then Union(Conc(deriv p a, b), deriv p b)
      else Conc(deriv p a, b)
  | Star(a) -> Conc(deriv p a, Star(a))

let rec optimize r= match r  with
| Zero -> Zero
| One -> One
| Value p -> Value p
| Union (Zero, b) -> optimize b
| Union (b,Zero) -> optimize b
| Union (a,b) -> Union(optimize a, optimize b) (*let optimize a, b*)
| Conc(Zero,b) -> Zero
| Conc(b,Zero) -> Zero
| Conc(One,b) -> optimize b
| Conc (b,One) -> optimize b
| Conc (a,b) -> Conc(optimize a, optimize b)
| Star(One) -> One
| Star (Zero) -> One
| Star (b) -> Star (optimize b)
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
  | Zero -> "ZERO "
  | One -> "ONE "
  | Value(a) -> String.make 1 a
  | Union(a, b) -> "(" ^ tos(a) ^ "+" ^ tos(b) ^ ")"
  | Conc(a, b) -> "(" ^ tos(a) ^ "^" ^ tos(b) ^")"
  | Star (Value(a)) ->"(" ^ String.make 1 a ^ ")" ^"*"
  | Star r -> "(" ^ tos r ^ ")" ^ "*"

