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

let example3= Conc(Value 1, Value 8)

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
  | if p' == p then One else
  | if p' != p then Zero else One
  | Union(a, b) -> Union(deriv p a, deriv p b)
  | Conc(a,b) -> 
      if (epsilon(a) = 1) then Union(Conc(deriv p a, b), deriv p b)
      else Conc(deriv p a, deriv p b)
  | Star(a) -> Conc(deriv p a, Star(a))





