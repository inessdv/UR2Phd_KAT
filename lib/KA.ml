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

module KAParser = struct
  open Parser.Combinators

  let symbol_parser : char kleene parser =
    let* s = satisfy (fun c -> is_alpha c ) in
    pure (Value s) << ws
  
  let one_parser : char kleene parser = 
    let* _ = keyword "1" in 
    pure One

  let zero_parser : char kleene parser = 
    let* _ = keyword "0" in 
    pure Zero

  let rec min_term_parser () =
    let* _ = pure () in
    choice
      [ symbol_parser
      ; one_parser
      ; zero_parser
      ; keyword "(" >> term_parser () << keyword ")"
      ]

  and star_parser () = 
    let* e = min_term_parser () in
    let* _ = keyword "*" <|> keyword "^*" in
    pure (Star e)

  and min_term_star_pareser () = star_parser () <|> min_term_parser () 
    
  and conc_parser () : char kleene parser = 
    let* e = min_term_star_pareser () in
    let opr () = 
          (*conc explicitly using "@" symbol*)
          (let* _ = keyword "@" in
          let* e = min_term_star_pareser () in
          pure ((fun e1 e2 -> Conc (e1, e2)), e)) 
          <|>
          (*conc implicitly without using any operators*)
          (let* e = min_term_star_pareser () in
          pure ((fun e1 e2 -> Conc (e1, e2)), e)) 
    in
    let* es = many (opr ()) in
    pure (List.fold_left (fun acc (f, e) -> f acc e) e es)

  and union_parser () =
    let* e = conc_parser () in
    let opr () = (let* _ = keyword "+" in
           let* e = conc_parser () in
           pure ((fun e1 e2 -> Union (e1, e2)), e))
    in
    let* es = many (opr ()) in
    pure (List.fold_left (fun acc (f, e) -> f acc e) e es)

  and term_parser () =
    let* _ = pure () in
    union_parser ()

  let parse_reg (s : string) : char kleene option =
    match parse (ws >> term_parser ()) s with
    |Some (r,[]) -> Some r
    |_ -> None
end

(** end of parser**)


(** epsilon funtion to capture whether the regular expression r contains the empty word**)
let rec epsilon (r: 'a kleene): bool = match r with
  | One -> true
  | Zero -> false
  | Value _ -> false
  | Union(r1,r2) -> epsilon r1 || epsilon r2
  | Conc(r1,r2) -> epsilon r1 && epsilon r2
  | Star _ -> true

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
    | Zero, _ -> Zero
    (*r . 0 => r *)
    | _ ,Zero -> Zero
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
    
  
  (* let rec deriv_word_list w r =
    match w with
    | [] -> r (*** base case**)
    | p::rest -> deriv p (deriv_word_list rest r)
  
  let deriv_w w r = 
    let  w_rev = reverse_list (string_to_list(w)) in 
    deriv_word_list w_rev r *)


(** Check if there is duplicate when adding an element or adding a list, true if nothing duplicate, false if duplicate **)
let rec duplicateChecker list value = match list with
 |[] -> true
 |x1::xs -> if (x1==value) then false 
  else duplicateChecker xs value
  
let rec unique (list: 'a list): 'a list =
  match list with
  | [] -> []
  | x::xs -> let u = unique xs in
    if not (List.mem x u) then x::u
    else u
    
(*Add element which is not duuplicate into alist*) (** optimize function! check membership function List.mem, library**)
let union_list (lst1: 'a list) (lst2: 'a list): 'a list = 
unique lst1@lst2

  


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

let rec concList_tuple (r_linear: ('a * 'a kleene) list) (r: 'a kleene): ('a * 'a kleene) list = 
  match r_linear with
  | []->[]
  |(p,r2)::rs -> (p,Conc(r2,r))::concList_tuple rs r


(*** do i need a helper function to find head p for r?**)
(*** linearization function returning a list of tuples of the head p of regular expression r1 (p,r1)**)
let rec linearization (r: 'a kleene): ('a * 'a kleene) list = match r with
  | Zero-> []
  | One -> []
  | Value p -> [(p,One)]
  | Union(r1,r2) -> union_list (linearization r1) (linearization r2) (*** how do i find the head p**)
  (* four concatnation cases**)
  | Conc(Value p,r') -> [(p,r')]
  | Conc((Star(r1)),r2) -> union_list (concList_tuple(concList_tuple (linearization r1) (Star(r1))) (r2)) (linearization r2)
  | Conc((Union(r1,r2)),r3) -> union_list (linearization (Conc(r1,r2))) (linearization (Conc(r2,r3))) 
  | Conc(Conc(r1,r2),r3) -> linearization (Conc(r1,Conc(r2,r3)))
  | Conc(One, r') -> linearization r'
  | Conc(Zero, _) -> []
  | Star(r') -> concList_tuple (linearization r') (Star(r'))

(** The following functions wil help define the decision procedure
    hd(RE) , der_p(RE) , der_ext(P(RE)), ep(RE) , derivatives(R1,R2)
**)
(** Function hd(r)to find head**)

let hd (r: 'a kleene): 'a list =
  let s = linearization(r) in
    unique (List.map fst s) (** list of hd's (p) of f(r)**)

(** Function der_p(RE) -> P(RE) to find **)
let der_p (p: 'a)(r: 'a kleene): 'a kleene list = 
  let s = linearization(r) in
    let t = (fun x -> fst x == p) in
    unique (List.map snd (List.filter t (s))) (** list of unique r' from f(r)**)


(** Function eps(P(RE)) checking for empty word**)
let eps (rlist: 'a kleene list): 'a kleene =
  let e = List.filter (fun x -> x == true) (List.map epsilon rlist) in
    if e == [] then One else Zero



(** Function der_ext(P(RE)) ????**)
let der_ext (p: 'a )(rlist: 'a kleene list): 'a kleene list =
  let s = unique (List.flatten(List.map linearization rlist)) in
    let t = (fun x -> fst x == p) in
      unique (List.map snd (List.filter t (s)))

(** Function hd_ext, extension of hd to lists of RE**)
let hd_ext (rlist: 'a kleene list): 'a list =
  unique (List.map fst (List.flatten (List.map linearization rlist)))
  
(*Helper function allHead, derOfList for derivative*)
let rec allHead(re:('a kleene list * 'a kleene list)list):'a list=
  match re with
  |[]->[]
  |(r1,r2)::rest-> (hd_ext r1 @ hd_ext r2)@allHead rest 
  
let rec derOfList (re: 'a kleene list)(p:'a list): 'a kleene list=
match p with
|[]->[]
|x1::xs-> der_ext x1 re @ derOfList re xs


(* let rec derivativeHelper (re:('a kleene list * 'a kleene list)list) (heads:'a list):'a kleene list=
  match re with
  |[]->[]
  |(r1,r2)::rest-> (derOfList r1 heads @ derOfList r2 heads)@ derivativeHelper rest heads *)
let rec derivativeHelper (re:('a kleene list * 'a kleene list)list) (heads:'a):('a kleene list * 'a kleene list)list= 
  match re with
  |[]-> []
  |(r1,r2)::rs->(der_ext heads r1, der_ext heads r2)::derivativeHelper rs heads

let rec derHelper  (re:('a kleene list * 'a kleene list)list) (heads:'a list):(('a kleene list * 'a kleene list)list)list= 
  match heads with
  |[]-> []
  |x1::xs-> derivativeHelper re x1 :: derHelper re xs

(** INPUT: 'a kleene list * 'a kleene list
     listOUTPUT TYPE? ('a kleene list x a' kleene list) list**)
let derivative (re:('a kleene list * 'a kleene list)list):(('a kleene list * 'a kleene list)list)list=
  let heads=unique (allHead re) in  unique (derHelper re heads)

let derivatives (re_pair: 'a kleene list * 'a kleene list): ('a kleene list * 'a kleene list) list =
  match re_pair with
  | (r1_set,r2_set) -> let heads = union_list (hd_ext r1_set) (hd_ext r2_set) in
                        List.map (fun x -> (List.map der_ext x r1_set) * (List.map der_ext x r1_set)) heads




(**
    PRINTING METHODS
**)
let rec checkEmptyHelper (re:'a kleene list):bool=
match re with 
|[]->false 
|r1::rs-> if epsilon r1 then true
else checkEmptyHelper rs


let rec checkEmpty (re:('a kleene list * 'a kleene list)list):bool=
match re with
|[]->true
|(r1,r2)::rs-> if checkEmptyHelper r1 != checkEmptyHelper r2 then false
else checkEmpty rs


let rec equiv (re:((('a kleene list * 'a kleene list)list)list) * ((('a kleene list * 'a kleene list)list)list)):bool=
match re with
|([],_)-> true
|(r1,r2)->let regex=List.concat r1 in 
if checkEmpty regex==false then false
else 
let der=derivative regex in
let r2= unique (r1@r2)in
equiv (der,r2)



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


let derivativeTest1=Conc(Star(Value('a')),Value('a'))
let derivativeTest2=Conc(Star(Value('a')),Value('b'))
let ex1= [([derivativeTest1],[derivativeTest2])]