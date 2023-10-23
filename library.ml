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



open Format

module Parser = struct
  let is_lower_case c = 'a' <= c && c <= 'z'

  let is_upper_case c = 'A' <= c && c <= 'Z'

  let is_alpha c = is_lower_case c || is_upper_case c

  let is_blank c = String.contains " \012\n\r\t" c

  let explode s = List.of_seq (String.to_seq s)

  let implode ls = String.of_seq (List.to_seq ls)

  let readlines (file : string) : string =
    let fp = open_in file in
    let rec loop () =
      match input_line fp with
      | s -> s ^ "\n" ^ loop ()
      | exception End_of_file -> ""
    in
    let res = loop () in
    let () = close_in fp in
    res

  (* end of util functions *)

  (* parser combinators *)

  type 'a parser = char list -> ('a * char list) option

  let parse (p : 'a parser) (s : string) : ('a * char list) option =
    p (explode s)

  let pure (x : 'a) : 'a parser = fun ls -> Some (x, ls)

  let fail : 'a parser = fun ls -> None

  let bind (p : 'a parser) (q : 'a -> 'b parser) : 'b parser =
   fun ls ->
    match p ls with
    | Some (a, ls) -> q a ls
    | None -> None

  let ( >>= ) = bind

  let ( let* ) = bind

  let read : char parser =
   fun ls ->
    match ls with
    | x :: ls -> Some (x, ls)
    | _ -> None

  let satisfy (f : char -> bool) : char parser =
   fun ls ->
    match ls with
    | x :: ls ->
      if f x then
        Some (x, ls)
      else
        None
    | _ -> None

  let char (c : char) : char parser = satisfy (fun x -> x = c)

  let seq (p1 : 'a parser) (p2 : 'b parser) : 'b parser =
   fun ls ->
    match p1 ls with
    | Some (_, ls) -> p2 ls
    | None -> None

  let ( >> ) = seq

  let seq' (p1 : 'a parser) (p2 : 'b parser) : 'a parser =
   fun ls ->
    match p1 ls with
    | Some (x, ls) -> (
      match p2 ls with
      | Some (_, ls) -> Some (x, ls)
      | None -> None)
    | None -> None

  let ( << ) = seq'

  let alt (p1 : 'a parser) (p2 : 'a parser) : 'a parser =
   fun ls ->
    match p1 ls with
    | Some (x, ls) -> Some (x, ls)
    | None -> p2 ls

  let ( <|> ) = alt

  let choice (ps : 'a parser list) : 'a parser =
    match ps with
    | p :: ps -> List.fold_left (fun acc p -> acc <|> p) p ps
    | _ -> fail

  let map (p : 'a parser) (f : 'a -> 'b) : 'b parser =
   fun ls ->
    match p ls with
    | Some (a, ls) -> Some (f a, ls)
    | None -> None

  let ( >|= ) = map

  let ( >| ) p c = map p (fun _ -> c)

  let rec many (p : 'a parser) : 'a list parser =
   fun ls ->
    match p ls with
    | Some (x, ls) -> (
      match many p ls with
      | Some (xs, ls) -> Some (x :: xs, ls)
      | None -> Some ([ x ], ls))
    | None -> Some ([], ls)

  let whitespace : unit parser =
   fun ls ->
    match ls with
    | c :: ls ->
      if String.contains " \012\n\r\t" c then
        Some ((), ls)
      else
        None
    | _ -> None

  let ws : unit parser = many whitespace >| ()

  let literal (s : string) : unit parser =
   fun ls ->
    let cs = explode s in
    let rec loop cs ls =
      match (cs, ls) with
      | [], _ -> Some ((), ls)
      | c :: cs, x :: xs ->
        if x = c then
          loop cs xs
        else
          None
      | _ -> None
    in
    loop cs ls

  let keyword (s : string) : unit parser = literal s >> ws >| ()
end

module KATerm = struct
  open Parser

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
  
let rec unique (list: 'a list): 'a list =
  match list with
  | [] -> []
  | x::xs -> let u = unique xs in
    if not (List.mem x u) then x::u
    else x::u
    
(*Add element which is not duuplicate into alist*) (** optimize function! check membership function List.mem, library**)
let rec union_list (lst1: 'a list) (lst2: 'a list): 'a list = 
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


(** do i need a helper function to find head p for r?**)
(**linearization function returning a list of tuples of the head p of regular expression r1 (p,r1)**)
let rec linearization (r: 'a kleene): ('a * 'a kleene) list = match r with
  | Zero-> []
  | One -> []
  | Value p -> [(p,One)]
  | Union(r1,r2) -> union_list (linearization r1) (linearization r2) (** how do i find the head p**)
  (** four concatnation cases**)
  | Conc(Value p,r') -> [(p,r')]
  | Conc((Star(r1)),r2) -> union_list (concList_tuple(concList_tuple (linearization r1) (Star(r1))) (r2)) (linearization r2)
  | Conc((Union(r1,r2)),r3) -> union_list (linearization (Conc(r1,r2))) (linearization (Conc(r2,r3))) 
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
