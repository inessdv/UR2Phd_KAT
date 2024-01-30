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

  let symbol_parser : string kleene parser =
    let* char_list = many1 (satisfy (fun c -> is_alpha c )) in
    let str = implode char_list in
    pure (Value str) << ws
  
  let one_parser : string kleene parser = 
    let* _ = keyword "1" in 
    pure One

  let zero_parser : string kleene parser = 
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
    
  and conc_parser () : string kleene parser = 
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

  let parse_reg (s : string) : string kleene option =
    match parse (ws >> term_parser ()) s with
    |Some (r,[]) -> Some r
    |_ -> None
  let to_string (s) : 'a kleene=
  match s with 
  |Some(a)->a 
  |None -> Zero
end

(** end of parser**)


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


module Equiv = struct

  (** epsilon funtion to capture whether the regular expression r contains the empty word**)
  let rec epsilon (r: 'a kleene): bool = match r with
  | One -> true
  | Zero -> false
  | Value _ -> false
  | Union(r1,r2) -> epsilon r1 || epsilon r2
  | Conc(r1,r2) -> epsilon r1 && epsilon r2
  | Star _ -> true

  (** Set of Kleene algebra term, where each symbol is a string*)
  module KASet = Set.Make(struct
    type t = string kleene
    (*uses the default polymorphic compare,
       this only compare the syntax tree, 
       it is not the order in KA*)
    let compare = compare
  end)

  module PDerivPairSet = Set.Make (struct
    (* set of pairs of partical derivitives*)
    type t = KASet.t * KASet.t
    let compare = compare
  end) 

  (** Set of string*)
  module StringSet = Set.Make(String)

  (** A map from string*)
  module StringMap = Map.Make(String)

  (** The linear form of a expression, which is string mapped to as set of KA expressions*)
  type linearForm = KASet.t StringMap.t

  (**Monad structure on Set, bind function
      maps function onto the set, and flatten the set*)
  let (let*) (s: KASet.t) (f: string kleene -> KASet.t): KASet.t = 
    let sList = KASet.elements s in 
    let unflattened = List.map f sList in 
    List.fold_left KASet.union KASet.empty unflattened
  
    (**Monad structure on Set, return function.
        Simply creates the singleton set*)
  let return (elem: string kleene): KASet.t = 
    KASet.singleton elem

  (** concatenate a regular expression to every regular expressions in the linear form*)
  let concLinearForm (r_linear: linearForm) (r: string kleene): linearForm = 
    StringMap.map (fun derivs -> 
      KASet.map (fun deriv -> Conc (deriv, r)) derivs) 
    r_linear
    
  (** Create the union of two linear form, 
      this will merge all the deriviative of the same head
      this corresponds to the sum of two linear forms*)
  let unionLinearForm (lin1: linearForm) (lin2: linearForm): linearForm = 
    StringMap.union 
      (* combine two KA set with union, when their hd are the same*)
      (fun _ s1 s2 -> Some (KASet.union s1 s2))
      lin1 lin2

  (*** do i need a helper function to find head p for r?**)
  (** linearization function returning a list of tuples of the head p of regular expression r1 (p,r1)**)
  let rec linearization (r: string kleene): linearForm = match r with
    | Zero-> StringMap.empty
    | One -> StringMap.empty
    | Value p -> StringMap.singleton p (KASet.singleton One)
    | Union(r1,r2) -> unionLinearForm (linearization r1) (linearization r2)
    (* four concatnation cases**)
    | Conc(Value p,r') -> StringMap.singleton p (KASet.singleton r')
    | Conc((Star(r1)),r2) -> 
      unionLinearForm 
        (concLinearForm (concLinearForm (linearization r1) (Star r1)) r2)
        (linearization r2)
    | Conc((Union(r1,r2)),r3) -> unionLinearForm (linearization (Conc(r1,r2))) (linearization (Conc(r2,r3))) 
    | Conc(Conc(r1,r2),r3) -> linearization (Conc(r1,Conc(r2,r3)))
    | Conc(One, r') -> linearization r'
    | Conc(Zero, _) -> StringMap.empty
    | Star(r') -> concLinearForm (linearization r') (Star(r'))

  (*** The following functions will help define the decision procedure
      hd(RE) , der_p(RE) , der_ext(P(RE)), ep(RE) , derivatives(R1,R2)
  **)
  (** Function hd(r) to find head**)
  let hd (r: string kleene): StringSet.t =
    let lin_r = linearization r in 
    (*convert the keys into set*)
    StringSet.of_list (List.map fst (StringMap.to_list lin_r))

  (** Function der_p(RE) -> P(RE) to find **)
  let deriv (p: string) (r: string kleene): KASet.t = 
    StringMap.find p (linearization r)


  (** Function eps(P(RE)) checking for empty word**)
  let eps (sum: KASet.t): bool =
    KASet.exists (fun r -> epsilon r) sum

  (* Python Notation
    deriv_sum(p, sum) = {der for der in deriv(p, r) for r in sum} 
  *)
  (** Function der_ext(P(RE)) ????**)
  let deriv_sum (p: string)(sum: KASet.t): KASet.t =
    let* r = sum in 
    let* der = deriv p r in 
    return der

  (** Function hd_ext, extension of hd to lists of RE**)
  let hd_sum (sum: KASet.t): StringSet.t = 
    let sumList = KASet.to_list sum in 
    (* union each head of term in the sum*)
    List.fold_left StringSet.union StringSet.empty (List.map hd sumList)



  (** Function derivatives(R1,R2), findes derivatives of a pair of kleene sets**)
  let derivatives (re_pair: KASet.t * KASet.t): PDerivPairSet.t =
    match re_pair with
    |(r1_set,r2_set)-> let heads = StringSet.union (hd_sum r1_set) (hd_sum r2_set) in
      StringSet.fold (fun x acc -> PDerivPairSet.add (deriv_sum x r1_set, deriv_sum x r2_set) acc) heads
      PDerivPairSet.empty

(*Equiv function*)
  let rec equiv (r: PDerivPairSet.t * PDerivPairSet.t): bool =
    match r with
    |(pair_1,pair_2) -> (*pair 1 holds P(RE) and pair 2 holds  the pairs already tested*)
      if PDerivPairSet.is_empty pair_1 then true else
        let r = PDerivPairSet.choose pair_1 in
          match r with
          |(r1,r2) -> if eps(r1) != eps(r2) then false else
            let h' = PDerivPairSet.add r pair_2 in
              let dervs = derivatives(r1,r2) in
              let s' = PDerivPairSet.diff dervs h' in
              let s = PDerivPairSet.remove r pair_1 in
              equiv((PDerivPairSet.union s s'),h')
end
  
(**
    PRINTING METHODS
**)

module Print = struct

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

end
