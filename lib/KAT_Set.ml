open Common

(*Defining necessary types and modules*)

type kat =
  | Zero
  | One
  | PAct of string
  | PBool of string
  | Union of kat * kat
  | Conc of kat * kat
  | Star of kat
  | Not of kat

module KATSet = Set.Make (struct
  type t = kat

  let compare = compare
end)

module AtPactMap = Map.Make (struct
  type t = Atom.t * string (*change to Atom.t*)

  let compare = compare
end)

module SStringSet = Set.Make (Atom)
(** new type of set, set of string set to be produce power sets**)

type linearForm = KATSet.t AtPactMap.t
(** The linear form of a expression, which is a (StringSet (atoms), String(pact)) mapped to as set of KAT expressions*)

module StringMap = Map.Make (String)
(** A map from string*)

module DerMapSet = Set.Make (struct
  type t = linearForm

  let compare = compare
end)

type atPact = Atom.t * string

module AtPactSet = Set.Make (struct
  type t = Atom.t * string

  let compare = compare
end)

module PDerivPairSet = Set.Make (struct
  (* set of pairs of partial derivitives*)
  type t = KATSet.t * KATSet.t

  let compare = compare
end)

module Print = struct
  let pprint (exp : kat) =
    (*helper method, takes a expression, output the string,
        and **the precedence of the outer most expression** *)
    let rec helper (exp : kat) : string * int =
      match exp with
      | One -> ("1", 0)
      | Zero -> ("0", 0)
      | PAct c -> (c, 0)
      | PBool c -> (c, 0)
      | Star r ->
          let str, precedence = helper r in
          if precedence <= 0 then (str ^ "*", 0) else ("(" ^ str ^ ")*", 0)
      | Not r ->
          let str, precedence = helper r in
          if precedence <= 1 then ("~" ^ str, 1) else ("~(" ^ str ^ ")", 1)
      | Conc (r1, r2) ->
          let str1, precedence1 = helper r1 in
          let str2, precedence2 = helper r2 in
          let str1' = if precedence1 <= 2 then str1 else "(" ^ str1 ^ ")" in
          let str2' = if precedence2 < 2 then str2 else "(" ^ str2 ^ ")" in
          (str1' ^ " " ^ str2', 2)
      | Union (r1, r2) ->
          let str1, precedence1 = helper r1 in
          let str2, precedence2 = helper r2 in
          let str1' = if precedence1 <= 3 then str1 else "(" ^ str1 ^ ")" in
          let str2' = if precedence2 < 3 then str2 else "(" ^ str2 ^ ")" in
          (str1' ^ " + " ^ str2', 3)
    in
    let str, _ = helper exp in
    str

  let pprint_sum (expset : KATSet.t) : string =
    let exp_list = KATSet.to_list expset in
    (*I can do pipeline here*)
    let string_list = List.map pprint exp_list in
    String.concat " " string_list

  let pprint_pder (pair: PDerivPairSet.t): string =
    let pair_list = PDerivPairSet.to_list pair in
    let string_list = List.map (fun (x,y) -> print_string (pprint_sum x); pprint_sum y;) pair_list in
    String.concat " " string_list

  let pprint_atoms (atoms: SStringSet.t): string =
    let atom_list = SStringSet.to_list atoms in
    let atom_str = List.map (fun atom -> Atom.pprint atom) atom_list in
    String.concat "\n" atom_str

  let pprint_linear_form (linear: linearForm) : string = 
    let linear_list = AtPactMap.to_list linear in
      let linear_str = List.map (fun ((atom,pact), kat) -> Atom.pprint atom ^ ", " ^ pact ^ " -> " ^ pprint_sum kat) linear_list in 
      String.concat "\n" linear_str 
end

type katI =
  kat * bool (*True when expression is boolean, false when expression is KAT*)

let pAct p = (PAct p, false)
let pBool b = (PBool b, true)
let one = (One, true)
let zero = (Zero, true)

let union (e1 : katI) (e2 : katI) : katI =
  match (e1, e2) with
  | (Zero, _), _ -> e2
  | _, (Zero, _) -> e1
  | (k1, true), (k2, true) -> (Union (k1, k2), true)
  | (k1, _), (k2, _) -> (Union (k1, k2), false)

let conc (e1 : katI) (e2 : katI) : katI =
  match (e1, e2) with
  | (Zero, _), _ -> (Zero, true)
  | _, (Zero, _) -> (Zero, true)
  | (One, _), _ -> e2
  | _, (One, _) -> e1
  | (k1, true), (k2, true) ->
      ( Conc (k1, k2),
        true (*if k1==One and k2==One then One,true  else Zero,true*) )
  | (k1, false), (k2, false) -> (Conc (k1, k2), false)
  (*TODO: please fix this, conc can concatnate two types of expression*)
  | (k1, _), (k2, _) -> (Conc (k1, k2), false)

let not_N ((exp, expIsBExp) : kat * bool) =
  if expIsBExp then
    match exp with
    | One -> (Zero, true)
    | Zero -> (One, true)
    | _ -> (Not exp, true)
  else
    raise
      (Invalid_argument
         ("negation applied to non-boolean expression: " ^ Print.pprint exp))

let star ((exp, expIsBExp) : kat * bool) =
  if expIsBExp == false then (Star exp, false) else (One, true)

module KATISet = Set.Make (struct
  type t = katI

  let compare = compare
end)

let rec pBoolOf (exp : katI) : Atom.t =
  match exp with
  (*At*)
  | _, false -> Atom.empty
  | bExp, true -> (
      match bExp with
      | One -> Atom.empty
      | PBool b -> Atom.singleton b
      | Conc (a, b) -> Atom.union (pBoolOf (a, true)) (pBoolOf (b, true))
      | Union (a, b) -> Atom.union (pBoolOf (a, true)) (pBoolOf (b, true))
      | Not b -> pBoolOf (b, true)
      | _ -> Atom.empty)

(** function to get the atoms of the primitive bools through power set**)
let atOf (primitive_boolset : Atom.t) : SStringSet.t = 
  Atom.fold
    (fun x ps ->
      SStringSet.fold (fun ss -> SStringSet.add (Atom.add x ss)) ps ps) (*CHECK**)
    primitive_boolset
    (SStringSet.singleton Atom.empty)

(** empty word for KAT expressions**)
let rec epsilon (atom : Atom.t) (exp : kat) : bool =
  match exp with
  | Zero -> false
  | One -> true (*DOUBLE CHECK!!!!!!!!!*)
  | PAct _ -> false
  | PBool b -> Atom.mem b atom (*if b <= atom, then b must be in the atom *)
  | Union (a, b) -> epsilon atom a || epsilon atom b
  | Conc (a, b) -> epsilon atom a && epsilon atom b
  | Star _ -> true
  | Not a -> not (epsilon atom a)

(** empty word for KATset**)
let epsilon_sum (atom : Atom.t) (sum : KATSet.t) : bool =
  KATSet.exists (fun exp -> epsilon atom exp) sum

(** linearization function **)
let unionLinearForm (lin1 : linearForm) (lin2 : linearForm) : linearForm =
  AtPactMap.union
    (* combine two KAT sets with union, when their hds are the same*)
      (fun _ s1 s2 -> Some (KATSet.union s1 s2))
    lin1 lin2

let conc_alg (e1 : kat) (e2 : kat) : kat =
  match (e1, e2) with
  | One, _ -> e2
  | _, One -> e1
  | Zero, _ -> Zero
  | _, Zero -> Zero
  | _, _ -> Conc (e1, e2)

let concLinearForm (r_linear : linearForm) (r : kat) : linearForm =
  AtPactMap.map
    (fun derivs ->
      (* when concatenating with 1, elimination of map of the 1,
          we could also eliminate 0, as we'd get an empty set!!!*)
      KATSet.map (fun deriv -> conc_alg deriv r) derivs)
    r_linear

let rec mapMakerHelper (mapper : linearForm) (at : SStringSet.t) (p : string) :
    linearForm =
  if SStringSet.is_empty at then mapper
  else
    let atom = SStringSet.min_elt at in
    let combine = (atom, p) in
    mapMakerHelper
      (AtPactMap.add combine (KATSet.singleton One) mapper)
      (SStringSet.remove atom at)
      p

(* mapMaker produce all atoms*p map to One *)
let mapMaker (at : SStringSet.t) (p : string) : linearForm =
  let mapper = AtPactMap.empty in
  mapMakerHelper mapper at p

let atomExists (e2 : linearForm) (e1 : kat) : linearForm =
  let e2List = AtPactMap.to_list e2 in
  AtPactMap.of_list (List.filter (fun ((a, _), _) -> epsilon a e1) e2List)

let getAtomsof (exp : kat) : SStringSet.t =
  let primitives = pBoolOf (exp, true) in
  atOf primitives

let linearization (exp : kat) : linearForm =
  let rec linearization_helper (at : SStringSet.t) (exp : kat) : linearForm =
    match exp with
    | PBool _ -> AtPactMap.empty
    | PAct p -> mapMaker at p (* map p to each atom and then each to one*)
    | Union (e1, e2) ->
        unionLinearForm
          (linearization_helper at e1)
          (linearization_helper at e2)
    | Conc (e1, e2) ->
        let linear1 = linearization_helper at e1 in
        unionLinearForm
          (concLinearForm (linear1) e2)
          (atomExists (linearization_helper at e2) e1)
    | Star e -> concLinearForm (linearization_helper at e) (Star e)
    | _ -> AtPactMap.empty
  in
  print_string (Print.pprint_linear_form (linearization_helper (getAtomsof exp) exp));
  linearization_helper (getAtomsof exp) exp

(** gets the string set of atoms directly from expression**)

(** Get the derivative map for a set of KATs (sum), represented as a set of terms **)
let get_der_map_sum (sum : KATSet.t) : DerMapSet.t =
  KATSet.to_list sum |> List.map (fun x -> linearization x) |> DerMapSet.of_list

(**hd function gets the set of all heads αp mapped in the linearform of a KAT**)
let hd (r : linearForm) : AtPactSet.t =
  AtPactSet.of_list (List.map fst (AtPactMap.to_list r))

(** Function deriv collects all the partial derivatives of 
      a KAT expression in respect to a αp, that were computed 
      by linearization function. **)
let deriv (atp : atPact) (der_map : linearForm) : KATSet.t =
  
  match AtPactMap.find_opt atp der_map with
  (*If the p doesn't exists then return empty*)
  | None -> KATSet.empty
  (*Otherwise return the sum*)
  | Some der_sum -> der_sum

let hd_sum (sum : DerMapSet.t) : AtPactSet.t =
  let sumLinear = DerMapSet.to_list sum in
  (* union each head of term in the sum*)
  List.fold_left AtPactSet.union AtPactSet.empty (List.map hd sumLinear)

let deriv_sum (atp : atPact) (sum_der_map : DerMapSet.t) : KATSet.t =
  DerMapSet.to_list sum_der_map
  (*Take the derivative of each element of the sum*)
  |> List.map (deriv atp)
  (*Union the results*)
  |> List.fold_left KATSet.union KATSet.empty

(**hAll takes two expressions e1 and e2 returns True if, 
    for every atom α, we have Eα(e1)=Eα(e2) and False otherwise**)
let rec hAll (e1 : kat) (e2 : kat) (at : SStringSet.t) : bool =
  if SStringSet.is_empty at then true
  else
    let ele = SStringSet.min_elt at in
    if epsilon ele e1 == epsilon ele e2 then
      hAll e1 e2 (SStringSet.remove ele at)
    else false

(** takes two KATsets and returns true if for every atom α, we have Eα(E1)=Eα(E2) and False otherwise**)
let rec hAll_sum (e1 : KATSet.t) (e2 : KATSet.t) (at : SStringSet.t) : bool =
  if SStringSet.is_empty at then true
  else
    let ele = SStringSet.min_elt at in
    print_string ("current_atom " ^ (Atom.pprint ele));
    print_newline();
    print_newline();
    print_string ("epsilon_sum e1 with atom " ^ (Atom.pprint ele)^" :"^(Print.pprint_sum e1) ^" ->"^ (string_of_bool(epsilon_sum ele e1))) ;
    print_newline();
    print_string ("epsilon_sum e2 with atom  " ^ (Atom.pprint ele)^" :"^(Print.pprint_sum e2) ^" ->"^ (string_of_bool(epsilon_sum ele e2))) ;
    print_newline();
    if epsilon_sum ele e1 == epsilon_sum ele e2 then 
      hAll_sum e1 e2 (SStringSet.remove ele at)
    else false


let derivatives ((r1, r2) : KATSet.t * KATSet.t) : PDerivPairSet.t =
  let der_map1 = get_der_map_sum r1 in
  let der_map2 = get_der_map_sum r2 in
  let heads = AtPactSet.union (hd_sum der_map1) (hd_sum der_map2) in
  AtPactSet.to_list heads
  |> List.map (fun p -> (deriv_sum p der_map1, deriv_sum p der_map2))
  |> PDerivPairSet.of_list

(** Equivalence Function **)
let equiv (e1 : kat) (e2 : kat) : bool =
  let pb_e1 = pBoolOf (e1, true) and pb_e2 = pBoolOf (e2, true) in
  print_string ("pbools of e1 " ^ (Print.pprint e1)^ (Atom.pprint pb_e1));
  print_newline();
  print_string ("pbools of e2 " ^ (Print.pprint e2)^ (Atom.pprint pb_e2));
  print_newline();
  let prim_bools = Atom.union pb_e1 pb_e2 in
  print_string ("pbools union "^ (Atom.pprint prim_bools));
  print_newline();
  let atoms = atOf prim_bools in
  print_string ("atoms " ^ (Print.pprint_atoms atoms));
  print_newline();
  let rec equiv_help ((todo, visited) : PDerivPairSet.t * PDerivPairSet.t) :
      bool =
    print_string ("TODO:"  ^ (Print.pprint_pder todo));
    print_newline();
    let new_list = PDerivPairSet.to_list todo in 
    print_string(string_of_bool (List.for_all (fun (x,y) -> 
      (let kx_list = (KATSet.to_list x) in List.is_empty kx_list ) 
      && (let ky_list = (KATSet.to_list y) in List.is_empty ky_list )) new_list));
      print_newline();
        if 
          (List.for_all (fun (x,y) -> 
            (let kx_list = (KATSet.to_list x) in List.is_empty kx_list ) 
            && (let ky_list = (KATSet.to_list y) in List.is_empty ky_list )) new_list)
            then let string = "it is empty!!!" in
            print_string (string);
              true else 
    match PDerivPairSet.choose_opt todo with
    (*get a KATSet pair*)
    | None -> true (*todo is empty, finised*)
    | Some (sum1, sum2) ->
        print_string ("sum1 :" ^ (Print.pprint_sum sum1));
        print_newline();
        print_string ("sum2 :" ^ (Print.pprint_sum sum2));
        print_newline();
        (*first pair of todo*)
        print_string ("hAll_sum :"^string_of_bool (hAll_sum sum1 sum2 atoms));
        print_newline();
        if hAll_sum sum1 sum2 atoms = false then false (* Eα(E1)!=Eα(E2) *)
        else
          let new_visited = PDerivPairSet.add (sum1, sum2) visited in
          (* add checked pair to visited *)
          let dervs = derivatives (sum1, sum2) in
          (*Get rid of pairs of empty lists*)
          print_newline();
          print_string ("dervs :" ^ (Print.pprint_pder dervs));
          print_newline();
          (* find derivs of pair *)
         let new_todo =
            (* add new pairs from derivs to todo and take set diff of visited to avoid reps*)
            PDerivPairSet.diff (PDerivPairSet.union todo dervs) new_visited
          in
          print_string ("new todo :" ^ (Print.pprint_pder new_todo));
          print_newline();
          equiv_help (new_todo, new_visited) 
    (* first call to equiv_help with todo having e1 and e2 as the first pair and visited as empty pair *)
  in

  equiv_help
    ( PDerivPairSet.singleton (KATSet.singleton e1, KATSet.singleton e2),
      PDerivPairSet.empty )

module Parser = struct
  open Parser.Combinators

  let p_act_parser : katI parser =
    let* start =
      satisfy (fun c -> List.mem c [ 'p'; 'q'; 'r'; 's'; 't'; 'e' ])
    in
    let* rest = many (satisfy (fun c -> is_alpha c || is_digit c)) in
    pure (pAct (implode (start :: rest))) << ws

  let p_bool_parser : katI parser =
    let* start = satisfy (fun c -> List.mem c [ 'a'; 'b'; 'c'; 'd' ]) in
    let* rest = many (satisfy (fun c -> is_alpha c || is_digit c)) in
    pure (pBool (implode (start :: rest))) << ws

  let one_parser : katI parser =
    let* _ = keyword "1" in
    pure one

  let zero_parser : katI parser =
    let* _ = keyword "0" in
    pure zero

  let rec min_term_parser () : katI parser =
    let* _ = pure () in
    choice
      [
        p_act_parser;
        p_bool_parser;
        one_parser;
        zero_parser;
        keyword "(" >> term_parser () << keyword ")";
      ]

  and star_parser () : katI parser =
    let* eI = min_term_parser () in
    let* _ = keyword "*" <|> keyword "^*" in
    pure (star eI)

  and min_term_star_pareser () = star_parser () <|> min_term_parser ()

  and not_pareser () : katI parser =
    let* _ = char '~' << ws in
    let* eI = min_term_star_pareser () << ws in
    pure (not_N eI)

  and not_star_parser () = not_pareser () <|> min_term_star_pareser ()

  and conc_parser () : katI parser =
    let* eI = not_star_parser () in
    let opr () =
      (*conc explicitly using "@" symbol*)
      (let* _ = keyword "@" in
       let* eI = not_star_parser () in
       pure ((fun eI1 eI2 -> conc eI1 eI2), eI))
      <|>
      (*conc implicitly without using any operators*)
      let* eI = not_star_parser () in
      pure ((fun eI1 eI2 -> conc eI1 eI2), eI)
    in
    let* eIs = many (opr ()) in
    pure (List.fold_left (fun acc (f, e) -> f acc e) eI eIs)

  and union_parser () =
    let* eI = conc_parser () in
    let opr () =
      let* _ = keyword "+" in
      let* eI = conc_parser () in
      pure ((fun eI1 eI2 -> union eI1 eI2), eI)
    in
    let* eIs = many (opr ()) in
    pure (List.fold_left (fun acc (f, e) -> f acc e) eI eIs)

  and term_parser () =
    let* _ = pure () in
    union_parser ()

  let parse_kat (s : string) : kat option =
    match parse (ws >> term_parser ()) s with
    | Some ((r, _), []) -> Some r
    | _ -> None

  let parse_kat_unsafe (s : string) : kat = Option.get (parse_kat s)
end

(*Examples for testing*)
let fromStr str = (Parser.parse_kat_unsafe str)

let kat_bpc = fromStr "b(p(c))"
let atom_bc = Atom.of_list [ "b"; "c" ], "p"

let atom_b = Atom.of_list [ "b" ]
let atom_bp = Atom.of_list ["b"], "p"

let exp_b = fromStr "b"
let exp_bp = fromStr "b(p)"

let atoms =  Atom.of_list ["a";"b"],"p"
let x = (linearization (fromStr "a(p) + (b)q"))
let first = linearization (fromStr "a(p)")
let second = linearization (fromStr "b(q)")

(**examples to type check /tests**)
(* let rec pBoolOf((exp, expIsBExp): kat * bool):StringSet.t =
     if expIsBExp then
       match exp with           (*At*)
       |One -> StringSet.empty
       |PBool b-> StringSet.singleton b
       |Conc(a,b)-> StringSet.union (pBoolOf (a,true)) (pBoolOf (b,true))
       |Union(a,b)-> StringSet.union (pBoolOf (a,true)) (pBoolOf (b,true))
       |Not(b) -> pBoolOf (b,true)
       (*TODO: Just to surpress the warning for now, remove when finished*)
       | _ -> failwith "We want boolean expressions but KA expression is given"
   else raise (Invalid_argument "pBool only takes bool expressions") *)

(* OTHER WORK
let rec epsilon_2 (prim_bools : StringSet.t) (e : kat) : SStringSet.t =
  (*set of atoms*)
  match e with
  | One -> atOf prim_bools
  | Zero -> SStringSet.empty
  | PBool b ->
      atOf (StringSet.remove b prim_bools) |> SStringSet.map (StringSet.add b)
  | PAct _ -> SStringSet.empty (*???*)
  | Union (e1, e2) ->
      let ep1 = epsilon_2 prim_bools e1 and ep2 = epsilon_2 prim_bools e2 in
      SStringSet.union ep1 ep2
  | Conc (e1, e2) ->
      let ep1 = epsilon_2 prim_bools e1 and ep2 = epsilon_2 prim_bools e2 in
      SStringSet.inter ep1 ep2
  | Not e ->
      let atoms = atOf prim_bools and notE = epsilon_2 prim_bools e in
      SStringSet.diff atoms notE
  | Star _ -> atOf prim_bools (*???*)

(*write hAll version 2 using epsilon_2!!!!!*)
(*
let rec h_all_2 (prim_bools:StringSet.t)(s1: KATSet.t)(s2:KATSet.t): bool =
  let e1=KATSet.min_elt s1 in
  let e2=KATSet.min_elt s2 in
  let eps_e1=epsilon_2 prim_bools e1 in
  let eps_e2=epsilon_2 prim_bools e2 in
  if SStringSet.equal eps_e1 eps_e2 then h_all_2 prim_bools (KATSet.remove e1 s1) (KATSet.remove e2 s1)
  else false

 let rec h_all_2_sum (e1:KATSet.t)(e2:KATSet.t)(prim_bools: SStringSet.t): bool =
  if (StringSet.is_empty prim_bools) then true
  else 
    let ele = StringSet.min_elt prim_bools in 
    if h_all_2 ele e1 e2  then h_all_2_sum e1 e2 (StringSet.remove ele prim_bools)
    else false 
*)
*)
