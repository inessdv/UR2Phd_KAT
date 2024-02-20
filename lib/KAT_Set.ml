type kat =
  | Zero
  | One
  | PAct of string
  | PBool of string
  | Union of kat *  kat
  | Conc of  kat * kat
  | Star of kat
  | Not of kat

module Print = struct

  let pprint (exp: kat) = 
  (*helper method, takes a expression, output the string, 
      and **the precedence of the outer most expression** *)
  let rec helper (exp: kat): string * int = 
    match exp with
    | One -> ("1", 0)
    | Zero -> ("0", 0)
    | PAct(c) -> (c, 0)
    | PBool(c) -> (c, 0)
    | Star(r) -> 
      let (str, precedence) = helper r in 
      if precedence <= 0 then (str^"*", 0) else ("("^str^")*", 0)
    | Not (r) -> 
      let (str, precedence) = helper r in 
      if precedence <= 1 then ("~"^str, 1) else ("~("^str^")", 1)
    | Conc(r1, r2) ->
      let (str1, precedence1) = helper r1 in 
      let (str2, precedence2) = helper r2 in 
      let str1' = if precedence1 <= 2 then str1 else "("^str1^")" in 
      let str2' = if precedence2 < 2 then str2 else "("^str2^")" in 
      (str1' ^ " " ^ str2', 2)
    | Union(r1, r2) ->
      let (str1, precedence1) = helper r1 in 
      let (str2, precedence2) = helper r2 in 
      let str1' = if precedence1 <= 3 then str1 else "("^str1^")" in 
      let str2' = if precedence2 < 3 then str2 else "("^str2^")" in 
      (str1' ^ " + " ^ str2', 3) 
  in
  let (str, _) = helper exp in str 
  
end

type katI= kat * bool  (*True when expression is boolean, false when expression is KAT*)
let pAct p= PAct p,false
let pBool b = PBool b,true
let one = One,true 
let zero = (Zero,true) 

let union(e1:katI) (e2: katI):katI=
    match (e1,e2) with
    |(Zero,_),_-> e2
    |_,(Zero,_)-> e1
    | (k1,true),(k2,true) -> Union(k1,k2),true
    |(k1,_),(k2,_)-> Union(k1,k2),false

let conc(e1:katI) (e2:katI):katI= (** would it be better to use (kat*bool) pairs as input???**)
  match (e1,e2) with
    |(Zero,_),_-> Zero,true
    |_,(Zero,_)-> Zero,true
    |(One,_),_-> e2
    |_,(One,_)-> e1
    |(k1,true),(k2,true) -> Conc(k1,k2),true        (*if k1==One and k2==One then One,true  else Zero,true*)
    |(k1,false),(k2,false) -> Conc(k1,k2),false
    (*TODO: please fix this, conc can concatnate two types of expression*)
    |(_,_),(_,_) -> raise (Invalid_argument "conc only works in same type expression")


let not ((exp, expIsBExp): kat * bool) = 
    if expIsBExp 
      then match exp with 
        | One -> Zero, true 
        | Zero -> One, true 
        | _ -> (Not exp, true)
      else raise (Invalid_argument ("negation applied to non-boolean expression: "^(Print.pprint exp)))

let star((exp, expIsBExp): kat * bool)=
if expIsBExp==false then (Star(exp), false) else One,true

module KATSet = Set.Make(struct
type t = kat
let compare = compare
end)

module KATISet = Set.Make(struct
type t = katI 
let compare = compare
end)
  
(**examples to type check /tests**)
module StringSet = Set.Make(String)
let rec pBoolOf((exp, expIsBExp): kat * bool):StringSet.t =
  if expIsBExp then 
    match exp with           (*At*)
    |One -> StringSet.empty          
    |PBool b-> StringSet.singleton b
    |Conc(a,b)-> StringSet.union (pBoolOf (a,true)) (pBoolOf (b,true))      
    |Union(a,b)-> StringSet.union (pBoolOf (a,true)) (pBoolOf (b,true))           
    |Not(b) -> pBoolOf (b,true)
    (*TODO: Just to surpress the warning for now, remove when finished*)
    | _ -> failwith "We want boolean expressions but KA expression is given"
else raise (Invalid_argument "pBool only takes bool expressions")


let rec pBoolOf(exp:katI):StringSet.t =
  match exp with           (*At*)
  |(_,false) -> StringSet.empty (** or error message?**)
  |(bExp,true)-> 
    match bExp with
    |One -> StringSet.empty          
    |PBool b-> StringSet.singleton b
    |Conc(a,b)-> StringSet.union (pBoolOf (a,true)) (pBoolOf (b,true))     
    |Union(a,b)-> StringSet.union (pBoolOf (a,true)) (pBoolOf (b,true))           
    |Not(b) -> pBoolOf (b,true)
    |_ -> StringSet.empty


(** new type of set, set of string set to be produce power sets**)
module SStringSet=Set.Make(StringSet)

(** function to get the atoms of the primitive bools through power set**)
let atOf(primitive_boolset:StringSet.t):SStringSet.t =
  StringSet.fold (fun x ps -> SStringSet.fold 
    (fun ss-> SStringSet.add (StringSet.add x ss)) ps ps) primitive_boolset 
    (SStringSet.singleton StringSet.empty)

let rec epsilon (atom:StringSet.t) (exp: kat) : bool = 
match exp with
| Zero -> false
| One -> false
| PAct _ -> false
|PBool b -> StringSet.mem b atom(*if b<= atom, then b must in the atom *)
| Union(a,b) -> epsilon atom a || epsilon atom b
| Conc(a,b) -> epsilon atom a && epsilon atom b
| Star _ -> true
|Not(a)->epsilon atom a

(** empty word for KAT expressions**)
let eps (atom:StringSet.t)(sum: KATSet.t): bool =
  KATSet.exists (fun exp -> epsilon atom exp) sum


(** Linearization function
**)

(** A map from string*)
module StringMap = Map.Make(String)

(**pipeline for setm to seq and seq to set
let map aSet = ASet.to_seq aSet
  |> Seq.map
  |> BSet.of_seq
**)

(** define type of atom and prim act
**)
(* type p_bool = string
type p_act = string

module Atom = Set.Make(struct
  type t = p_bool
  let compare = compare
end) *)

(*Use StringSet to replace Atom*)


module AtPactMap = Map.Make(struct
  type t = StringSet.t * string
  let compare = compare
end)

(** The linear form of a expression, which is string mapped to as set of KA expressions*)
type linearForm = KATSet.t AtPactMap.t

module DerMapSet = Set.Make(struct
type t = linearForm
let compare = compare
end)

type atPact = StringSet.t * string

module AtPactSet = Set.Make(struct
type t = StringSet.t * string
let compare = compare
end)

module PDerivPairSet = Set.Make (struct
(* set of pairs of partial derivitives*)
type t = KATSet.t * KATSet.t
let compare = compare
end) 

(** linearization function
**)
let unionLinearForm (lin1: linearForm) (lin2: linearForm): linearForm = 
  AtPactMap.union
    (* combine two KAT sets with union, when their hd are the same*)
    (fun _ s1 s2 -> Some (KATSet.union s1 s2))
    lin1 lin2
    
let conc_alg (e1: kat) (e2: kat): kat = 
  match e1, e2 with 
    | One, _ -> e2 
    | _, One -> e1 
    | Zero, _ -> Zero
    | _, Zero -> Zero
    | _, _ -> Conc (e1, e2)

let concLinearForm (r_linear: linearForm) (r: kat): linearForm =
  AtPactMap.map (fun derivs -> 
(** when concatenating with 1, elimination of map of the 1, 
    we could also eliminate 0, as we'd get an empty set!!!*)
    KATSet.map (fun deriv -> conc_alg deriv  r ) derivs) 
    r_linear

(**let atoms (exp:kat): SStringSet.t = atOf (pBoolOf exp) ??????**)

let rec mapMakerHelper(mapper:linearForm)(at:SStringSet.t)(p:string):linearForm=
    if SStringSet.is_empty at then mapper else 
    let atom=SStringSet.min_elt at in
    let combine=(atom,p) in
    mapMakerHelper (AtPactMap.add combine (KATSet.singleton One) mapper) (SStringSet.remove atom at) p

(* mapMaker produce all atoms*p map to One *)
let mapMaker (at:SStringSet.t)(p:string):linearForm=
    let mapper=AtPactMap.empty in
    mapMakerHelper mapper at p

let atomExists(e2:linearForm)(e1:kat):linearForm =
      (* let e2List = AtPactMap.to_list e2 in
      match e2List with
      | ((a,b),_):: rest-> if epsilon a e1 then ()
      | _ -> *)
      (* AtPactMap.filter (fun (a,_) -> (epsilon a e1) ) e2   *) (*don't know why not working*)
      let e2List = AtPactMap.to_list e2 in
      AtPactMap.of_list (List.filter (fun ((a,_),_)-> epsilon a e1 ) e2List)


let rec linearization (at:SStringSet.t) (exp: kat): linearForm =
  match exp with
  | PBool _ -> AtPactMap.empty
  | PAct p  -> mapMaker at p (** map p to each atom and then each to one**)
  | Union(e1,e2) -> unionLinearForm (linearization at e1) (linearization at e2)
  | Conc(e1,e2) -> unionLinearForm (concLinearForm (linearization at e1) e2) (atomExists(linearization at e2) e1)
  | Star(e) -> concLinearForm (linearization at e) (Star(e)) 
  | _ -> AtPactMap.empty

(** Get the derivative map for a set of KATs (sum), represented as a set of terms **)
let get_der_map_sum (sum: KATSet.t): DerMapSet.t = 
  KATSet.to_list sum 
(** We need to get primitive bools and then atoms of each for each KAT???**)
  |> List.map linearization 
  |> DerMapSet.of_list


(**hd function gets the set of all heads αp mapped in the linearform of a KAT**)
let hd (r: linearForm ): AtPactSet.t =
    AtPactSet.of_list (List.map fst (AtPactMap.to_list r))
      
  
    (** Function deriv collects all the partial derivatives of 
      a KAT expression in respect to a αp, that were computed 
      by linearization function. **)
let deriv (atp: atPact) (der_map: linearForm): KATSet.t = 
      match AtPactMap.find_opt atp der_map with 
      (*If the p doesn't exists then return empty*)
      | None -> KATSet.empty
      (*Otherwise return the sum*)
      | Some der_sum -> der_sum
  
let hd_sum (sum: DerMapSet.t): AtPactSet.t = 
  let sumLinear = DerMapSet.to_list sum in 
  (* union each head of term in the sum*)
  List.fold_left AtPactSet.union AtPactSet.empty (List.map hd sumLinear)

let deriv_sum (atp: atPact)(sum_der_map: DerMapSet.t): KATSet.t =
    DerMapSet.to_list sum_der_map 
    (*Take the derivative of each element of the sum*)
    |> List.map (deriv atp)  
    (*Union the results*)
    |> List.fold_left KATSet.union KATSet.empty 

(**Is atoms from e1? **)
let rec hAll (e1:kat)(e2:kat)(at: SStringSet.t): bool =
if (SStringSet.is_empty at) then true
else 
  let ele =SStringSet.min_elt at in 
  if epsilon ele e1 == epsilon ele e2 then hAll e1 e2 (SStringSet.remove ele at)
  else false

let derivatives ((r1, r2): KATSet.t * KATSet.t): PDerivPairSet.t =
    let der_map1 = get_der_map_sum r1 in  
    let der_map2 = get_der_map_sum r2 in
    let heads = AtPactSet.union (hd_sum der_map1) (hd_sum der_map2) in
    (AtPactSet.to_list heads)
    |> (List.map (fun p -> (deriv_sum p der_map1, deriv_sum p der_map2)) )
    |> PDerivPairSet.of_list
  

(*examples*)

let example1=StringSet.of_list ["b";"c";"d"]
let example1= atOf example1 

let example2=SStringSet.to_list



module Parser = struct
  open Parser.Combinators

  let p_act_parser : katI parser =
    let* start = satisfy (fun c -> List.mem c ['p'; 'q'; 'r'; 's'; 't'; 'e']) in
    let* rest =  many (satisfy (fun c -> is_alpha c || is_digit c)) in
    pure (pAct (implode (start :: rest))) << ws

  let p_bool_parser : katI parser =
    let* start = satisfy (fun c -> List.mem c ['a'; 'b'; 'c'; 'd']) in
    let* rest =  many (satisfy (fun c -> is_alpha c || is_digit c)) in
    pure (pBool (implode (start :: rest))) << ws
    
  
  let one_parser : katI parser = 
    let* _ = keyword "1" in 
    pure one

  let zero_parser : katI parser = 
    let* _ = keyword "0" in 
    pure zero

  let rec min_term_parser (): katI parser =
    let* _ = pure () in
    choice
      [ p_act_parser 
      ; p_bool_parser
      ; one_parser
      ; zero_parser
      ; keyword "(" >> term_parser () << keyword ")"
      ]

  and star_parser (): katI parser = 
    let* eI = min_term_parser () in
    let* _ = keyword "*" <|> keyword "^*" in
    pure (star eI)

  and min_term_star_pareser () = star_parser () <|> min_term_parser () 

  and not_pareser () : katI parser = 
    let* _ = char '~' << ws in 
    let* eI = min_term_star_pareser () << ws in 
    pure (not eI)

  and not_star_parser () = not_pareser () <|> min_term_star_pareser ()
    
  and conc_parser () : katI parser = 
    let* eI = not_star_parser () in
    let opr () = 
          (*conc explicitly using "@" symbol*)
          (let* _ = keyword "@" in
          let* eI = not_star_parser () in
          pure (
            (fun eI1 eI2 -> conc eI1 eI2), eI)) 
          <|>
          (*conc implicitly without using any operators*)
          (let* eI = not_star_parser () in
          pure ((fun eI1 eI2 -> conc eI1 eI2), eI)) 
    in
    let* eIs = many (opr ()) in
    pure (List.fold_left (fun acc (f, e) -> f acc e) eI eIs)

  and union_parser () =
    let* eI = conc_parser () in
    let opr () = (let* _ = keyword "+" in
           let* eI = conc_parser () in
           pure ((fun eI1 eI2 -> union eI1 eI2), eI))
    in
    let* eIs = many (opr ()) in
    pure (List.fold_left (fun acc (f, e) -> f acc e) eI eIs)

  and term_parser () =
    let* _ = pure () in
    union_parser ()

  let parse_kat (s : string) : kat option =
    match parse (ws >> term_parser ()) s with
    |Some ((r, _),[]) -> Some r
    |_ -> None

  let parse_kat_unsafe (s: string) : kat =
    Option.get (parse_kat s)
end


