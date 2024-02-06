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
type t = kat (**would this be katI???**)
let compare = compare
end)

module KATISet = Set.Make(struct
type t = katI (**would this be katI???**)
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



(**similar question to pBool**)
let rec epsilon (atom:StringSet.t) (exp: kat) : bool = 
if (expIsBExp== false) then 
match exp with
| Zero -> false
| One -> true
| PAct _ -> false
| Union(a,b) -> epsilon (a,false) || epsilon (b,false)
| Conc(a,b) -> epsilon (a,false) && epsilon (b,false)
| Star _ -> true
| _ -> false
else raise (Invalid_argument "epsilon only takes KA expressions")

(** empty word for KAT expressions**)
let eps (sum: KATISet.t): bool =
  KATISet.exists (fun exp -> epsilon exp) sum 


(* existence of atom in R, set of KAT**)
let existance ((exp,expIsBExp):kat * bool) (rSet:KATISet.t): bool = (*??**)
  if expIsBExp then KATISet.mem (exp,true) rSet else raise (Invalid_argument "epsilon only takes Bexp expressions")

(** function to extract p?
**)

(** derivative function: we need a and p and a KAT Exp
let deriv (a:kat(* bexp atom **))(p:kat (*primitive action **))(exp:kat): KATSet.t =
**)

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


