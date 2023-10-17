open Format

module Parser = struct
  let is_lower_case c = 'a' <= c && c <= 'z'

  let is_upper_case c = 'A' <= c && c <= 'Z'

  let is_alpha c = is_lower_case c || is_upper_case c

  let is_digit c = '0' <= c && c <= '9'

  let is_alphanum c = is_lower_case c || is_upper_case c || is_digit c

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

  let rec many1 (p : 'a parser) : 'a list parser =
   fun ls ->
    match p ls with
    | Some (x, ls) -> (
      match many p ls with
      | Some (xs, ls) -> Some (x :: xs, ls)
      | None -> Some ([ x ], ls))
    | None -> None

  let rec many' (p : unit -> 'a parser) : 'a list parser =
   fun ls ->
    match p () ls with
    | Some (x, ls) -> (
      match many' p ls with
      | Some (xs, ls) -> Some (x :: xs, ls)
      | None -> Some ([ x ], ls))
    | None -> Some ([], ls)

  let rec many1' (p : unit -> 'a parser) : 'a list parser =
   fun ls ->
    match p () ls with
    | Some (x, ls) -> (
      match many' p ls with
      | Some (xs, ls) -> Some (x :: xs, ls)
      | None -> Some ([ x ], ls))
    | None -> None

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

  let ws1 : unit parser = many1 whitespace >| ()

  let digit : char parser = satisfy is_digit

  let natural : int parser =
   fun ls ->
    match many1 digit ls with
    | Some (xs, ls) -> Some (int_of_string (implode xs), ls)
    | _ -> None

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
(** above parser combinators **)
module Term = struct
  open Parser

  type t =
    | Var of string
    | Fun of string * string * t
    | App of t * t
    | If of t * t * t

    | Let of string * t * t
    | Match of t * (int * t) list
    | Try of t * t
    | Print of t list
    | Unit
    | Bool of bool
    | Int of int
    | Add of t * t
    | Sub of t * t
    | Mul of t * t
    | Div of t * t
    | Mod of t * t
    | And of t * t
    | Or of t * t
    | Not of t
    | Equal of t * t
    | Lt of t * t
    | Lte of t * t
    | Gt of t * t
    | Gte of t * t

  let reserved =
    [ "fun"
    ; "if"
    ; "then"
    ; "else"
    ; "let"
    ; "rec"
    ; "in"
    ; "print"
    ; "match"
    ; "try"
    ; "with"
    ; "mod"
    ; "not"
    ; "true"
    ; "false"
    ; "exn"
    ]

  let name : string parser =
    let* xs1 = many1 (satisfy (fun c -> is_alpha c || c = '_')) in
    let* xs2 = many (satisfy (fun c -> is_alphanum c || c = '_' || c = '\'')) in
    let s = implode xs1 ^ implode xs2 in
    if List.exists (fun x -> x = s) reserved then
      fail
    else
      pure ("v" ^ s) << ws

  let name_parser () =
    let* n = name in
    if n = "v_" then
      fail
    else
      pure (Var n)

  let unit_parser () =
    let* _ = keyword "()" in
    pure Unit

  let integer_parser () =
    (let* _ = keyword "-" in
     let* n = natural in
     pure (-n))
    <|> (let* n = natural in
         pure n)
    << ws

  let int_parser () =
    let* n = natural in
    pure (Int n) << ws

  let bool_parser () =
    keyword "true" >| Bool true <|> (keyword "false" >| Bool false)

  let rec term_parser0 () =
    let* _ = pure () in
    choice
      [ name_parser ()
      ; unit_parser ()
      ; int_parser ()
      ; bool_parser ()
      ; keyword "(" >> term_parser () << keyword ")"
      ]

  and term_parser1 () =
    let* es = many1 (term_parser0 ()) in
    match es with
    | e :: es -> pure (List.fold_left (fun acc e -> App (acc, e)) e es)
    | _ -> fail

  and term_parser2 () =
    choice
      [ (let* _ = keyword "-" in
         let* e = term_parser1 () in
         pure (Sub (Int 0, e)))
      ; (let* e = term_parser1 () in
         pure e)
      ]

  and term_parser3 () =
    let* e = term_parser2 () in
    let opr () =
      choice
        [ (let* _ = keyword "*" in
           let* e = term_parser2 () in
           pure ((fun e1 e2 -> Mul (e1, e2)), e))
        ; (let* _ = keyword "/" in
           let* e = term_parser2 () in
           pure ((fun e1 e2 -> Div (e1, e2)), e))
        ; (let* _ = keyword "mod" in
           let* e = term_parser2 () in
           pure ((fun e1 e2 -> Mod (e1, e2)), e))
        ]
    in
    let* es = many (opr ()) in
    pure (List.fold_left (fun acc (f, e) -> f acc e) e es)

  and term_parser4 () =
    let* e = term_parser3 () in
    let opr () =
      choice
        [ (let* _ = keyword "+" in
           let* e = term_parser3 () in
           pure ((fun e1 e2 -> Add (e1, e2)), e))
        ; (let* _ = keyword "-" in
           let* e = term_parser3 () in
           pure ((fun e1 e2 -> Sub (e1, e2)), e))
        ]
    in
    let* es = many (opr ()) in
    pure (List.fold_left (fun acc (f, e) -> f acc e) e es)

  and term_parser5 () =
    let* e = term_parser4 () in
    let opr () =
      choice
        [ (let* _ = keyword "=" in
           let* e = term_parser4 () in
           pure ((fun e1 e2 -> Equal (e1, e2)), e))
        ; (let* _ = keyword "<" in
           let* e = term_parser4 () in
           pure ((fun e1 e2 -> Lt (e1, e2)), e))
        ; (let* _ = keyword "<=" in
           let* e = term_parser4 () in
           pure ((fun e1 e2 -> Lte (e1, e2)), e))
        ; (let* _ = keyword ">" in
           let* e = term_parser4 () in
           pure ((fun e1 e2 -> Gt (e1, e2)), e))
        ; (let* _ = keyword ">=" in
           let* e = term_parser4 () in
           pure ((fun e1 e2 -> Gte (e1, e2)), e))
        ]
    in
    let* es = many (opr ()) in
    pure (List.fold_left (fun acc (f, e) -> f acc e) e es)

  and term_parser6 () =
    (let* _ = keyword "not" in
     let* m = term_parser5 () in
     pure (Not m))
    <|> term_parser5 ()

  and term_parser7 () =
    let* e = term_parser6 () in
    let opr () =
      let* _ = keyword "&&" in
      let* e = term_parser6 () in
      pure ((fun e1 e2 -> And (e1, e2)), e)
    in
    let* es = many (opr ()) in
    pure (List.fold_left (fun acc (f, e) -> f acc e) e es)

  and term_parser8 () =
    let* e = term_parser7 () in
    let opr () =
      let* _ = keyword "||" in
      let* e = term_parser7 () in
      pure ((fun e1 e2 -> Or (e1, e2)), e)
    in
    let* es = many (opr ()) in
    pure (List.fold_left (fun acc (f, e) -> f acc e) e es)

  and term_parser () =
    let* _ = pure () in
    choice
      [ term_parser8 ()
      ; fun_parser ()
      ; if_parser ()
      ; letrec_parser ()
      ; let_parser ()
      ; match_parser ()
      ; try_parser ()
      ; trace_parser ()
      ]

  and trace_parser () =
    let* _ = keyword "print" in
    let* ms = many1' term_parser0 in
    pure (Print ms)

  and fun_parser () =
    let* _ = keyword "fun" in
    let* xs = many1 name in
    let* _ = keyword "->" in
    let* e = term_parser () in
    let m = List.fold_right (fun x acc -> Fun ("fun", x, acc)) xs e in
    pure m

  and if_parser () =
    let* _ = keyword "if" in
    let* cond = term_parser () in
    let* _ = keyword "then" in
    let* e1 = term_parser () in
    let* _ = keyword "else" in
    let* e2 = term_parser () in
    pure (If (cond, e1, e2))

  and let_parser () =
    let* _ = keyword "let" in
    let* n = name in
    let* _ = keyword "=" in
    let* e1 = term_parser () in
    let* _ = keyword "in" in
    let* e2 = term_parser () in
    pure (Let (n, e1, e2))

  and letrec_parser () =
    let* _ = keyword "let" in
    let* _ = keyword "rec" in
    let* n = name in
    let* args = many1 name in
    let* _ = keyword "=" in
    let* e1 = term_parser () in
    let e1, _ =
      List.fold_right
        (fun arg (acc, len) ->
          let fn =
            if len = 1 then
              n
            else
              "fun"
          in
          (Fun (fn, arg, acc), len - 1))
        args
        (e1, List.length args)
    in
    let* _ = keyword "in" in
    let* e2 = term_parser () in
    pure (Let (n, e1, e2))

  and match_parser () =
    let* _ = keyword "match" in
    let* e1 = term_parser () in
    let* _ = keyword "with" in
    let* cls = many' clause_parser in
    pure (Match (e1, cls))

  and try_parser () =
    let* _ = keyword "try" in
    let* e1 = term_parser () in
    let* _ = keyword "with" in
    let* e2 = term_parser () in
    pure (Try (e1, e2))

  and clause_parser () =
    let* _ = keyword "|" in
    let* i = integer_parser () in
    let* _ = keyword "->" in
    let* m = term_parser () in
    pure (i, m)

  let parse_prog (s : string) : (t * char list) option =
    parse (ws >> term_parser ()) s
end
