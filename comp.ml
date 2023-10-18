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

  type t =
    | Val of char
    | Union of t * t
    | Seq of t * t
    | Star of t

  let symbol_parser : t parser =
    let*  s = satisfy (fun c -> is_alpha c ) in
    pure (Val s) << ws

  let rec term_parser0 () =
    let* _ = pure () in
    choice
      [ symbol_parser
        ; keyword "(" >> term_parser_star () << keyword ")^*"
      ; keyword "(" >> term_parser () << keyword ")"
      ]

  and seq_parser () =
    let* e = term_parser0 () in
    let opr () = (let* _ = keyword "@" in
           let* e = term_parser0 () in
           pure ((fun e1 e2 -> Seq (e1, e2)), e))
    in
    let* es = many (opr ()) in
    pure (List.fold_left (fun acc (f, e) -> f acc e) e es)

  and union_parser () =
    let* e = seq_parser () in
    let opr () = (let* _ = keyword "+" in
           let* e = seq_parser () in
           pure ((fun e1 e2 -> Union (e1, e2)), e))
    in
    let* es = many (opr ()) in
    pure (List.fold_left (fun acc (f, e) -> f acc e) e es)

  and term_parser () =
    let* _ = pure () in
    union_parser ()

  and term_parser_star () =
    let* e = union_parser () in
    pure (Star e)
       
  let parse_prog (s : string) : t  option =
    match parse (ws >> term_parser ()) s with
    |Some (r,[]) -> Some r
    |_ -> None
end