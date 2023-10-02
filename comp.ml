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

module Comp = struct
  open Term

  type const =
    | Unit
    | Int of int
    | Bool of bool
    | Name of string

  type cmd =
    | Push of const
    | Pop of int
    | Add of int
    | Sub of int
    | Mul of int
    | Div of int
    | Equal
    | Lte
    | And
    | Or
    | Not
    | Trace of int
    | Local
    | Global
    | Lookup
    | BeginEnd of cmds
    | IfElse of cmds * cmds
    | Fun of string * string * cmds
    | Call
    | Try of cmds
    | Switch of (int * cmds) list

  and cmds = cmd list

  let pp_const fmt x =
    match x with
    | Unit -> fprintf fmt "()"
    | Int i -> fprintf fmt "%d" i
    | Bool b ->
      if b then
        fprintf fmt "True"
      else
        fprintf fmt "False"
    | Name s -> fprintf fmt "%s" s

  let indent idt = String.make idt ' '

  let rec pp_cmd idt fmt cmd =
    match cmd with
    | Push s -> fprintf fmt "Push %a" pp_const s
    | Pop i -> fprintf fmt "Pop %d" i
    | Add i -> fprintf fmt "Add %d" i
    | Sub i -> fprintf fmt "Sub %d" i
    | Mul i -> fprintf fmt "Mul %d" i
    | Div i -> fprintf fmt "Div %d" i
    | Equal -> fprintf fmt "Equal"
    | Lte -> fprintf fmt "Lte"
    | And -> fprintf fmt "And"
    | Or -> fprintf fmt "Or"
    | Not -> fprintf fmt "Not"
    | Trace i -> fprintf fmt "Trace %d" i
    | Local -> fprintf fmt "Local"
    | Global -> fprintf fmt "Global"
    | Lookup -> fprintf fmt "Lookup"
    | BeginEnd cmds ->
      fprintf fmt "Begin\n%a%sEnd" (pp_cmds (idt + 2)) cmds (indent idt)
    | IfElse (cmds1, cmds2) ->
      fprintf fmt "If\n%a%sElse\n%a%sEnd"
        (pp_cmds (idt + 2))
        cmds1 (indent idt)
        (pp_cmds (idt + 2))
        cmds2 (indent idt)
    | Fun (f, arg, cmds) ->
      fprintf fmt "Fun %s %s\n%a%sEnd" f arg
        (pp_cmds (idt + 2))
        cmds (indent idt)
    | Call -> fprintf fmt "Call"
    | Try cmds ->
      fprintf fmt "Try\n%a%sEnd" (pp_cmds (idt + 2)) cmds (indent idt)
    | Switch cls ->
      fprintf fmt "Switch\n%a%sEnd" (pp_cls (idt + 2)) cls (indent idt)

  and pp_cmds idt fmt cmds =
    match cmds with
    | [] -> ()
    | cmd :: cmds ->
      fprintf fmt "%s%a\n%a" (indent idt) (pp_cmd idt) cmd (pp_cmds idt) cmds

  and pp_cls idt fmt cls =
    match cls with
    | [] -> ()
    | (i, cmds) :: cls ->
      fprintf fmt "%sCase %d\n%a%a" (indent idt) i
        (pp_cmds (idt + 2))
        cmds (pp_cls idt) cls

  and pp fmt cmds = fprintf fmt "%a" (pp_cmds 0) cmds

  let rec add_spine m =
    match m with
    | Term.Add (m, n) ->
      let h, sp = add_spine m in
      (h, sp @ [ n ])
    | _ -> (m, [])

  let rec sub_spine m =
    match m with
    | Term.Sub (m, n) ->
      let h, sp = sub_spine m in
      (h, sp @ [ n ])
    | _ -> (m, [])

  let rec mul_spine m =
    match m with
    | Term.Mul (m, n) ->
      let h, sp = mul_spine m in
      (h, sp @ [ n ])
    | _ -> (m, [])

  let rec div_spine m =
    match m with
    | Term.Div (m, n) ->
      let h, sp = div_spine m in
      (h, sp @ [ n ])
    | _ -> (m, [])

  let rec comp m =
    match m with
    | Var s -> [ Push (Name s); Lookup ]
    | Fun (f, arg, m) ->
      let cmds = comp m in
      [ Fun (f, arg, cmds); Push (Name f); Lookup ]
    | App (m, n) ->
      let cmds1 = comp n in
      let cmds2 = comp m in
      cmds1 @ cmds2 @ [ Call ]
    | If (cond, m1, m2) ->
      let cmds1 = comp cond in
      let cmds2 = [ BeginEnd (comp m1) ] in
      let cmds3 = [ BeginEnd (comp m2) ] in
      cmds1 @ [ IfElse (cmds2, cmds3) ]
    | Let (s, m, n) ->
      let cmds1 = comp m in
      let cmds2 = comp n in
      [ BeginEnd (cmds1 @ [ Push (Name s); Local; Pop 1 ] @ cmds2) ]
    | Match (m, cls) ->
      let cmds = comp m in
      let cases =
        List.map
          (fun (i, m) ->
            let cmds = [ BeginEnd (comp m) ] in
            (i, cmds))
          cls
      in
      cmds @ [ Switch cases ]
    | Try (m, n) ->
      let exn = Name "exn" in
      let cmds1 = comp m in
      let cmds1 = cmds1 @ [ Push (Bool true); Push exn; Global; Pop 1 ] in
      let cmds2 = comp n @ [ Push (Bool true); Push exn; Global; Pop 1 ] in
      let cmds2 =
        [ Push exn; Lookup; IfElse ([ Pop 0 ], [ BeginEnd cmds2 ]) ]
      in
      [ Push (Bool false); Push exn; Global; Pop 1; Try cmds1 ] @ cmds2
    | Print ms ->
      let cmds = List.concat_map comp ms in
      cmds @ [ Trace (List.length ms); Push Unit ]
    | Unit -> [ Push Unit ]
    | Bool b -> [ Push (Bool b) ]
    | Int i ->
      if i >= 0 then
        [ Push (Int i) ]
      else
        [ Push (Int i); Push (Int 0); Sub 2 ]
    | Add _ ->
      let h, sp = add_spine m in
      let cmds1 = comp h in
      let cmds2 = List.concat_map comp sp in
      cmds2 @ cmds1 @ [ Add (List.length sp + 1) ]
    | Sub _ ->
      let h, sp = sub_spine m in
      let cmds1 = comp h in
      let cmds2 = List.concat_map comp sp in
      cmds2 @ cmds1 @ [ Sub (List.length sp + 1) ]
    | Mul _ ->
      let h, sp = mul_spine m in
      let cmds1 = comp h in
      let cmds2 = List.concat_map comp sp in
      cmds2 @ cmds1 @ [ Mul (List.length sp + 1) ]
    | Div _ ->
      let h, sp = div_spine m in
      let cmds1 = comp h in
      let cmds2 = List.concat_map comp sp in
      cmds2 @ cmds1 @ [ Div (List.length sp + 1) ]
    | Mod (m, n) ->
      let cmds1 = comp m in
      let cmds2 = comp n in
      let cmds3 = cmds2 @ cmds1 @ [ Div 2 ] in
      let cmds3 = cmds3 @ cmds2 @ [ Mul 2 ] in
      cmds3 @ cmds1 @ [ Sub 2 ]
    | And (m, n) ->
      let cmds1 = comp m in
      let cmds2 = comp n in
      cmds2 @ cmds1 @ [ And ]
    | Or (m, n) ->
      let cmds1 = comp m in
      let cmds2 = comp n in
      cmds2 @ cmds1 @ [ Or ]
    | Not m ->
      let cmds = comp m in
      cmds @ [ Not ]
    | Equal (m, n) ->
      let cmds1 = comp m in
      let cmds2 = comp n in
      cmds2 @ cmds1 @ [ Equal ]
    | Lt (m, n) ->
      let cmds1 = comp m in
      let cmds2 = comp n in
      cmds2 @ cmds1 @ [ Lte ] @ cmds2 @ cmds1 @ [ Equal; Not; And ]
    | Lte (m, n) ->
      let cmds1 = comp m in
      let cmds2 = comp n in
      cmds2 @ cmds1 @ [ Lte ]
    | Gt (m, n) ->
      let cmds1 = comp m in
      let cmds2 = comp n in
      cmds2 @ cmds1 @ [ Lte; Not ]
    | Gte (m, n) ->
      let cmds1 = comp m in
      let cmds2 = comp n in
      cmds2 @ cmds1 @ [ Lte; Not ] @ cmds2 @ cmds1 @ [ Equal; Or ]
end

module Interp = struct
  open Comp

  type env = (string * value) list

  and value =
    | VUnit
    | VInt of int
    | VBool of bool
    | VName of string
    | VClosure of string * string * cmds * env

  type stack = value list

  type log = string list

  let pp_log fmt log =
    let rec aux fmt log =
      match log with
      | [] -> ()
      | [ s ] -> fprintf fmt "\"%s\"" s
      | s :: log -> fprintf fmt "\"%s\"; %a" s aux log
    in
    fprintf fmt "[%a]" aux log

  let rec addn n ls =
    if n < 0 then
      None
    else if n = 0 then
      Some (0, ls)
    else
      match ls with
      | VInt x :: ls -> (
        match addn (n - 1) ls with
        | Some (y, ls) -> Some (x + y, ls)
        | None -> None)
      | _ -> None

  let subn n ls =
    if n < 0 then
      None
    else if n = 0 then
      Some (0, ls)
    else
      match ls with
      | VInt x :: ls -> (
        match addn (n - 1) ls with
        | Some (y, ls) -> Some (x - y, ls)
        | None -> None)
      | _ -> None

  let rec muln n ls =
    if n < 0 then
      None
    else if n = 0 then
      Some (1, ls)
    else
      match ls with
      | VInt x :: ls -> (
        match muln (n - 1) ls with
        | Some (y, ls) -> Some (x * y, ls)
        | None -> None)
      | _ -> None

  let rec divn n ls =
    if n < 0 then
      None
    else if n = 0 then
      Some (1, ls)
    else
      match ls with
      | VInt x :: ls -> (
        match muln (n - 1) ls with
        | Some (0, ls) -> None
        | Some (y, ls) -> Some (x / y, ls)
        | None -> None)
      | _ -> None

  let rec popn n ls =
    if n < 0 then
      None
    else if n = 0 then
      Some ls
    else
      match ls with
      | _ :: ls -> (
        match popn (n - 1) ls with
        | Some ls -> Some ls
        | None -> None)
      | _ -> None

  let string_of_value v =
    match v with
    | VUnit -> "()"
    | VInt i -> string_of_int i
    | VBool b ->
      if b then
        "True"
      else
        "False"
    | VName n -> n
    | VClosure _ -> "<fun>"

  let rec tracen n ls =
    if n < 0 then
      None
    else if n = 0 then
      Some ([], ls)
    else
      match ls with
      | v :: ls -> (
        match tracen (n - 1) ls with
        | Some (log, ls) -> Some (string_of_value v :: log, ls)
        | None -> None)
      | _ -> None

  let rec eval (g : env) (l : env) (st : stack) (log : log) (cmds : cmds) :
      env * log * stack option =
    match cmds with
    | Push cst :: cmds -> (
      match cst with
      | Unit -> eval g l (VUnit :: st) log cmds
      | Int i -> eval g l (VInt i :: st) log cmds
      | Bool b -> eval g l (VBool b :: st) log cmds
      | Name n -> eval g l (VName n :: st) log cmds)
    | Pop n :: cmds -> (
      match popn n st with
      | Some st -> eval g l st log cmds
      | _ -> (g, log, None))
    | Add n :: cmds -> (
      match addn n st with
      | Some (x, st) -> eval g l (VInt x :: st) log cmds
      | _ -> (g, log, None))
    | Sub n :: cmds -> (
      match subn n st with
      | Some (x, st) -> eval g l (VInt x :: st) log cmds
      | _ -> (g, log, None))
    | Mul n :: cmds -> (
      match muln n st with
      | Some (x, st) -> eval g l (VInt x :: st) log cmds
      | _ -> (g, log, None))
    | Div n :: cmds -> (
      match divn n st with
      | Some (x, st) -> eval g l (VInt x :: st) log cmds
      | _ -> (g, log, None))
    | Equal :: cmds -> (
      match st with
      | VInt i1 :: VInt i2 :: st -> eval g l (VBool (i1 = i2) :: st) log cmds
      | _ -> (g, log, None))
    | Lte :: cmds -> (
      match st with
      | VInt i1 :: VInt i2 :: st -> eval g l (VBool (i1 <= i2) :: st) log cmds
      | _ -> (g, log, None))
    | And :: cmds -> (
      match st with
      | VBool b1 :: VBool b2 :: st -> eval g l (VBool (b1 && b2) :: st) log cmds
      | _ -> (g, log, None))
    | Or :: cmds -> (
      match st with
      | VBool b1 :: VBool b2 :: st -> eval g l (VBool (b1 || b2) :: st) log cmds
      | _ -> (g, log, None))
    | Not :: cmds -> (
      match st with
      | VBool b :: st -> eval g l (VBool (not b) :: st) log cmds
      | _ -> (g, log, None))
    | Trace n :: cmds -> (
      match tracen n st with
      | Some (lg, st) -> eval g l st (List.rev lg @ log) cmds
      | _ -> (g, log, None))
    | Local :: cmds -> (
      match st with
      | VName n :: v :: st -> eval g ((n, v) :: l) (VUnit :: st) log cmds
      | _ -> (g, log, None))
    | Global :: cmds -> (
      match st with
      | VName n :: v :: st -> eval ((n, v) :: g) l (VUnit :: st) log cmds
      | _ -> (g, log, None))
    | Lookup :: cmds -> (
      match st with
      | VName n :: st -> (
        match List.assoc_opt n (l @ g) with
        | Some v -> eval g l (v :: st) log cmds
        | None -> (g, log, None))
      | _ -> (g, log, None))
    | BeginEnd bod :: cmds -> (
      match eval g l [] log bod with
      | g, log, Some (v :: _) -> eval g l (v :: st) log cmds
      | g, log, _ -> (g, log, None))
    | IfElse (cmds1, cmds2) :: cmds -> (
      match st with
      | VBool b :: st ->
        if b then
          eval g l st log (cmds1 @ cmds)
        else
          eval g l st log (cmds2 @ cmds)
      | _ -> (g, log, None))
    | Fun (f, arg, bod) :: cmds ->
      let clo = VClosure (f, arg, bod, l) in
      eval g ((f, clo) :: l) st log cmds
    | Call :: cmds -> (
      match st with
      | VClosure (f, arg, bod, local) :: v :: st -> (
        let local = (arg, v) :: local in
        let local = (f, VClosure (f, arg, bod, local)) :: local in
        match eval g local [] log bod with
        | g, log, Some (v :: _) -> eval g l (v :: st) log cmds
        | g, log, _ -> (g, log, None))
      | _ -> (g, log, None))
    | Try bod :: cmds -> (
      match eval g l [] log bod with
      | g, log, Some (v :: _) -> eval g l (v :: st) log cmds
      | g, log, Some [] -> (g, log, None)
      | g, log, None -> eval g l st log cmds)
    | Switch cls :: cmds -> (
      match st with
      | VInt i :: st -> (
        match List.assoc_opt i cls with
        | Some cmds' -> eval g l st log (cmds' @ cmds)
        | None -> (g, log, None))
      | _ -> (g, log, None))
    | _ -> (g, log, Some st)
end

let _ =
  let src =
    if Array.length Sys.argv > 1 then
      Parser.readlines Sys.argv.(1)
    else
      ""
  in
  match Term.parse_prog src with
  | Some (m, []) ->
    let cmds = Comp.comp m in
    let log =
      match Interp.eval [] [] [] [] cmds with
      | _, log, Some _ -> log
      | _, _, None -> [ "Error" ]
    in
    printf "%a" Comp.pp cmds;
    printf "----------------interp result----------------\n";
    printf "%a" Interp.pp_log log
  | _ ->
    let log = [ "Error" ] in
    printf "%a" Interp.pp_log log