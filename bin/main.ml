open QCheck2
open KA_equiv

let exp_max_size = 2000
let bexp_max_size = 3
let max_p_bool_count = 800
let bench_count = 10

module GenExp = struct
  open GKAT_2

  let return = Gen.return
  let ( >|= ) = Gen.( >|= )
  let ( let* ) = Gen.( let* )

  let p_bool : bExp Gen.t =
    Gen.int_range 1 max_p_bool_count >|= fun n -> PBool n

  let b_exp size : bExp Gen.t =
    Gen.fix
      (fun self size ->
        if size <= 1 then p_bool
        else
          Gen.oneof
            [
              p_bool;
              (let* b_exp1 = self (size / 2) in
               let* b_exp2 = self (size / 2) in
               return @@ And (b_exp1, b_exp2));
              (let* b_exp1 = self (size / 2) in
               let* b_exp2 = self (size / 2) in
               return @@ Or (b_exp1, b_exp2));
              (let* b_exp' = self (size - 1) in
               return @@ Not b_exp');
            ])
      size

  module IntSet = Set.Make (Int)

  (** Generate a CF-GKAT expression *)
  let exp_sized bexp_size size =
    (* a function that generate a expression and all the labels in the expression,
       represented as ints*)
    (Gen.fix (fun self size ->
         (* all the expression with size 1 *)
         let size_one_lst =
           [
             (1, return @@ test One);
             ( 50,
               let* p = Gen.small_nat in
               return @@ Pact ("p" ^ string_of_int p) );
           ]
         in
         (* all the recursive expression generation (not size 1) *)
         let recursive_lst =
           [
             ( 15,
               let* e1 = self (size / 2) in
               let* e2 = self (size / 2) in
               return @@ Seq (e1, e2) );
             ( 3,
               let* b = b_exp bexp_size in
               let* e1 = self (size / 2) in
               let* e2 = self (size / 2) in
               return @@ If (b, e2, e1) );
             ( 1,
               let* b = b_exp bexp_size in
               let* e_loop = self (size - 1) in
               return @@ While (b, e_loop) );
           ]
         in
         if size <= 1 then Gen.frequency size_one_lst
         else Gen.frequency @@ recursive_lst))
      (* default configuration for generating expressions:
         not in loop, with the input labels as start, and the input size*)
      size

  let gen_eq_bexp size =
    Gen.fix
      (fun self size ->
        if size <= 1 then
          Gen.oneof
            [
              (* reflexivity *)
              (let* b = b_exp size in
               return @@ (b, b));
            ]
        else
          Gen.oneof
            [
              (* symmetry *)
              (let* b1, b2 = self (size - 1) in
               return @@ (b2, b1));
              (* congurence *)
              (let* b1, b2 = self (size - 1) in
               return (Not b1, Not b2));
              (let* b1, b1' = self (size / 2) in
               let* b2, b2' = self (size / 2) in
               return (And (b1, b2), And (b1', b2')));
              (let* b1, b1' = self (size / 2) in
               let* b2, b2' = self (size / 2) in
               return (Or (b1, b2), Or (b1', b2')));
              (* commutativity *)
              (let* b1, b1' = self (size / 2) in
               let* b2, b2' = self (size / 2) in
               return (Or (b1, b2), Or (b2', b1')));
              (let* b1, b1' = self (size / 2) in
               let* b2, b2' = self (size / 2) in
               return (And (b1, b2), And (b2', b1')));
              (* Associativity *)
              (let* b1, b1' = self (size / 3) in
               let* b2, b2' = self (size / 3) in
               let* b3, b3' = self (size / 3) in
               return (Or (b1, Or (b2, b3)), Or (Or (b1', b2'), b3')));
              (let* b1, b1' = self (size / 3) in
               let* b2, b2' = self (size / 3) in
               let* b3, b3' = self (size / 3) in
               return (And (b1, And (b2, b3)), And (And (b1', b2'), b3')));
              (* Identity *)
              (let* b1, b1' = self (size - 1) in
               return (And (b1, One), b1'));
              (let* b1, b1' = self (size - 1) in
               return (And (One, b1), b1'));
              (* (let* b1 = b_exp (size - 1) in
                  return (And (b1, Zero), Zero));
                 (let* b1 = b_exp (size - 1) in
                  return (And (Zero, b1), Zero)); *)
              (let* b1, b1' = self (size - 1) in
               return (Or (b1, Zero), b1'));
              (let* b1, b1' = self (size - 1) in
               return (Or (Zero, b1), b1'));
              (let* b1 = b_exp (size - 1) in
               return (Or (b1, One), One));
              (let* b1 = b_exp (size - 1) in
               return (Or (One, b1), One));
              (* complement *)
              (let* b1, b2 = self (size / 2) in
               return (Or (Not b1, b2), One));
              (let* b1, b2 = self (size / 2) in
               return (And (Not b1, b2), Zero));
              (* idempotence *)
              (let* b1, b2 = self (size / 2) in
               return (Or (b1, b2), b1));
              (let* b1, b2 = self (size / 2) in
               return (Or (b1, b2), b2));
              (let* b1, b2 = self (size / 2) in
               return (And (b1, b2), b1));
              (let* b1, b2 = self (size / 2) in
               return (And (b1, b2), b2));
            ])
      size

  (** given a pair of equal expression, generate *)
  let gen_eq_exp =
    Gen.fix
      (fun self size ->
        if size <= 1 then
          Gen.frequency
            [
              (* primitive action *)
              ( 100,
                let* label = Gen.small_nat in
                return (Pact (string_of_int label), Pact (string_of_int label))
              );
              (* skip *)
              (1, return (Test One, Test One));
            ]
        else
          Gen.frequency
            [
              (* reflexivity *)
              ( 30,
                let* e = exp_sized bexp_max_size size in
                return @@ (e, e) );
              (* symmetry *)
              ( 40,
                let* e1, e2 = self (size - 1) in
                return @@ (e2, e1) );
              (* equal test *)
              (* (let* b1, b2 = gen_eq_bexp bexp_max_size in
                 return @@ (Test b1, Test b2)); *)
              (* congurence *)
              ( 50,
                let* e1, e1' = self (size / 2) in
                let* e2, e2' = self (size / 2) in
                return @@ (Seq (e1, e2), Seq (e1', e2')) );
              ( 20,
                let* b, b' = gen_eq_bexp bexp_max_size in
                let* e1, e1' = self (size / 2) in
                let* e2, e2' = self (size / 2) in
                return @@ (If (b, e1, e2), If (b', e1', e2')) );
              ( 2,
                let* b, b' = gen_eq_bexp bexp_max_size in
                let* e, e' = self (size - 1) in
                return @@ (While (b, e), While (b', e')) );
              (* idempotence *)
              ( 2,
                let* b = b_exp bexp_max_size in
                let* e, e' = self (size / 2) in
                return @@ (If (b, e, e'), e) );
              (* skew commutativity *)
              ( 2,
                let* b, b' = gen_eq_bexp bexp_max_size in
                let* e1, e1' = self (size / 2) in
                let* e2, e2' = self (size / 2) in
                return @@ (If (b, e1, e2), If (Not b', e2', e1')) );
              (* skew assoc *)
              ( 2,
                let* b, b' = gen_eq_bexp bexp_max_size in
                let* c, c' = gen_eq_bexp bexp_max_size in
                let* e1, e1' = self (size / 3) in
                let* e2, e2' = self (size / 3) in
                let* e3, e3' = self (size / 3) in
                return
                @@ ( If (c, If (b, e1, e2), e3),
                     If (And (b', c'), e1', If (c, e2', e3')) ) );
              (* guardedness *)
              ( 2,
                let* b, b' = gen_eq_bexp bexp_max_size in
                let* e1, e1' = self (size / 2) in
                let* e2, e2' = self (size / 2) in
                return @@ (If (b, e1, e2), If (b', Seq (Test b', e1'), e2')) );
              (* right distribute *)
              ( 2,
                let* b, b' = gen_eq_bexp bexp_max_size in
                let* e1, e1' = self (size / 3) in
                let* e2, e2' = self (size / 3) in
                let* e3, e3' = self (size / 3) in
                return
                @@ ( Seq (If (b, e1, e2), e3),
                     If (b', Seq (e1', e3'), Seq (e2', e3')) ) );
              (* associativity *)
              ( 10,
                let* e1, e1' = self (size / 3) in
                let* e2, e2' = self (size / 3) in
                let* e3, e3' = self (size / 3) in
                return @@ (Seq (e1, Seq (e2, e3)), Seq (Seq (e1', e2'), e3')) );
              (* identities *)
              (* (let* e = exp_sized bexp_max_size (size - 1) in
                  return @@ (Seq (Test Zero, e), Test Zero));
                 (let* e = exp_sized bexp_max_size (size - 1) in
                  return @@ (Seq (e, Test Zero), Test Zero)); *)
              ( 2,
                let* e, e' = self (size - 1) in
                return @@ (Seq (Test One, e), e') );
              ( 2,
                let* e, e' = self (size - 1) in
                return @@ (Seq (e, Test One), e') );
              (* unrolling *)
              ( 5,
                let* b, b' = gen_eq_bexp bexp_max_size in
                let* e, e' = self (size / 2) in
                return
                @@ (While (b, e), If (b', Seq (e', While (b, e')), Test One)) );
              (* tightening *)
              ( 5,
                let* b, b' = gen_eq_bexp bexp_max_size in
                let* c, c' = gen_eq_bexp bexp_max_size in
                let* e, e' = self (size - 1) in
                return
                @@ ( While (b, If (c, e, Test One)),
                     While (b', Seq (Test c', e')) ) );
            ])
      exp_max_size
  (* default size of two expression *)
end

let rec from_be_to_hashcons (be : GKAT_2.bExp) : GKAT_Symb.BExp.t =
  match be with
  | Zero -> GKAT_Symb.BExp.zero
  | One -> GKAT_Symb.BExp.one
  | PBool str -> GKAT_Symb.BExp.pBool str
  | Or (b1, b2) ->
      GKAT_Symb.BExp.b_or (from_be_to_hashcons b1) (from_be_to_hashcons b2)
  | And (b1, b2) ->
      GKAT_Symb.BExp.b_and (from_be_to_hashcons b1) (from_be_to_hashcons b2)
  | Not b1 -> GKAT_Symb.BExp.b_not (from_be_to_hashcons b1)

let rec from_gkat_to_hashcon (exp1 : GKAT_2.gkat) : GKAT_Symb.Exp.t =
  match exp1 with
  | Pact p -> GKAT_Symb.Exp.p_act p
  | Seq (e, f) ->
      GKAT_Symb.Exp.seq (from_gkat_to_hashcon e) (from_gkat_to_hashcon f)
  | If (be, e, f) ->
      GKAT_Symb.Exp.if_then_else (from_be_to_hashcons be)
        (from_gkat_to_hashcon e) (from_gkat_to_hashcon f)
  | Test be -> GKAT_Symb.Exp.test (from_be_to_hashcons be)
  | While (be, e) ->
      GKAT_Symb.Exp.while_do (from_be_to_hashcons be) (from_gkat_to_hashcon e)

let bench_rand_exp_symb =
  Test.make ~count:bench_count
    ~name:"benchmarking symbolic algorithm with generated equivalence"
    (Gen.pair
       (GenExp.exp_sized bexp_max_size exp_max_size)
       (GenExp.exp_sized bexp_max_size exp_max_size))
    (fun (e1, e2) ->
      let e1_hashcons = from_gkat_to_hashcon e1 in
      let e2_hashcons = from_gkat_to_hashcon e2 in
      print_endline
        ("exp1: p_acts: "
        ^ (string_of_int @@ GKAT_Symb.Exp.num_pact e1_hashcons)
        ^ "; tests: "
        ^ (string_of_int @@ GKAT_Symb.Exp.num_bexp e1_hashcons)
        ^ "; if's: "
        ^ (string_of_int @@ GKAT_Symb.Exp.num_if e1_hashcons)
        ^ "; seq's: "
        ^ (string_of_int @@ GKAT_Symb.Exp.num_seq e1_hashcons)
        ^ "; while's: " ^ string_of_int
        @@ GKAT_Symb.Exp.num_while e1_hashcons);
      print_endline
        ("exp2: p_acts: "
        ^ (string_of_int @@ GKAT_Symb.Exp.num_pact e2_hashcons)
        ^ "; tests: "
        ^ (string_of_int @@ GKAT_Symb.Exp.num_bexp e2_hashcons)
        ^ "; if's: "
        ^ (string_of_int @@ GKAT_Symb.Exp.num_if e2_hashcons)
        ^ "; seq's: "
        ^ (string_of_int @@ GKAT_Symb.Exp.num_seq e2_hashcons)
        ^ "; while's: " ^ string_of_int
        @@ GKAT_Symb.Exp.num_while e2_hashcons);
      let start_time = Sys.time () in
      print_endline
        ("result: " ^ string_of_bool
        @@ GKAT_Symb.Derivatives.equiv e1_hashcons e2_hashcons);
      print_endline
        ("Execution time: " ^ string_of_float (Sys.time () -. start_time) ^ "s");
      print_newline ();
      true)

let bench_equiv_symb =
  Test.make ~count:bench_count
    ~name:"benchmarking symbolic algorithm with generated equivalence"
    GenExp.gen_eq_exp (fun (e1, e2) ->
      let e1_hashcons = from_gkat_to_hashcon e1 in
      let e2_hashcons = from_gkat_to_hashcon e2 in
      print_endline
        ("exp1: p_acts: "
        ^ (string_of_int @@ GKAT_Symb.Exp.num_pact e1_hashcons)
        ^ "; tests: "
        ^ (string_of_int @@ GKAT_Symb.Exp.num_bexp e1_hashcons)
        ^ "; if's: "
        ^ (string_of_int @@ GKAT_Symb.Exp.num_if e1_hashcons)
        ^ "; seq's: "
        ^ (string_of_int @@ GKAT_Symb.Exp.num_seq e1_hashcons)
        ^ "; while's: " ^ string_of_int
        @@ GKAT_Symb.Exp.num_while e1_hashcons);
      print_endline
        ("exp2: p_acts: "
        ^ (string_of_int @@ GKAT_Symb.Exp.num_pact e2_hashcons)
        ^ "; tests: "
        ^ (string_of_int @@ GKAT_Symb.Exp.num_bexp e2_hashcons)
        ^ "; if's: "
        ^ (string_of_int @@ GKAT_Symb.Exp.num_if e2_hashcons)
        ^ "; seq's: "
        ^ (string_of_int @@ GKAT_Symb.Exp.num_seq e2_hashcons)
        ^ "; while's: " ^ string_of_int
        @@ GKAT_Symb.Exp.num_while e2_hashcons);
      let start_time = Sys.time () in
      let equiv_res = GKAT_Symb.Derivatives.equiv e1_hashcons e2_hashcons in
      print_endline
        ("Execution time: " ^ string_of_float (Sys.time () -. start_time) ^ "s");
      print_newline ();
      equiv_res)

let () =
  print_newline ();
  print_endline "Testing random expressions with symbolic algorithm";
  print_newline ();
  Test.check_exn bench_rand_exp_symb;
  print_newline ();
  print_endline "Testing equivalent expressions with symbolic algorithm";
  print_newline ();
  Test.check_exn bench_equiv_symb
