open KA_equiv.Common
open KA_equiv.GKAT.Automaton
open KA_equiv.GKAT
open OUnit2

(* circular automata, it will loop forever. *)
let automaton1 : t =
  {
    start = 1;
    trans_map =
      Trans.map_of_list
        [
          ( 1,
            [
              (PBoolSet.empty, To (2, "p1"));
              (PBoolSet.singleton "b", To (2, "p2"));
            ] );
          ( 2,
            [
              (PBoolSet.empty, To (3, "p3"));
              (PBoolSet.singleton "b", To (3, "p3"));
            ] );
          ( 3,
            [
              (PBoolSet.empty, To (1, "p3"));
              (PBoolSet.singleton "b", To (1, "p3"));
            ] );
        ];
  }

(* start state is circular, but every other state is live *)
let automaton2 : t =
  {
    start = 1;
    trans_map =
      Trans.map_of_list
        [
          ( 1,
            [
              (PBoolSet.empty, To (1, "p1"));
              (PBoolSet.singleton "b", To (1, "p1"));
            ] );
          (2, [ (PBoolSet.empty, Accept); (PBoolSet.singleton "b", Accept) ]);
          (3, [ (PBoolSet.empty, Accept); (PBoolSet.singleton "b", Accept) ]);
        ];
  }

(* a automata that every state is live *)
let automaton3 : t =
  {
    start = 1;
    trans_map =
      Trans.map_of_list
        [
          ( 1,
            [
              (PBoolSet.empty, To (2, "p2"));
              (PBoolSet.singleton "b", To (1, "p1"));
            ] );
          ( 2,
            [
              (PBoolSet.empty, To (3, "p2"));
              (PBoolSet.singleton "b", To (1, "p1"));
            ] );
          ( 3,
            [ (PBoolSet.empty, Accept); (PBoolSet.singleton "b", To (1, "p1")) ]
          );
        ];
  }

(* The automata that almost equal to automata 3,
    except the action from 1 to 2 is different *)
let automaton4 : t =
  {
    start = 1;
    trans_map =
      Trans.map_of_list
        [
          ( 1,
            [
              (PBoolSet.empty, To (2, "p1"));
              (PBoolSet.singleton "b", To (1, "p1"));
            ] );
          ( 2,
            [
              (PBoolSet.empty, To (3, "p2"));
              (PBoolSet.singleton "b", To (1, "p1"));
            ] );
          ( 3,
            [ (PBoolSet.empty, Accept); (PBoolSet.singleton "b", To (1, "p1")) ]
          );
        ];
  }

(* a automata that is equivalent to automata 3 *)
let automaton5 : t =
  {
    start = 1;
    trans_map =
      Trans.map_of_list
        [
          ( 1,
            [
              (PBoolSet.empty, To (2, "p2"));
              (PBoolSet.singleton "b", To (1, "p1"));
            ] );
          ( 2,
            [
              (PBoolSet.empty, To (3, "p2"));
              (PBoolSet.singleton "b", To (4, "p1"));
            ] );
          ( 3,
            [ (PBoolSet.empty, Accept); (PBoolSet.singleton "b", To (1, "p1")) ]
          );
          ( 4,
            [
              (PBoolSet.empty, To (5, "p2"));
              (PBoolSet.singleton "b", To (4, "p1"));
            ] );
          ( 5,
            [
              (PBoolSet.empty, To (3, "p2"));
              (PBoolSet.singleton "b", To (1, "p1"));
            ] );
        ];
  }

(* an automata where 4 and 5 are dead state
    and state 8 is the same as state 1, and state 9 is the same as state 2 *)
let automaton6 : t =
  {
    start = 1;
    trans_map =
      Trans.map_of_list
        [
          (1, [ (PBoolSet.empty, To (2, "p2")) ]);
          ( 2,
            [
              (PBoolSet.empty, To (3, "p2"));
              (PBoolSet.singleton "b", To (8, "p1"));
            ] );
          ( 3,
            [ (PBoolSet.empty, Accept); (PBoolSet.singleton "b", To (5, "p1")) ]
          );
          (4, [ (PBoolSet.singleton "b", To (5, "p3")) ]);
          (5, [ (PBoolSet.empty, To (4, "p2")) ]);
          ( 8,
            [
              (PBoolSet.empty, To (9, "p2"));
              (PBoolSet.singleton "b", To (4, "p1"));
            ] );
          ( 9,
            [
              (PBoolSet.empty, To (3, "p2"));
              (PBoolSet.singleton "b", To (1, "p1"));
            ] );
        ]
      (* 1 -> \atom -> if atom == Set.fromList [1] then Reject else To 2 2
            2 -> \atom -> if atom == Set.fromList [1] then To 8 1 else To 3 2
            3 -> \atom -> if atom == Set.fromList [1] then To 5 1 else Accept
            4 -> \atom -> if atom == Set.fromList [1] then To 5 3 else Reject
            5 -> \atom -> if atom == Set.fromList [1] then Reject else To 4 2
            8 -> \atom -> if atom == Set.fromList [1] then To 4 1 else To 9 2
            9 -> \atom -> if atom == Set.fromList [1] then To 1 1 else To 3 2 *);
  }

(* an automata that is equal to automata6
      with 4, 6, 7 being dead state
      with 8 the same as 1 *)
let automaton7 : t =
  {
    start = 1;
    trans_map =
      Trans.map_of_list
        [
          ( 1,
            [
              (PBoolSet.empty, To (2, "p2"));
              (PBoolSet.singleton "b", To (6, "p2"));
            ] );
          ( 2,
            [
              (PBoolSet.empty, To (3, "p2"));
              (PBoolSet.singleton "b", To (8, "p1"));
            ] );
          ( 3,
            [ (PBoolSet.empty, Accept); (PBoolSet.singleton "b", To (4, "p2")) ]
          );
          (4, [ (PBoolSet.singleton "b", To (7, "p3")) ]);
          ( 6,
            [
              (PBoolSet.empty, To (7, "p5"));
              (PBoolSet.singleton "b", To (7, "p4"));
            ] );
          ( 8,
            [
              (PBoolSet.empty, To (2, "p2"));
              (PBoolSet.singleton "b", To (4, "p3"));
            ] );
        ]
      (* 1 -> \atom -> if atom == Set.fromList [1] then To 6 2 else To 2 2
         2 -> \atom -> if atom == Set.fromList [1] then To 8 1 else To 3 2
         3 -> \atom -> if atom == Set.fromList [1] then To 4 2 else Accept
         4 -> \atom -> if atom == Set.fromList [1] then To 7 3 else Reject
         6 -> \atom -> if atom == Set.fromList [1] then To 7 4 else To 7 5
         7 -> (const Reject)
         8 -> \atom -> if atom == Set.fromList [1] then To 4 3 else To 2 2 *);
  }

let normalization_tests =
  "normalization test"
  >::: [
         ( "normalize automata1 should get empty automata." >:: fun _ ->
           assert_equal ~cmp:Trans.map_equal ~printer:Trans.pprint_map StateMap.empty
             (normalize automaton1).trans_map );
         ( "normalize automata2 should remove transition from 1." >:: fun _ ->
           assert_equal ~cmp:Trans.map_equal ~printer:Trans.pprint_map
             (Trans.map_of_list
                [
                  ( 2,
                    [
                      (PBoolSet.empty, Accept); (PBoolSet.singleton "b", Accept);
                    ] );
                  ( 3,
                    [
                      (PBoolSet.empty, Accept); (PBoolSet.singleton "b", Accept);
                    ] );
                ])
             (normalize automaton2).trans_map );
         ( "normalize automata3 should get itself." >:: fun _ ->
           assert_equal ~cmp:Trans.map_equal ~printer:Trans.pprint_map automaton3.trans_map
             (normalize automaton3).trans_map );
       ]

let equiv_tests =
  "equality test"
  >::: [
         ( "automata1 is equal automata2." >:: fun _ ->
           assert_equal true @@ equiv automaton1 automaton2 );
         ( "automata1 is not equal automata3." >:: fun _ ->
           assert_equal false @@ equiv automaton1 automaton3 );
         ( "automata3 is not equal automata4." >:: fun _ ->
           assert_equal false @@ equiv automaton3 automaton4 );
         ( "automata3 is not equal automata6." >:: fun _ ->
           assert_equal false @@ equiv automaton3 automaton6 );
         ( "automata5 is equal to automata3." >:: fun _ ->
           assert_equal true @@ equiv automaton5 automaton3 );
         ( "automata6 is equal to automata7." >:: fun _ ->
           assert_equal true @@ equiv automaton6 automaton7 );
       ]
