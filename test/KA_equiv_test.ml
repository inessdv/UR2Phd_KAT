open OUnit2

let _ =
  run_test_tt_main
    ("all tests"
    >::: [
           KA_test.epsilon_tests;
           KA_test.deriv_test;
           KAT_test.epsilon_tests;
           KAT_test.deriv_test;
         ])
