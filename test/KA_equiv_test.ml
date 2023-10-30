open OUnit2
open KA_test



let _ = run_test_tt_main ("all tests" >::: [
  epsilon_tests; deriv_test
])
