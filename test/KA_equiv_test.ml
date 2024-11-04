open OUnit2

let _ =
  run_test_tt_main
    ("all tests"
    >::: [
           KA_test.epsilon_tests;
           KA_test.deriv_test;
           KAT_test.epsilon_tests;
           KAT_test.deriv_test;
           GKAT_test_qcheck.test_equiv_deriv; 
           GKAT_test_qcheck.test_equiv_aut;
           GKAT_test_qcheck.test_equiv_Z3symb;
           (**GKAT_test_qcheck.test_equiv_MLBDDsymb;
           GKAT_test_qcheck.test_Z3symb_vs_gkat; 
           GKAT_test_qcheck.test_MLBDDsymb_vs_gkat; 
           GKAT_test_qcheck.test_Z3symb_vs_aut;
<<<<<<< HEAD
           GKAT_test_qcheck.test_MLBDDsymb_vs_aut;
           GKAT_test_qcheck.test_equiv_Asymb
=======
           GKAT_test_qcheck.test_MLBDDsymb_vs_aut**)
>>>>>>> ad4ba0c (test_equiv_Z3symb only 20)
  ])
