open OUnit2
open KA_equiv.KAT_Set.Parser
open KA_equiv.KAT_Set

let fromStr str = (parse_kat_unsafe str)

let epsilon_tests = "epslion test" >:::[
  "ϵ(a*) = 1" >:: (fun _ ->
    assert_equal true (epsilon (fromStr "bc")(fromStr "bpc")));
  "ϵ(a) = 0" >:: (fun _ -> 
    assert_equal false (epsilon (fromStr "b")(fromStr "bpc")));
]

let deriv_test = "deriv test" >::: [
  "D(bcp)((b+p)p) = p + 1" >:: (fun _ ->
    assert_equal ~printer: pprint 
      (fromStr "p + 1") (deriv 'a' (fromStr "a + b")));
]