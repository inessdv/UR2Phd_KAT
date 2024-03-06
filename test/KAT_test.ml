open OUnit2
open KA_equiv.KAT_Set.Parser
open KA_equiv.KAT_Set
open KA_equiv.Common
open KA_equiv.KAT_Set.Print

let fromStr str = (parse_kat_unsafe str)

let epsilon_tests = "epslion test" >:::[
  "ϵ(a*) = 1" >:: (fun _ ->
    assert_equal true (epsilon (Atom.of_list ["b";"c"]) (fromStr "bpc")));
  "ϵ(a) = 0" >:: (fun _ -> 
    assert_equal false (epsilon (Atom.of_list ["b"]) (fromStr "bpc")));
]

let deriv_test = "deriv and linearization test" >::: [
  "D(ap)((ap+bq) = 1+0" >:: (fun _ ->
    assert_equal ~printer: pprint_sum
      (KATSet.singleton(fromStr "1+0")) (deriv (Atom.of_list ["a";"b"],"p") (linearization (fromStr "ap + bq"))));
]


(* let linearization_test = "linearization test" >::: [
  "D(bcp)((b+p)p) = p + 1" >:: (fun _ ->
    assert_equal ~printer: pprint 
      (fromStr "p + 1") (deriv 'a' (fromStr "a + b")));
] *)

(* let deriv_test = "equiv test" >::: [
  "D(bcp)((b+p)p) = p + 1" >:: (fun _ ->
    assert_equal ~printer: pprint_sum
      (KATSet.singleton(fromStr "1+0")) (deriv (Atom.of_list ["a";"b"],"p") (linearization (fromStr "ap + bq"))));
] *)