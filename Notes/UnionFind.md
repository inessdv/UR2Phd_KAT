# A UnionFind Based Algorithm For KAT

Ocaml UnionFind Doc: 
- How to Construct a Union Find module: https://v3.ocaml.org/p/unionFind/latest/doc/index.html
- Functions: https://v3.ocaml.org/p/unionFind/latest/doc/UnionFind/index.html

PseudoCode: 
```Ocaml
(*build the union find module, I am not sure this will work TBH*)
module UF = UnionFind.Make(UnionFind.StoreTransactionalRef)

(*Derivatives As Pairs*)
fun equivCheck (todo: KATPairSets.t) : bool = 
    case Set.chooseopt todo of 
    (*nothing left to check, done*)
    | None -> True 
    (*checking sum1 and sum2*)
    | Some (sum1, sum2) ->
        let rest = KATPairSets.delete (sum1, sum2) todo
        (*find the representative of rep1 and rep2*)
        let rep1 = UF.find (UF.make sum1) in
        let rep2 = UF.find (UF.make sum2) in

        (*they have the same representative hence bisimular,
        only need to check the rest*)
        if UF.eq rep1 rep2 
            then equivCheck rest
        (*their epsilon is not the same, hence not bisimular*)
        else if ep_sum sum1 != ep_sum sum2 
            then False
        (*check all the derivatives*)
        else 
            (*marks the two derivative as bisimular*)
            let _ = UF.union sum1 sum2 in 
            (*append the derivatives to the rest*)
            let deriv_pairs = deriv_sum_pairs (sum1, sum2) in 
            let new_todo = KATPairSets.union rest deriv_pairs in 
            equivCheck new_todo
```