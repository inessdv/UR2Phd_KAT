let rec equiv (re: (('a kleene list * 'a kleene list) list) * (('a kleene list * 'a kleene list) list)): bool =
  match re with
  |([],_)-> true
  |(r1,r2)->if (checkEmpty r1)==false then false
  else 
  let r2=unique(r1@r2) 
  in  (*Updated Head*)
  let deri=List.concat(List.map (fun x -> derivatives x) r1) in
  let der= List.fold_left(fun acc x-> if (List.mem x r2) then acc else x::acc) [] deri  (*derivatives after filtering*)
  in equiv (der,r2)