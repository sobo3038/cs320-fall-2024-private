(*Problem 1: Integer powers*)
let rec pow n k =
  if k = 0 then 1 (*base case*)
  else n * pow n (k - 1) (*rec case*)


(*Syntax Source: https://ocaml.org/docs/loops-recursion*)