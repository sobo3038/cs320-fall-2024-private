let gen_fib l k =
  let len = List.length l in
  
  let rec sum_last n lst =
    if n = 0 then 0
    else match lst with
         | [] -> 0
         | x::xs -> x + sum_last (n-1) xs
  in
  
  let rec helper acc n =
    if n < len then List.nth l n
    else
      let new_sum = sum_last len acc in
      if n = k then new_sum
      else helper (new_sum :: acc) (n + 1)
  in
  
  if k < len then List.nth l k
  else helper (List.rev l) len
  

  (*Syntax: https://cs3110.github.io/textbook/chapters/data/lists.html i also used this one again
  https://ocaml.org/manual/5.2/api/List.html for .rev and .nth*)