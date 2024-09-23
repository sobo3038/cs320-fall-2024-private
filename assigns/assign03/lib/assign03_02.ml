let gen_fib l k =
  let rec length lst =
    match lst with
    | [] -> 0
    | _::xs -> 1 + length xs
  in
  
  let len = length l in
  
  let rec take n lst =
    if n = 0 then []
    else match lst with
         | [] -> []
         | x::xs -> x :: take (n-1) xs
  in
  
  let rec sum lst =
    match lst with
    | [] -> 0
    | x::xs -> x + sum xs
  in
  
  let rec helper acc n =
    if n < len then List.nth l n
    else
      let new_sum = sum (take len acc) in
      if n = k then new_sum
      else helper (new_sum :: acc) (n + 1)
  in
  
  if k < len then List.nth l k
  else helper (List.rev l) len