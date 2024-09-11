let is_prime n = (*this function is from the last assignment*)
  let rec check d =
    if d * d > n then true
    else if n mod d = 0 then false
    else check (d + 1)
  in
  n > 1 && check 2

  let nth_prime n =
    let rec next_prime num =
      if is_prime num then num
      else next_prime (num + 1)
    in
    
    let rec find_nth_prime count current = (* this wil find the nth prime *)
      if count = n then current
      else
        let next = next_prime (current + 1) in
        find_nth_prime (count + 1) next
    in
    find_nth_prime 0 2

(*Syntax Source:
   https://cs3110.github.io/textbook/chapters/basics/functions.html?highlight=tail+recursion understanding tail recursion
   https://ocaml.org/exercises used as examples
   *)