let is_prime n =
  let rec check d =
    if d * d > n then true
    else if n mod d = 0 then false
    else check (d + 1)
  in
  n > 1 && check 2