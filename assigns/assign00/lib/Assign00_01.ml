let sqrt n =
  let rec findsqrt k =
    if k * k >= n then k  
    else findsqrt (k + 1)  
  in
  if n < 0 then -1 
  else findsqrt 0 