open Assign01_02

let nth s i =
  let prime = nth_prime i in
  let rec count s inc =
    if s mod prime = 0 then
      count (s / prime) (inc + 1)
    else
      inc
  in
  count s 0


(*Source Syntax: 
https://cs3110.github.io/textbook/chapters/basics/expressions.html using sec2.3 primitive types and values
*)