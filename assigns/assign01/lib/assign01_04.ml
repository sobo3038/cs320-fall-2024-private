open Assign01_02 
open Assign01_03  

let to_string number =
  let rec build_factor_string n index result =
    if n = 1 then
      result
    else
      let prime = nth_prime index in      
      let count = nth n index in
      let newvalueforn = n / (int_of_float (float_of_int prime ** float_of_int count)) in
      
      let new_result = 
        if result = "" then 
          string_of_int count
        else 
          result ^ "; " ^ string_of_int count
      in
      build_factor_string newvalueforn (index + 1) new_result
  in
  
  let factors = build_factor_string number 0 "" in "[" ^ factors ^ "]"


(*Source Syntax: 
https://ocaml.org/manual/5.2/expr.html used for expressions
https://ocaml.org/manual/5.2/api/String.html#concat used to help me with concatination synrax
*)