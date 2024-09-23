let group l =
  let rec aux current_group groups = function
    | [] -> 
        if current_group = [] then Some (List.rev groups)
        else Some (List.rev (List.rev current_group :: groups))
    | 0 :: rest ->
        if current_group = [] then None
        else aux [] (List.rev current_group :: groups) rest
    | x :: rest ->
        match current_group with
        | [] -> aux [x] groups rest
        | y :: _ when (x > 0 && y > 0) || (x < 0 && y < 0) ->
            aux (x :: current_group) groups rest
        | _ -> None
  in
  let validate_zeros l =
    let rec check_zeros prev = function
      | [] -> true
      | 0 :: rest ->
          (match prev, rest with
           | Some x, y :: _ when x * y < 0 -> check_zeros (Some y) rest
           | _ -> false)
      | x :: rest -> check_zeros (Some x) rest
    in
    check_zeros None l
  in
  if not (validate_zeros l) then None
  else aux [] [] l