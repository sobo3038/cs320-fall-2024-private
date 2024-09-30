let last_function_standing funcs start pred =
  let rec lifespan f s p count =
    if p (f s) then count
    else lifespan f (f s) p (count + 1)
  in

  let calculate_lifespans fs =
    List.map (fun f -> (f, lifespan f start pred 0)) fs
  in

  let rec find_max_lifespan lifespans current_max current_func duplicates =
    match lifespans with
    | [] -> if duplicates then None else Some current_func
    | (f, l) :: rest ->
        if l > current_max then
          find_max_lifespan rest l f false
        else if l = current_max then
          find_max_lifespan rest current_max current_func true
        else
          find_max_lifespan rest current_max current_func duplicates
  in

  let lifespans = calculate_lifespans funcs in
  match lifespans with
  | [] -> None
  | (f, l) :: rest -> find_max_lifespan rest l f false