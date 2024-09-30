let last_function_standing funcs start pred =
  let rec lifespan f s p count max_steps =
    if count >= max_steps then count 
    else if p (f s) then count
    else lifespan f (f s) p (count + 1) max_steps
  in

  let calculate_lifespans fs =
    let max_steps = 10000 in
    List.map (fun f -> (f, lifespan f start pred 0 max_steps)) fs
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
