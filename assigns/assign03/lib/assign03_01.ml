let rec add_to_map map key value =
  match map with
  | [] -> [(key, value)]
  | (k, v) :: tail when k = key -> (k, v + value) :: tail
  | kv :: tail -> kv :: add_to_map tail key value

let mk_unique_keys alst =
  List.fold_left (fun acc (key, value) -> add_to_map acc key value) [] alst
