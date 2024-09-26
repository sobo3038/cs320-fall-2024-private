let rec add_to_map map key value =
  match map with
  | [] -> [(key, value)]
  | (k, v) :: tail when k = key -> (k, v + value) :: tail
  | kv :: tail -> kv :: add_to_map tail key value

let mk_unique_keys alst =
  List.fold_left (fun acc (key, value) -> add_to_map acc key value) [] alst

(*Sources: https://pl.cs.jhu.edu/pl2/lecture/more-fp.html used for fold left syntax
https://ocaml.org/docs/lists also used for fold left syntax and examples
https://cs3110.github.io/textbook/chapters/data/lists.html *)