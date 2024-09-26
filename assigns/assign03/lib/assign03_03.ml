type tree = 
  | Leaf of int
  | Node of tree list
let rec collect_terminals t =
  match t with
  | Leaf _ -> [t]
  | Node [] -> [t]
  | Node children -> List.concat (List.map collect_terminals children)
let rec collapse h t =
  match h with
  | 0 -> t  
  | _ -> 
    match t with
    | Leaf _ -> t  
    | Node [] -> t 
    | Node children ->
      if h = 1 then 
        Node (List.concat (List.map collect_terminals children)) 
      else 
        Node (List.map (collapse (h - 1)) children) 
