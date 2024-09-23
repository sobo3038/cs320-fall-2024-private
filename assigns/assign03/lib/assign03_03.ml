type tree = 
  | Leaf of int
  | Node of tree list

(* Helper function to collect all terminal elements (i.e., leaves and empty nodes) in a tree *)
let rec collect_terminals t =
  match t with
  | Leaf _ -> [t]
  | Node [] -> [t]
  | Node children -> List.concat (List.map collect_terminals children)

(* Main function to collapse the tree to height h *)
let rec collapse h t =
  match h with
  | 0 -> t  (* If h is 0, we return the original tree *)
  | _ -> 
    match t with
    | Leaf _ -> t  (* A leaf is already terminal, so we return it as-is *)
    | Node [] -> t (* An empty node is terminal, so we return it as-is *)
    | Node children ->
      if h = 1 then 
        Node (List.concat (List.map collect_terminals children)) (* Collapse the tree to height 1 *)
      else 
        Node (List.map (collapse (h - 1)) children) (* Recursively collapse the tree *)
