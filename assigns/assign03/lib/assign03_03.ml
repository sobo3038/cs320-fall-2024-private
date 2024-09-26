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


(*Syntax: https://courses.cs.cornell.edu/cs3110/2021sp/textbook/data/trees.html for help with the trees
  https://www.perplexity.ai/search/hi-GmEn67GUSKmlHQsGWixpCQ this video from readings https://cs3110.github.io/textbook/chapters/data/trees.html
  *)
