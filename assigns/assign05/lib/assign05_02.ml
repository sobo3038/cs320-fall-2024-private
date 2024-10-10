type 'a tree =
  | Leaf
  | Node of 'a * 'a tree * 'a tree

let sum_tr t =
  let rec go t cont =
    match t with
    | Leaf -> cont 0
    | Node (x, left, right) ->
        go left (fun sum_left ->
          go right (fun sum_right ->
            cont (x + sum_left + sum_right)))
  in
  go t (fun x -> x)