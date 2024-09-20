(*problem 3: walking distance*)

type dir = North | South | East | West
type path = dir list

let dist (dirs: path) : float =
  let startx = 0 in
  let starty = 0 in
  
  let move (x, y) direction =
    if direction = North then
      (x, y + 1)
    else if direction = South then
      (x, y - 1)
    else if direction = East then
      (x + 1, y)
    else  
      (x - 1, y)
  in

  let current_position = (startx, starty) in

  let final_position =
    List.fold_left (fun (x, y) direction -> move (x, y) direction) current_position dirs
  in

  let finalx, finaly = final_position in
  let sum_sq = (finalx * finalx) + (finaly * finaly) in
  let float_sum = float_of_int sum_sq in
  let final_dist = sqrt float_sum in
  final_dist

(*
  https://ocaml.org/manual/5.2/api/List.html foir fold left 
  https://stackoverflow.com/questions/38669012/type-conversion-with-float-of-int for float and also this https://ocaml.org/manual/4.07/libref/Float.html
  https://cs3110.github.io/textbook/chapters/basics/functions.html
*)

