(*problem 2: matrices*)

type matrix = {
  entries : float list list;
  rows : int;
  cols : int;
}

let mk_matrix (entries: float list) ((r, c): int * int) : matrix =
  let rec splitlist lst n =
    if List.length lst = 0 then
      []
    else
      let row = List.take n lst in
      let rest = List.drop n lst in
      row :: splitlist rest n
  in
  {
    entries = splitlist entries c;
    rows = r;
    cols = c;
  }

(*
used a lot of these for the list library 
  https://ocaml.org/manual/5.2/api/List.html
  https://stackoverflow.com/questions/5516815/ocaml-using-list-length
  https://batsov.com/articles/2024/02/23/ocaml-adds-list-take-and-list-drop/
  https://cs3110.github.io/textbook/chapters/data/lists.html
  https://ocaml.org/manual/5.2/api/Stdlib.List.html
*)