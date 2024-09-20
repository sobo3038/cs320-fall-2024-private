(*problem 1: tic tac toe*)

(*this was all given*)
type piece = 
| X
| O

type pos = 
| Piece of piece
| Blank

type board = (pos * pos * pos) * (pos * pos * pos) * (pos * pos * pos)

type row_index = 
| Top
| Middle
| Bottom

type col_index = 
| Left
| Middle
| Right

type pos_index = row_index * col_index

let get_row (board: board) (row: row_index) : pos * pos * pos =
  match board, row with
  | (r, _, _), Top -> r
  | (_, r, _), Middle -> r
  | (_, _, r), Bottom -> r

let get_pos_from_row ((p1, p2, p3): pos * pos * pos) (col: col_index) : pos =
  match col with
  | Left -> p1
  | Middle -> p2
  | Right -> p3

let get_pos (board: board) ((row, col): pos_index) : pos =
  get_pos_from_row (get_row board row) col

let all_same = function
  | (Piece x, Piece y, Piece z) when x = y && y = z -> true
  | _ -> false

let get_column (board: board) (col: col_index) : pos * pos * pos =
  let (r1, r2, r3) = board in
  match col with
  | Left -> let (p1, _, _) = r1 in
            let (p2, _, _) = r2 in
            let (p3, _, _) = r3 in (p1, p2, p3)
  | Middle -> let (_, p1, _) = r1 in
              let (_, p2, _) = r2 in
              let (_, p3, _) = r3 in (p1, p2, p3)
  | Right -> let (_, _, p1) = r1 in
             let (_, _, p2) = r2 in
             let (_, _, p3) = r3 in (p1, p2, p3)

let get_diagonals (board: board) : (pos * pos * pos) * (pos * pos * pos) =
  let (r1, r2, r3) = board in
  let (r1l, _, r1r) = r1 in
  let (_, r2m, _) = r2 in
  let (r3l, _, r3r) = r3 in
  ((r1l, r2m, r3r), (r1r, r2m, r3l))


let winner (board: board) : bool =
  let (r1, r2, r3) = board in
  let (d1, d2) = get_diagonals board in
  
  all_same r1 ||  
  all_same r2 ||  
  all_same r3 ||  
  
  all_same (get_column board Left) ||   
  all_same (get_column board Middle) || 
  all_same (get_column board Right) ||  
  
  all_same d1 ||  
  all_same d2


  (*
  lots of pattern matching sources here 
  https://caml.inria.fr/pub/docs/oreilly-book/html/book-ora016.html
  https://www2.lib.uchicago.edu/keith/ocaml-class/pattern-matching.html
  https://abitofocaml.weebly.com/12-pattern-matching.html
  https://discuss.ocaml.org/t/conversion-patterns-of-pattern-matching-to-disjoint-patterns/5285/2 helped me with formatting 
  *)