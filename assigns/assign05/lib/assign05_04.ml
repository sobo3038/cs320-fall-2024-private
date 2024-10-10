type set_info = {
  ind : int -> bool;
  mn : int;
  mx : int;
}

module ListSet = struct
  type t = int list

  let mem x s = List.mem x s

  let empty = []

  let singleton x = [x]

  let rec card = function
    | [] -> 0
    | _::xs -> 1 + card xs

  let rec union s1 s2 =
    match s1, s2 with
    | [], s | s, [] -> s
    | x::xs, y::ys ->
        if x < y then x :: union xs s2
        else if x > y then y :: union s1 ys
        else x :: union xs ys
end

module FuncSet = struct
  type t = set_info

  let mem x s = s.ind x

  let empty = { ind = (fun _ -> false); mn = max_int; mx = min_int }

  let singleton x = { ind = (fun y -> y = x); mn = x; mx = x }

  let card s =
    let rec count n x =
      if x > s.mx then n
      else if s.ind x then count (n+1) (x+1)
      else count n (x+1)
    in
    count 0 s.mn

  let union s1 s2 =
    let new_mn = min s1.mn s2.mn in
    let new_mx = max s1.mx s2.mx in
    {
      ind = (fun x -> s1.ind x || s2.ind x);
      mn = new_mn;
      mx = new_mx
    }
end