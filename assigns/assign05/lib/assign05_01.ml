type 'a test = 
  | TestCase of 'a
  | TestList of 'a test list

let rec fold_left op acc = function
  | TestCase x -> op acc x
  | TestList lst -> List.fold_left (fold_left op) acc lst

