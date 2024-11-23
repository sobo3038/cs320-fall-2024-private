open Lib
open Utils

(* String representation of values *)
let string_of_value = function
  | VUnit -> "unit"
  | VBool b -> if b then "true" else "false"
  | VNum n -> string_of_int n
  | VClos _ -> "<closure>"

(* String representation of errors *)
let string_of_error = function
  | ParseErr -> "ParseErr"
  | UnknownVar v -> "UnknownVar: " ^ v
  | IfTyErr (t1, t2) -> "IfTyErr(" ^ string_of_ty t1 ^ ", " ^ string_of_ty t2 ^ ")"
  | IfCondTyErr t -> "IfCondTyErr(" ^ string_of_ty t ^ ")"
  | OpTyErrL (op, expected, actual) ->
      "OpTyErrL(" ^ string_of_bop op ^ ", " ^ string_of_ty expected ^ ", " ^ string_of_ty actual ^ ")"
  | OpTyErrR (op, expected, actual) ->
      "OpTyErrR(" ^ string_of_bop op ^ ", " ^ string_of_ty expected ^ ", " ^ string_of_ty actual ^ ")"
  | FunArgTyErr (expected, actual) ->
      "FunArgTyErr(" ^ string_of_ty expected ^ ", " ^ string_of_ty actual ^ ")"
  | FunAppTyErr t -> "FunAppTyErr(" ^ string_of_ty t ^ ")"
  | LetTyErr (expected, actual) ->
      "LetTyErr(" ^ string_of_ty expected ^ ", " ^ string_of_ty actual ^ ")"
  | AssertTyErr t -> "AssertTyErr(" ^ string_of_ty t ^ ")"

(* Run a single test case *)
let run_test input expected =
  match interp input with
  | Ok value ->
      let result = string_of_value value in
      if result = expected then
        Printf.printf "Test Passed: Input: %s -> Result: %s\n" input result
      else
        Printf.printf "Test Failed: Input: %s -> Expected: %s, but got: %s\n" input expected result
  | Error err ->
      let error_msg = string_of_error err in
      Printf.printf "Test Failed: Input: %s -> Error: %s\n" input error_msg




      
(* Test cases *)
let () =
  let test_cases = [
    (* Parsing and evaluation tests *)
    ("let x : int = 5 in x + 1", "6");
    ("let rec fact (n : int) : int = if n = 0 then 1 else n * fact (n - 1) in fact 5", "120");
    ("if true then 1 else 0", "1");
    ("if false then 1 else 0", "0");
    ("let _ : unit = assert (1 + 1 = 2)", "unit");

    (* Edge cases *)
    ("let x : int = 0 in x / 0", ""); (* Division by zero *)
    ("let rec loop (x : int) : int = loop (x + 1) in loop 0", ""); (* Infinite recursion *)
  ] in

  (* Run all test cases *)
  List.iter (fun (input, expected) -> run_test input expected) test_cases
