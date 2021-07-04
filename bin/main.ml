(* let () = print_endline "hello!" *)

open Lib

let example_direct : CEK.Direct.t =
  let open CEK.Direct in
  Let
    ( "add2"
    , Lambda ("x", Plus (Var "x", Int 2))
    , Plus (Int 5, Apply (Var "add2", Int 3)) )

let () =
  Stdio.printf "Direct:\n%s\n\n" (CEK.Direct.to_string example_direct) ;
  let anf = CEK.direct_to_anf example_direct in
  Stdio.printf "ANF Transform:\n%s\n\n" (CEK.ANF.to_string anf) ;
  Stdio.print_endline "evaluating..." ;
  let result = CEK.CEK.evaluate anf in
  Stdio.printf "Result: %s\n" (CEK.CEK.value_to_string result)
