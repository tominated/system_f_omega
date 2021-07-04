(* let () = print_endline "hello!" *)

open Lib

let example_direct : CEK.Direct.t =
  let open CEK.Direct in
  Plus (Plus (Int 2, Int 2), Let ("x", Int 1, Apply (Var "f", Var "x")))

let example_anf : CEK.ANF.t =
  let open CEK.ANF in
  LetPlus
    ( "plus1"
    , (Int 2, Int 2)
    , LetValue
        ( "x"
        , Int 1
        , LetApply
            ("app2", (Var "f", Var "x"), TailPlus (Var "plus0", Var "app2")) )
    )

let () =
  Stdio.printf "Direct:\n%s\n\n" (CEK.Direct.to_string example_direct) ;
  Stdio.printf "ANF Manual:\n%s\n\n" (CEK.ANF.to_string example_anf) ;
  Stdio.printf "ANF Transform:\n%s\n\n"
    (CEK.ANF.to_string (CEK.direct_to_anf example_direct))
