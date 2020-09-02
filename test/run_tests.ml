
let () =
  Alcotest.run "system_f_omega" [
    ("Type", Lib.Type.Test.test_suite);
    ("Check", Lib.Check.Test.test_suite)
  ]
