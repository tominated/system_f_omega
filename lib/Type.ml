open Base

type t =
  | Var of t Bindlib.var
  | Arrow of t * t
  | Forall of Kind.t * (t, t) Bindlib.binder
  | Abstract of Kind.t * (t, t) Bindlib.binder
  | Apply of t * t
  | Group of t
  | RowEmpty
  | RowExtend of (string * t) * t
  | Record of t

let rec to_string = function
  | Var x -> Bindlib.name_of x
  | Arrow (a, b) ->
      Printf.sprintf "%s -> %s" (to_string a) (to_string b)
  | Forall (Star, binder) ->
      let (x, a) = Bindlib.unbind binder in
      Printf.sprintf "∀%s.%s" (Bindlib.name_of x) (to_string a)
  | Forall (k, binder) ->
      let (x, a) = Bindlib.unbind binder in
      Printf.sprintf "∀(%s:%s).%s" (Bindlib.name_of x) (Kind.to_string k) (to_string a)
  | Abstract (Star, binder) ->
      let (x, a) = Bindlib.unbind binder in
      Printf.sprintf "λ%s.%s" (Bindlib.name_of x) (to_string a)
  | Abstract (k, binder) ->
      let (x, a) = Bindlib.unbind binder in
      Printf.sprintf "λ(%s:%s).%s" (Bindlib.name_of x) (Kind.to_string k) (to_string a)
  | Apply (a, b) ->
      Printf.sprintf "%s %s" (to_string a) (to_string b)
  | Group t ->
      Printf.sprintf "(%s)" (to_string t)
  | RowEmpty -> ""
  | RowExtend ((label, t), RowEmpty) ->
      Printf.sprintf "%s: %s" label (to_string t)
  | RowExtend ((label, t), rest) ->
      Printf.sprintf "%s: %s, %s" label (to_string t) (to_string rest)
  | Record RowEmpty -> "{}"
  | Record t ->
      Printf.sprintf "{ %s }" (to_string t)

let mkfree x = Var x

let var : t Bindlib.var -> t Bindlib.box = Bindlib.box_var
let arrow = Bindlib.box_apply2 (fun a b -> Arrow (a, b))
let forall = Bindlib.box_apply2 (fun k f -> Forall (k, f))
let abstract = Bindlib.box_apply2 (fun k f -> Abstract (k, f))
let apply = Bindlib.box_apply2 (fun a b -> Apply (a, b))
let group = Bindlib.box_apply (fun t -> Group t)
let row_empty = Bindlib.box RowEmpty
let row_extend = Bindlib.box_apply3 (fun label t rest -> RowExtend ((label, t), rest))
let record = Bindlib.box_apply (fun t -> Record t)

let rec lift = function
  | Var x -> var x
  | Arrow (a, b) -> arrow (lift a) (lift b)
  | Forall (k, b) -> forall (Kind.lift k) (Bindlib.box_binder lift b)
  | Abstract (k, b) -> abstract (Kind.lift k) (Bindlib.box_binder lift b)
  | Apply (a, b) -> apply (lift a) (lift b)
  | Group t -> group (lift t)
  | RowEmpty -> row_empty
  | RowExtend ((label, t), rest) ->
      row_extend (Bindlib.box label) (lift t) (lift rest)
  | Record t -> record (lift t)

let rec alpha_equiv a b =
  match (a, b) with
  | Var x, Var y -> Bindlib.eq_vars x y
  | Arrow (a1, b1), Arrow (a2, b2) -> alpha_equiv a1 a2  && alpha_equiv b1 b2
  | Forall (k1, b1), Forall (k2, b2) -> Kind.equal k1 k2 && Bindlib.eq_binder alpha_equiv b1 b2
  | Abstract (k1, b1), Abstract (k2, b2) -> Kind.equal k1 k2 && Bindlib.eq_binder alpha_equiv b1 b2
  | Apply (a1, b1), Apply (a2, b2) -> alpha_equiv a1 a2 && alpha_equiv b1 b2
  | RowEmpty, RowEmpty -> true
  
  (* Row head equivalency *)
  | RowExtend ((l, t), r), RowExtend ((l', t'), s)
    when String.equal l l' ->
      alpha_equiv t t' && alpha_equiv r s

  (* Row swap equivalency *)
  | RowExtend ((l, t), RowExtend ((l', t'), rest)), b
    when not (String.equal l l') ->
      let swapped = RowExtend ((l', t'), RowExtend ((l, t), rest)) in
      alpha_equiv swapped b

  | Group a, Group b | Group a, b | a, Group b | Record a, Record b -> alpha_equiv a b
  | _ -> false

module Test = struct
  let fmt = Fmt.of_to_string to_string
  let ty = Alcotest.testable fmt alpha_equiv

  let x_var = Bindlib.new_var mkfree "x"
  let y_var = Bindlib.new_var mkfree "y"

  let id_term = Arrow ((Var x_var), (Var x_var))

  let unit_ty = Record RowEmpty
  let row_basic = RowExtend (("x", unit_ty), RowExtend (("y", unit_ty), RowEmpty))
  let row_basic2 = RowExtend (("y", unit_ty), RowExtend (("x", unit_ty), RowEmpty))
  let row_basic3 = RowExtend (("y", unit_ty), RowExtend (("z", unit_ty), RowEmpty))

  let alpha_equiv_test () =
    Alcotest.check ty
        "id fn is equiv to itself"
        (id_term) id_term;

    Alcotest.check ty
        "var x and x are equiv"
        (Var x_var) (Var x_var);

    Alcotest.check ty
        "row [x: unit, y: unit] and [y: unit, x: unit] are equiv"
        row_basic row_basic2;

    Alcotest.(check @@ neg ty)
        "row [x: unit, y: unit] and [y: unit, z: unit] are not equiv"
        row_basic2 row_basic3

  let test_suite = [("alpha_equiv", `Quick, alpha_equiv_test)]
end
