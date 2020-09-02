open Base

(** The type checking environment manages bound term and type variables *)
module Env = struct
  (** Represents a type variable with comparitor for use in a map *)
  module TypeVar = struct
    module T = struct
      type t = Type.t Bindlib.var

      let compare = Bindlib.compare_vars

      let sexp_of_t x = Sexp.Atom (Bindlib.name_of x)
    end

    include T
    include Comparator.Make (T)
  end

  (** Represents a term variable with comparitor for use in a map *)
  module TermVar = struct
    module T = struct
      type t = Term.t Bindlib.var

      let compare = Bindlib.compare_vars

      let sexp_of_t x = Sexp.Atom (Bindlib.name_of x)
    end

    include T
    include Comparator.Make (T)
  end

  module TypeVarMap = Map.M (TypeVar)
  module TermVarMap = Map.M (TermVar)

  type t = {vars: Type.t TermVarMap.t; types: Kind.t TypeVarMap.t}

  let empty : t =
    {vars= Map.empty (module TermVar); types= Map.empty (module TypeVar)}

  (** Find the type of a term variable in the environment *)
  let find_var (env : t) = Map.find env.vars

  (** Find the kind of a type variable in the environment *)
  let find_ty (env : t) = Map.find env.types

  (** Set the type of a term variable in the environment *)
  let set_var (env : t) key data = {env with vars= Map.set env.vars ~key ~data}

  (** Set the kind of a type variable in the environment *)
  let set_ty (env : t) key data = {env with types= Map.set env.types ~key ~data}
end

(** Find the kind of a type. Throws an exception on failure *)
let rec kind_of env : Type.t -> Kind.t = function
  (* Check the type variable kind in the environment *)
  | Var v -> (
    match Env.find_ty env v with
    | Some k ->
        k
    | _ ->
        failwith "[kind_of] type var not found" )
  (* Check that both arguments to Arrow are of kind Star
     TODO: Make this a regular type abstraction in the default env *)
  | Arrow (a, b) -> (
      let a_k = kind_of env a in
      let b_k = kind_of env b in
      match (a_k, b_k) with
      | Star, Star ->
          Star
      | _ ->
          failwith "[kind_of] arrow must be * -> *" )
  (* Check the kind of the body, with the newly bound type variable in the
     environment *)
  | Forall (k, binder) ->
      let var, body = Bindlib.unbind binder in
      let env' = Env.set_ty env var k in
      kind_of env' body
  (* Check the kind of the body, with the newly bound type variable in the
     environment, and return an Arrow kind as a type abstraction *)
  | Abstract (k, binder) ->
      let var, body = Bindlib.unbind binder in
      let env' = Env.set_ty env var k in
      Arrow (k, kind_of env' body)
  (* Check that the left value is of kind Arrow, and that the argument is the
     correct kind for the type abstraction argument *)
  | Apply (tyabs, arg) -> (
      let arg_k' = kind_of env arg in
      match kind_of env tyabs with
      | Arrow (arg_k, rt_k) when Kind.equal arg_k arg_k' ->
          rt_k
      | Arrow _ ->
          failwith "[kind_of] applied incorrect kind to type abstraction"
      | _ ->
          failwith "[kind_of] expected a type abstraction" )
  (* Just check the kind of the type embedded *)
  | Group t ->
      kind_of env t
  (* The recursion base-case for RowExtend. Will always be of kind Row *)
  | RowEmpty ->
      Row
  (* Ensure each field in the record is of kind Star. Expects the leaf node to be RowEmpty *)
  | RowExtend ((_, field_ty), rest) -> (
    match kind_of env field_ty with
    | Star ->
        kind_of env rest
    | _ ->
        failwith "[kind_of] all fields in a row must be of kind star" )
  (* Ensure the parameter to a record is of kind Row.
     TODO: Make this a regular type abstraction in the default env *)
  | Record row -> (
    match kind_of env row with
    | Row ->
        Star
    | _ ->
        failwith "[kind_of] record type must contain a row" )
  | Fix t -> (
    match kind_of env t with
    | Arrow (k, k') when Kind.equal k k' ->
        k'
    | _ ->
        failwith "[kind_of] cannot fix a type that is not of kind K -> K" )

let rec type_of env : Term.t -> Type.t = function
  | Var v -> (
    match Env.find_var env v with
    | Some ty ->
        ty
    | _ ->
        failwith "[type_of] term var not found" )
  | Abstract (ty, binder) ->
      let var, body = Bindlib.unbind binder in
      let env' = Env.set_var env var ty in
      Arrow (ty, type_of env' body)
  | Apply (fn, arg) -> (
      let arg_ty' = type_of env arg in
      match Type.ungroup (type_of env fn) with
      | Arrow (arg_ty, rt_ty) when Type.alpha_equiv arg_ty arg_ty' ->
          rt_ty
      | Arrow _ ->
          failwith "[type_of] applied incorrect type to arrow"
      | _ ->
          failwith "[type_of] expected an arrow" )
  | TypeAbstract (k, binder) ->
      let var, body = Bindlib.unbind binder in
      let env' = Env.set_ty env var k in
      let rt_ty = type_of env' body in
      let ty_binder = Bindlib.bind_var var (Type.lift rt_ty) in
      Forall (k, Bindlib.unbox ty_binder)
  | TypeApply (ty_abs, ty_arg) -> (
      let ty_arg_k' = kind_of env ty_arg in
      match type_of env ty_abs with
      | Forall (ty_arg_k, binder) when Kind.equal ty_arg_k ty_arg_k' ->
          Bindlib.subst binder ty_arg
      | Forall _ ->
          failwith "[type_of] applied incorrect kind to type abstraction"
      | _ ->
          failwith "[type_of] expected a type abstraction" )
  | RowEmpty ->
      RowEmpty
  | RowExtend ((label, field), rest) -> (
      let field_ty = type_of env field in
      match type_of env rest with
      | (RowExtend _ | RowEmpty) as rest' ->
          RowExtend ((label, field_ty), rest')
      | _ ->
          failwith "[type_of] cannot extend row with non-row" )
  | Record te -> (
    match type_of env te with
    | (RowExtend _ | RowEmpty) as row ->
        Record row
    | _ ->
        failwith "[type_of] expected a row" )
  | RecordProject (record, label) -> (
      let rec find_in_row label : Type.t -> Type.t = function
        | RowExtend ((l, ty), _) when String.equal label l ->
            ty
        | RowExtend (_, rest) ->
            find_in_row label rest
        | _ ->
            failwith "[type_of] label not found in record"
      in
      match type_of env record with
      | Record row ->
          find_in_row label row
      | _ ->
          failwith "[type_of] expected a record" )
  | Let (term, binder) ->
      let term_ty = type_of env term in
      let var, body = Bindlib.unbind binder in
      let env' = Env.set_var env var term_ty in
      type_of env' body
  | LetType (ty, binder) ->
      let ty_k = kind_of env ty in
      let tyvar, body = Bindlib.unbind binder in
      let env' = Env.set_ty env tyvar ty_k in
      type_of env' body
  | Fix te -> (
    match type_of env te with
    | Arrow (ty, ty') when Type.alpha_equiv ty ty' ->
        ty'
    | _ ->
        failwith "[type_of] cannot fix a term that is not of type T -> T" )

module Test = struct
  let kind = Alcotest.testable (Fmt.of_to_string Kind.to_string) Kind.equal

  let ty = Alcotest.testable (Fmt.of_to_string Type.to_string) Type.alpha_equiv

  let unit_ty : Type.t = Bindlib.unbox (Type.record Type.row_empty)

  let unit_term : Term.t = Bindlib.unbox (Term.record Term.row_empty)

  let id_term : Term.t =
    let open Term in
    let tyvar = Bindlib.new_var Type.mkfree "x" in
    let termvar = Bindlib.new_var mkfree "x" in
    let fn =
      abstract (Type.var tyvar) (Bindlib.bind_var termvar (var termvar))
    in
    Bindlib.unbox (ty_abstract Kind.star (Bindlib.bind_var tyvar fn))

  let id_ty : Type.t =
    let open Type in
    let tyvar = Bindlib.new_var mkfree "x" in
    let arrow_ty = arrow (var tyvar) (var tyvar) in
    forall Kind.star (Bindlib.bind_var tyvar arrow_ty) |> Bindlib.unbox

  let nat_ty : Type.t =
    let open Type in
    let tvar = Bindlib.new_var mkfree "t" in
    forall Kind.star
      (Bindlib.bind_var tvar
         (arrow (var tvar)
            (arrow (group (arrow (var tvar) (var tvar))) (var tvar))))
    |> Bindlib.unbox

  let z_term : Term.t =
    let open Term in
    let tvar = Bindlib.new_var Type.mkfree "t" in
    let bvar = Bindlib.new_var mkfree "b" in
    let svar = Bindlib.new_var mkfree "s" in
    let t = Type.var tvar in
    let b = var bvar in
    ty_abstract Kind.star
      (Bindlib.bind_var tvar
         (abstract t
            (Bindlib.bind_var bvar
               (abstract (Type.arrow t t) (Bindlib.bind_var svar b)))))
    |> Bindlib.unbox

  let succ_term =
    let open Term in
    let tvar = Bindlib.new_var Type.mkfree "t" in
    let xvar = Bindlib.new_var mkfree "x" in
    let bvar = Bindlib.new_var mkfree "b" in
    let svar = Bindlib.new_var mkfree "s" in
    let t = Type.var tvar in
    let x = var xvar in
    let b = var bvar in
    let s = var svar in
    abstract (Type.lift nat_ty)
      (Bindlib.bind_var xvar
         (ty_abstract Kind.star
            (Bindlib.bind_var tvar
               (abstract t
                  (Bindlib.bind_var bvar
                     (abstract (Type.arrow t t)
                        (Bindlib.bind_var svar
                           (apply s (apply (apply (ty_apply x t) b) s)))))))))
    |> Bindlib.unbox

  let one_term = Term.apply (Term.lift succ_term) (Term.lift z_term)

  let two_term = Term.apply (Term.lift succ_term) one_term

  let basic_module_usage : Term.t =
    let open Term in
    let basic_module =
      row_empty
      |> row_extend (Bindlib.box "z") (Term.lift z_term)
      |> row_extend (Bindlib.box "id") (Term.lift id_term)
      |> record
    in
    let projected_id = record_project basic_module (Bindlib.box "id") in
    let nat_id = ty_apply projected_id (Type.lift nat_ty) in
    Bindlib.unbox @@ apply nat_id two_term

  let kind_of_test () =
    Alcotest.check kind "unit type has kind star" Kind.Star
      (kind_of Env.empty unit_ty) ;
    Alcotest.check kind "nat type has kind star" Kind.Star
      (kind_of Env.empty nat_ty)

  let type_of_test () =
    Alcotest.check ty "id fn has correct type" id_ty (type_of Env.empty id_term) ;
    Alcotest.check ty "z has type of nat" nat_ty (type_of Env.empty z_term) ;
    Alcotest.check ty "two has type of nat" nat_ty
      (type_of Env.empty (Bindlib.unbox two_term)) ;
    Alcotest.check ty
      "record projection of polymorphic id function, applied to two" nat_ty
      (type_of Env.empty basic_module_usage)

  let test_suite =
    [("kind_of", `Quick, kind_of_test); ("type_of", `Quick, type_of_test)]
end
