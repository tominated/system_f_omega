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
     environment *)
  | Exists (k, binder) ->
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
  | Pack (witness_ty, term, into_ty) when Kind.is_mono (kind_of env into_ty)
    -> (
      (* Get the kind of the witness type for later *)
      let witness_k = kind_of env witness_ty in
      (* Ensure that we're packing into an existential *)
      match into_ty with
      | Exists (exists_k, binder) when Kind.equal exists_k witness_k ->
          let term_ty = type_of env term in
          let subst_exists_ty = Bindlib.subst binder witness_ty in
          if Type.alpha_equiv term_ty subst_exists_ty then into_ty
          else failwith "[type_of] packing incorrect type into existential"
      | Exists _ ->
          failwith "[type_of] cannot pack witness type in to diff kind"
      | _ ->
          failwith "[type_of] can only pack in to existential type" )
  | Pack _ ->
      failwith "[type_of] can only pack mono-kinded types"
  | Unpack (impl, binder) -> (
    match type_of env impl with
    | Exists (k, exists_binder) ->
        let _, impl_ty = Bindlib.unbind exists_binder in
        let tyvar, body_binder = Bindlib.unbind binder in
        let var, body = Bindlib.unbind body_binder in
        (* add the hidden type and term to the env *)
        let env' = Env.set_var (Env.set_ty env tyvar k) var impl_ty in
        let body_ty = type_of env' body in
        (* check the kind without the hidden type/term in the env *)
        let body_k = kind_of env body_ty in
        if Kind.is_mono body_k then body_ty
        else failwith "[type_of] unpack body is not mono-kind"
    | _ ->
        failwith "[type_of] unpacked non-existential type" )
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

  (** Unit type : {} *)
  let unit_ty : Type.t = Bindlib.unbox (Type.record Type.row_empty)

  (** Unit term = {} *)
  let unit_term : Term.t = Bindlib.unbox (Term.record Term.row_empty)

  (** Identity function term = Λa:*. λx:a. x *)
  let id_term : Term.t =
    let open Term in
    let tyvar = Bindlib.new_var Type.mkfree "x" in
    let termvar = Bindlib.new_var mkfree "x" in
    let fn =
      abstract (Type.var tyvar) @@ Bindlib.bind_var termvar (var termvar)
    in
    Bindlib.unbox @@ ty_abstract Kind.star @@ Bindlib.bind_var tyvar fn

  (** Identity function type : ∀a:*. a -> a *)
  let id_ty : Type.t =
    let open Type in
    let tyvar = Bindlib.new_var mkfree "x" in
    let arrow_ty = arrow (var tyvar) (var tyvar) in
    Bindlib.unbox @@ forall Kind.star @@ Bindlib.bind_var tyvar arrow_ty

  (* boolean type : ∀t:* t -> t -> t *)
  let bool_ty =
    let open Type in
    let tvar = Bindlib.new_var mkfree "t" in
    let t = var tvar in
    forall Kind.star @@ Bindlib.bind_var tvar @@ arrow t (arrow t t)

  (* true term : Λt:* λtrue:t. λfalse:t. true *)
  let true_term =
    let open Term in
    let tvar = Bindlib.new_var Type.mkfree "t" in
    let true_var = Bindlib.new_var mkfree "true" in
    let false_var = Bindlib.new_var mkfree "false" in
    let t, true_val = (Type.var tvar, var true_var) in
    ty_abstract Kind.star @@ Bindlib.bind_var tvar @@ abstract t
    @@ Bindlib.bind_var true_var @@ abstract t @@ Bindlib.bind_var false_var
    @@ true_val

  (* false term : Λt:* λtrue:t. λfalse:t. false *)
  let false_term =
    let open Term in
    let tvar = Bindlib.new_var Type.mkfree "t" in
    let true_var = Bindlib.new_var mkfree "true" in
    let false_var = Bindlib.new_var mkfree "false" in
    let t, false_val = (Type.var tvar, var false_var) in
    ty_abstract Kind.star @@ Bindlib.bind_var tvar @@ abstract t
    @@ Bindlib.bind_var true_var @@ abstract t @@ Bindlib.bind_var false_var
    @@ false_val

  (** Natural number type : ∀t:*. t -> (t -> t) -> t *)
  let nat_ty : Type.t =
    let open Type in
    let tvar = Bindlib.new_var mkfree "t" in
    Bindlib.unbox @@ forall Kind.star @@ Bindlib.bind_var tvar
    @@ arrow (var tvar)
    @@ arrow (group (arrow (var tvar) (var tvar))) (var tvar)

  (** Zero term = Λt:*. λz:t. λs:(t -> t). z *)
  let z_term : Term.t =
    let open Term in
    let tvar = Bindlib.new_var Type.mkfree "t" in
    let bvar = Bindlib.new_var mkfree "b" in
    let svar = Bindlib.new_var mkfree "s" in
    let t = Type.var tvar in
    let b = var bvar in
    Bindlib.unbox @@ ty_abstract Kind.star @@ Bindlib.bind_var tvar
    @@ abstract t @@ Bindlib.bind_var bvar
    @@ abstract (Type.arrow t t)
    @@ Bindlib.bind_var svar b

  (** Succ term =
    λx:nat. Λt:*. λz:t. λs:(t -> t). s (x [t] z) s
    *)
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
    Bindlib.unbox
    @@ abstract (Type.lift nat_ty)
    @@ Bindlib.bind_var xvar @@ ty_abstract Kind.star @@ Bindlib.bind_var tvar
    @@ abstract t @@ Bindlib.bind_var bvar
    @@ abstract (Type.arrow t t)
    @@ Bindlib.bind_var svar
    @@ apply s (apply (apply (ty_apply x t) b) s)

  let add_ty =
    let open Type in
    let nat = lift nat_ty in
    arrow nat (arrow nat nat)

  (** Nat add term = λa:nat. λb:nat. Λt:*. λz:t. λs:(t -> t). b [t] (a [x] s z) s *)
  let add_term =
    let open Term in
    let avar = Bindlib.new_var mkfree "a" in
    let bvar = Bindlib.new_var mkfree "b" in
    let svar = Bindlib.new_var mkfree "s" in
    let zvar = Bindlib.new_var mkfree "z" in
    let tvar = Bindlib.new_var Type.mkfree "t" in
    let a, b, s, z, t =
      (var avar, var bvar, var svar, var zvar, Type.var tvar)
    in
    abstract (Type.lift nat_ty)
    @@ Bindlib.bind_var avar
    @@ abstract (Type.lift nat_ty)
    @@ Bindlib.bind_var bvar @@ ty_abstract Kind.star @@ Bindlib.bind_var tvar
    @@ abstract t @@ Bindlib.bind_var zvar
    @@ abstract (Type.arrow t t)
    @@ Bindlib.bind_var svar
    @@ apply (apply (ty_apply b t) (apply (apply (ty_apply a t) z) s)) s

  (* is_zero type : nat -> bool *)
  let is_zero_ty =
    let open Type in
    arrow (lift nat_ty) bool_ty

  (* is_zero term = λn:nat. n [bool] true (λ_:bool. false) *)
  let is_zero_term =
    let open Term in
    let nvar = Bindlib.new_var mkfree "n" in
    let ignored_var = Bindlib.new_var mkfree "_" in
    let n = var nvar in
    abstract (Type.lift nat_ty)
    @@ Bindlib.bind_var nvar
    @@ apply (apply (ty_apply n bool_ty) true_term)
    @@ abstract bool_ty
    @@ Bindlib.bind_var ignored_var
    @@ false_term

  (** One nat number = succ (succ zero) *)
  let one_term = Term.apply (Term.lift succ_term) (Term.lift z_term)

  (** Two nat number = succ one *)
  let two_term = Term.apply (Term.lift succ_term) one_term

  (** Basic module use =
    { id: id, z: zero }.id [nat] two
    *)
  let basic_module_usage : Term.t =
    let open Term in
    let basic_module =
      record
      @@ row_extend (Bindlib.box "id") (Term.lift id_term)
      @@ row_extend (Bindlib.box "z") (Term.lift z_term) row_empty
    in
    let projected_id = record_project basic_module (Bindlib.box "id") in
    let nat_id = ty_apply projected_id (Type.lift nat_ty) in
    Bindlib.unbox @@ apply nat_id two_term

  (** Row polymorphic function term =
    (Λr:Row. λx:{b: nat, ...r}. x.b) [{ a: nat }] {a: one, b: two} 
    *)
  let row_polymorphism_usage =
    let open Term in
    let rvar = Bindlib.new_var Type.mkfree "r" in
    let xvar = Bindlib.new_var mkfree "x" in
    let get_b =
      ty_abstract Kind.row @@ Bindlib.bind_var rvar
      @@ abstract
           ( Type.record
           @@ Type.row_extend (Bindlib.box "b") (Type.lift nat_ty)
                (Type.var rvar) )
      @@ Bindlib.bind_var xvar
      @@ record_project (var xvar) (Bindlib.box "b")
    in
    let my_record =
      record
      @@ row_extend (Bindlib.box "a") one_term
      @@ row_extend (Bindlib.box "b") two_term row_empty
    in
    let my_record_ty =
      Type.row_extend (Bindlib.box "a") (Type.lift nat_ty) Type.row_empty
    in
    Bindlib.unbox @@ apply (ty_apply get_b my_record_ty) my_record

  (** module type : ∃t:*. { zero: t, one: t, combine: t -> t -> t, is_zero: t -> bool } *)
  let existential_module_ty =
    let open Type in
    let tvar = Bindlib.new_var Type.mkfree "t" in
    let t = var tvar in
    exists Kind.star @@ Bindlib.bind_var tvar @@ record
    @@ row_extend (Bindlib.box "zero") t
    @@ row_extend (Bindlib.box "one") t
    @@ row_extend (Bindlib.box "combine") (arrow t (arrow t t))
    @@ row_extend (Bindlib.box "is_zero") (arrow t bool_ty) row_empty

  (** Natural number module term =
    pack {nat, { zero: zero, one: one, combine: add, isEmpty:  }} as monoid
    *)
  let nat_module_term =
    let open Term in
    let impl =
      record
      @@ row_extend (Bindlib.box "zero") (lift z_term)
      @@ row_extend (Bindlib.box "one") one_term
      @@ row_extend (Bindlib.box "combine") add_term
      @@ row_extend (Bindlib.box "is_zero") is_zero_term row_empty
    in
    pack (Type.lift nat_ty) impl existential_module_ty

  (* Nat monoid usage = unpack {T, m} = nat_monoid in m.combine m.empty m.empty *)
  let nat_module_usage =
    let open Term in
    let tvar = Bindlib.new_var Type.mkfree "t" in
    let mvar = Bindlib.new_var mkfree "m" in
    let m = var mvar in
    let m_is_zero = record_project m (Bindlib.box "is_zero") in
    let m_zero = record_project m (Bindlib.box "zero") in
    unpack nat_module_term @@ Bindlib.bind_var tvar @@ Bindlib.bind_var mvar
    @@ apply m_is_zero m_zero

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
    Alcotest.check ty "add has correct type" (Bindlib.unbox add_ty)
      (type_of Env.empty (Bindlib.unbox add_term)) ;
    Alcotest.check ty
      "record projection of polymorphic id function, applied to two" nat_ty
      (type_of Env.empty basic_module_usage) ;
    Alcotest.check ty "calling a row polymorphic function with a record" nat_ty
      (type_of Env.empty row_polymorphism_usage) ;
    Alcotest.check ty "is_zero returns bool" (Bindlib.unbox bool_ty)
      (type_of Env.empty (Bindlib.unbox @@ Term.apply is_zero_term one_term)) ;
    Alcotest.check ty "pack"
      (Bindlib.unbox existential_module_ty)
      (type_of Env.empty @@ Bindlib.unbox nat_module_term) ;
    Stdio.printf "uhhh monoid usage?: \n%s\n"
      (Term.to_string @@ Bindlib.unbox nat_module_usage)

  let test_suite =
    [("kind_of", `Quick, kind_of_test); ("type_of", `Quick, type_of_test)]
end
