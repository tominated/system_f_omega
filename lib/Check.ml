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
    include Comparator.Make(T)
  end

  (** Represents a term variable with comparitor for use in a map *)
  module TermVar = struct
    module T = struct
      type t = Term.t Bindlib.var
      let compare = Bindlib.compare_vars
      let sexp_of_t x = Sexp.Atom (Bindlib.name_of x)
    end

    include T
    include Comparator.Make(T)
  end

  module TypeVarMap = Map.M(TypeVar)
  module TermVarMap = Map.M(TermVar)

  type t = {
    vars: Type.t TermVarMap.t;
    types: Kind.t TypeVarMap.t;
  }

  let empty: t = {
    vars = Map.empty (module TermVar);
    types = Map.empty (module TypeVar);
  }

  (** Find the type of a term variable in the environment *)
  let find_var (env: t) = Map.find env.vars

  (** Find the kind of a type variable in the environment *)
  let find_ty (env: t) = Map.find env.types

  (** Set the type of a term variable in the environment *)
  let set_var (env: t) key data = { env with vars = Map.set env.vars ~key ~data }
  
  (** Set the kind of a type variable in the environment *)
  let set_ty (env: t) key data = { env with types = Map.set env.types ~key ~data }
end

(** Find the kind of a type. Throws an exception on failure *)
let rec kind_of env : Type.t -> Kind.t = function
  (* Check the type variable kind in the environment *)
  | Var v -> begin
      match Env.find_ty env v with
      | Some k -> k
      | _ -> failwith "[kind_of] type var not found"
    end

  (* Check that both arguments to Arrow are of kind Star
     TODO: Make this a regular type abstraction in the default env *)
  | Arrow (a, b) -> begin
      let a_k = kind_of env a in
      let b_k = kind_of env b in
      match (a_k, b_k) with
      | Star, Star -> Star
      | _ -> failwith "[kind_of] arrow must be * -> *"
    end

  (* Check the kind of the body, with the newly bound type variable in the
     environment *)
  | Forall (k, binder) ->
      let (var, body) = Bindlib.unbind binder in
      let env' = Env.set_ty env var k in
      kind_of env' body

  (* Check the kind of the body, with the newly bound type variable in the
     environment, and return an Arrow kind as a type abstraction *)
  | Abstract (k, binder) ->
      let (var, body) = Bindlib.unbind binder in
      let env' = Env.set_ty env var k in
      Arrow (k, kind_of env' body)

  (* Check that the left value is of kind Arrow, and that the argument is the
     correct kind for the type abstraction argument *)
  | Apply (tyabs, arg) -> begin
      let arg_k' = kind_of env arg in
      match kind_of env tyabs with
      | Arrow (arg_k, rt_k) when Kind.equal arg_k arg_k' -> rt_k
      | Arrow _ -> failwith "[kind_of] applied incorrect kind to type abstraction"
      | _ -> failwith "[kind_of] expected a type abstraction"
    end

  (* Just check the kind of the type embedded *)
  | Group t -> kind_of env t

  (* The recursion base-case for RowExtend. Will always be of kind Row *)
  | RowEmpty -> Row

  (* Ensure each field in the record is of kind Star. Expects the leaf node to be RowEmpty *)
  | RowExtend ((_, field_ty), rest) -> begin
      match kind_of env field_ty with
      | Star -> kind_of env rest
      | _ -> failwith "[kind_of] all fields in a row must be of kind star"
    end

  (* Ensure the parameter to a record is of kind Row.
     TODO: Make this a regular type abstraction in the default env *)
  | Record row -> begin
      match kind_of env row with
      | Row -> Row
      | _ -> failwith "[kind_of] record type must contain a row"
    end
  
  | Fix t -> begin
      match kind_of env t with
      | Arrow (k, k') when Kind.equal k k' -> k'
      | _ -> failwith "[kind_of] cannot fix a type that is not of kind K -> K"
    end

let rec type_of env : Term.t -> Type.t = function
  | Var v -> begin
      match Env.find_var env v with
      | Some ty -> ty
      | _ -> failwith "[type_of] term var not found"
    end
  
  | Abstract (ty, binder) ->
      let (var, body) = Bindlib.unbind binder in
      let env' = Env.set_var env var ty in
      Arrow (ty, type_of env' body)
  
  | Apply (fn, arg) -> begin
      let arg_ty' = type_of env arg in
      match Type.ungroup (type_of env fn) with
      | Arrow (arg_ty, rt_ty) when Type.alpha_equiv arg_ty arg_ty' -> rt_ty
      | Arrow _ -> failwith "[type_of] applied incorrect type to arrow"
      | _ -> failwith "[type_of] expected an arrow"
    end
  
  | TypeAbstract (k, binder) ->
      let (var, body) = Bindlib.unbind binder in
      let env' = Env.set_ty env var k in
      let rt_ty = type_of env' body in
      let ty_binder = Bindlib.bind_var var (Type.lift rt_ty) in
      Forall (k, Bindlib.unbox ty_binder)
  
  | TypeApply (ty_abs, ty_arg) -> begin
      let ty_arg_k' = kind_of env ty_arg in
      match type_of env ty_abs with
      | Forall (ty_arg_k, binder) when Kind.equal ty_arg_k ty_arg_k' -> Bindlib.subst binder ty_arg
      | Forall _ -> failwith "[type_of] applied incorrect kind to type abstraction"
      | _ -> failwith "[type_of] expected a type abstraction"
    end
  
  | RowEmpty -> RowEmpty

  | RowExtend ((label, field), rest) -> begin
      let field_ty = type_of env field in
      match type_of env rest with
      | RowEmpty -> RowExtend ((label, field_ty), RowEmpty)
      | _ -> failwith "[type_of] cannot extend row with non-row"
    end
  
  | Record (te) -> begin
      match type_of env te with
      | RowExtend _ | RowEmpty as row -> Record row
      | _ -> failwith "[type_of] expected a row"
    end
  
  | RecordProject (record, label) -> begin
      let rec find_in_row label : Type.t -> Type.t = function
      | RowExtend ((l, ty), _) when String.equal label l -> ty
      | RowExtend (_, rest) -> find_in_row label rest
      | _ -> failwith "[type_of] label not found in record"
      in
      match type_of env record with
      | Record row -> find_in_row label row
      | _ -> failwith "[type_of] expected a record"
    end
  
  | Fix te -> begin
      match type_of env te with
      | Arrow (ty, ty') when Type.alpha_equiv ty ty' -> ty'
      | _ -> failwith "[type_of] cannot fix a term that is not of type T -> T"
    end
