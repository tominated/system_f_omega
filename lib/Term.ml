open Base

type t =
  | Var of t Bindlib.var
  | Abstract of Type.t * (t, t) Bindlib.binder
  | Apply of t * t
  | TypeAbstract of Kind.t * (Type.t, t) Bindlib.binder
  | TypeApply of t * Type.t
  | RowEmpty
  | RowExtend of (string * t) * t
  | Record of t
  | RecordProject of t * string
  | Let of t * (t, t) Bindlib.binder
  | LetType of Type.t * (Type.t, t) Bindlib.binder
  | Fix of t

let rec to_string = function
  | Var x -> Bindlib.name_of x
  | Abstract (ty, binder) ->
      let (var, body) = Bindlib.unbind binder in
      Printf.sprintf "λ(%s:%s).%s" (Bindlib.name_of var) (Type.to_string ty) (to_string body)
  | Apply (a, b) ->
      Printf.sprintf "%s %s" (to_string a) (to_string b)
  | TypeAbstract (Star, binder) ->
      let (tyvar, body) = Bindlib.unbind binder in
      Printf.sprintf "Λ%s.%s" (Bindlib.name_of tyvar) (to_string body)
  | TypeAbstract (k, binder) ->
      let (tyvar, body) = Bindlib.unbind binder in
      Printf.sprintf "Λ(%s:%s).%s" (Bindlib.name_of tyvar) (Kind.to_string k) (to_string body)
  | TypeApply (term, ty) ->
      Printf.sprintf "[%s %s]" (to_string term) (Type.to_string ty)
  | RowEmpty -> ""
  | RowExtend ((label, term), RowEmpty) ->
      Printf.sprintf "%s: %s" label (to_string term)
  | RowExtend ((label, term), rest) ->
      Printf.sprintf "%s: %s, %s" label (to_string term) (to_string rest)
  | Record RowEmpty -> "{}"
  | Record term ->
      Printf.sprintf "{ %s }" (to_string term)
  | RecordProject (term, label) ->
      Printf.sprintf "%s.%s" (to_string term) label
  | Let (term, binder) ->
      let (var, body) = Bindlib.unbind binder in
      Printf.sprintf "let %s = %s in\n%s" (Bindlib.name_of var) (to_string term) (to_string body)
  | LetType (ty, binder) ->
      let (var, body) = Bindlib.unbind binder in
      Printf.sprintf "type %s = %s in\n%s" (Bindlib.name_of var) (Type.to_string ty) (to_string body)
  | Fix term ->
      Printf.sprintf "fix (%s)" (to_string term)

let mkfree x = Var x

let var : t Bindlib.var -> t Bindlib.box = Bindlib.box_var
let abstract = Bindlib.box_apply2 (fun t b -> Abstract (t, b))
let apply = Bindlib.box_apply2 (fun a b -> Apply (a, b))
let ty_abstract = Bindlib.box_apply2 (fun k b -> TypeAbstract (k, b))
let ty_apply = Bindlib.box_apply2 (fun te ty -> TypeApply (te, ty))
let row_empty = Bindlib.box RowEmpty
let row_extend = Bindlib.box_apply3 (fun label te rest -> RowExtend ((label, te), rest))
let record = Bindlib.box_apply (fun t -> Record t)
let record_project = Bindlib.box_apply2(fun ty label -> RecordProject (ty, label))
let let_term = Bindlib.box_apply2 (fun te b -> Let (te, b))
let let_type = Bindlib.box_apply2 (fun ty b -> LetType (ty, b))
let fix = Bindlib.box_apply (fun t -> Fix t)

let rec lift = function
  | Var x -> var x
  | Abstract (ty, binder) -> abstract (Type.lift ty) (Bindlib.box_binder lift binder)
  | Apply (a, b) -> apply (lift a) (lift b)
  | TypeAbstract (k, binder) -> ty_abstract (Kind.lift k) (Bindlib.box_binder lift binder)
  | TypeApply (term, ty) -> ty_apply (lift term) (Type.lift ty)
  | RowEmpty -> row_empty
  | RowExtend ((label, term), rest) ->
      row_extend (Bindlib.box label) (lift term) (lift rest)
  | Record term -> record (lift term)
  | RecordProject (term, label) -> record_project (lift term) (Bindlib.box label)
  | Let (term, binder) -> let_term (lift term) (Bindlib.box_binder lift binder)
  | LetType (ty, binder) -> let_type (Type.lift ty) (Bindlib.box_binder lift binder)
  | Fix term -> fix (lift term)
