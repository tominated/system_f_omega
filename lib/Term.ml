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
  | Fix of t

let rec to_string = function
  | Var x -> Bindlib.name_of x
  | Abstract (t, binder) ->
      let (x, body) = Bindlib.unbind binder in
      Printf.sprintf "λ(%s:%s).%s" (Bindlib.name_of x) (Type.to_string t) (to_string body)
  | Apply (a, b) ->
      Printf.sprintf "%s %s" (to_string a) (to_string b)
  | TypeAbstract (Star, binder) ->
      let (x, body) = Bindlib.unbind binder in
      Printf.sprintf "Λ%s.%s" (Bindlib.name_of x) (to_string body)
  | TypeAbstract (k, binder) ->
      let (x, body) = Bindlib.unbind binder in
      Printf.sprintf "Λ(%s:%s).%s" (Bindlib.name_of x) (Kind.to_string k) (to_string body)
  | TypeApply (term, ty) ->
      Printf.sprintf "[%s %s]" (to_string term) (Type.to_string ty)
  | RowEmpty -> ""
  | RowExtend ((label, term), RowEmpty) ->
      Printf.sprintf "%s: %s" label (to_string term)
  | RowExtend ((label, term), rest) ->
      Printf.sprintf "%s: %s, %s" label (to_string term) (to_string rest)
  | Record RowEmpty -> "{}"
  | Record t ->
      Printf.sprintf "{ %s }" (to_string t)
  | RecordProject (t, label) ->
      Printf.sprintf "%s.%s" (to_string t) label
  | Fix t ->
      Printf.sprintf "fix (%s)" (to_string t)

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
let fix = Bindlib.box_apply (fun t -> Fix t)

let rec lift = function
  | Var x -> var x
  | Abstract (ty, b) -> abstract (Type.lift ty) (Bindlib.box_binder lift b)
  | Apply (a, b) -> apply (lift a) (lift b)
  | TypeAbstract (k, b) -> ty_abstract (Kind.lift k) (Bindlib.box_binder lift b)
  | TypeApply (te, ty) -> ty_apply (lift te) (Type.lift ty)
  | RowEmpty -> row_empty
  | RowExtend ((label, t), rest) ->
      row_extend (Bindlib.box label) (lift t) (lift rest)
  | Record t -> record (lift t)
  | RecordProject (t, label) -> record_project (lift t) (Bindlib.box label)
  | Fix t -> fix (lift t)
