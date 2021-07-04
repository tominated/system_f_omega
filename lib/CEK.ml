open Base

module Direct = struct
  type t =
    | Var of string
    | Bool of bool
    | Int of int
    | Lambda of string * t
    | Apply of t * t
    | If of t * t * t
    | Let of string * t * t
    | Plus of t * t

  let rec to_string = function
    | Var v ->
        v
    | Int i ->
        Int.to_string i
    | Bool b ->
        Bool.to_string b
    | Lambda (arg, body) ->
        Printf.sprintf "(\\%s -> %s)" arg (to_string body)
    | Apply (fn, arg) ->
        Printf.sprintf "%s %s" (to_string fn) (to_string arg)
    | If (cond, if_true, if_false) ->
        Printf.sprintf "if %s then %s else %s" (to_string cond)
          (to_string if_true) (to_string if_false)
    | Let (v, value, body) ->
        Printf.sprintf "let %s = %s in\n%s" v (to_string value) (to_string body)
    | Plus (a, b) ->
        Printf.sprintf "(%s + %s)" (to_string a) (to_string b)
end

module ANF = struct
  type value =
    | Var of string
    | Int of int
    | Bool of bool
    | Lambda of string * t

  and t =
    | TailApply of value * value
    | TailIf of value * t * t
    | TailPlus of value * value
    | LetApply of string * (value * value) * t
    | LetPlus of string * (value * value) * t
    | LetValue of string * value * t
    | Value of value

  let rec value_to_string = function
    | Var v ->
        v
    | Int i ->
        Int.to_string i
    | Bool b ->
        Bool.to_string b
    | Lambda (arg, body) ->
        Printf.sprintf "\\%s -> %s" arg (to_string body)

  and to_string = function
    | TailApply (fn, arg) ->
        Printf.sprintf "%s %s" (value_to_string fn) (value_to_string arg)
    | TailIf (cond, if_true, if_false) ->
        Printf.sprintf "if %s then %s else %s" (value_to_string cond)
          (to_string if_true) (to_string if_false)
    | TailPlus (a, b) ->
        Printf.sprintf "%s + %s" (value_to_string a) (value_to_string b)
    | LetApply (v, (fn, arg), body) ->
        Printf.sprintf "let %s = %s %s in\n%s" v (value_to_string fn)
          (value_to_string arg) (to_string body)
    | LetPlus (v, (a, b), body) ->
        Printf.sprintf "let %s = %s + %s in\n%s" v (value_to_string a)
          (value_to_string b) (to_string body)
    | LetValue (v, value, body) ->
        Printf.sprintf "let %s = %s in\n%s" v (value_to_string value)
          (to_string body)
    | Value v ->
        value_to_string v
end

let direct_to_anf expr =
  let fresh =
    let last_num = ref 1 in
    fun prefix ->
      let x = !last_num in
      last_num := x + 1 ;
      Printf.sprintf "%s%d" prefix x
  in
  let rec trans0 : Direct.t -> ANF.t = function
    | Var x ->
        Value (Var x)
    | Int i ->
        Value (Int i)
    | Bool b ->
        Value (Bool b)
    | Lambda (args, body) ->
        Value (Lambda (args, trans0 body))
    | Apply (fn, arg) ->
        trans1 fn
        @@ fun fn_val ->
        trans1 arg @@ fun arg_val -> ANF.TailApply (fn_val, arg_val)
    | If (cond, if_true, if_false) ->
        trans1 cond
        @@ fun cond_val -> ANF.TailIf (cond_val, trans0 if_true, trans0 if_false)
    | Let (v, value, body) ->
        trans1 value @@ fun value_val -> ANF.LetValue (v, value_val, trans0 body)
    | Plus (a, b) ->
        trans1 a
        @@ fun a_val -> trans1 b @@ fun b_val -> ANF.TailPlus (a_val, b_val)
  and trans1 (expr : Direct.t) (k : ANF.value -> ANF.t) : ANF.t =
    match expr with
    | Var x ->
        k (Var x)
    | Int i ->
        k (Int i)
    | Bool b ->
        k (Bool b)
    | Lambda (arg, body) ->
        k (Lambda (arg, trans0 body))
    | Apply (fn, arg) ->
        trans1 fn
        @@ fun fn_val ->
        trans1 arg
        @@ fun arg_val ->
        let v = fresh "app" in
        LetApply (v, (fn_val, arg_val), k (Var v))
    | If (cond, if_true, if_false) ->
        trans1 cond
        @@ fun cond_val -> TailIf (cond_val, trans0 if_true, trans0 if_false)
    | Let (x, value, body) ->
        trans1 value @@ fun value_val -> LetValue (x, value_val, trans1 body k)
    | Plus (a, b) ->
        trans1 a
        @@ fun a_val ->
        trans1 b
        @@ fun b_val ->
        let v = fresh "plus" in
        LetPlus (v, (a_val, b_val), k (Var v))
  in
  trans0 expr
