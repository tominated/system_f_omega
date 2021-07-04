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
    | LetApply (x, (fn, arg), body) ->
        Printf.sprintf "let %s = %s %s in\n%s" x (value_to_string fn)
          (value_to_string arg) (to_string body)
    | LetPlus (x, (a, b), body) ->
        Printf.sprintf "let %s = %s + %s in\n%s" x (value_to_string a)
          (value_to_string b) (to_string body)
    | LetValue (x, value, body) ->
        Printf.sprintf "let %s = %s in\n%s" x (value_to_string value)
          (to_string body)
    | Value v ->
        value_to_string v
end

module CEK = struct
  type t = ANF.t * env * kont

  and env = value Map.M(String).t

  and value = Bool of bool | Int of int | Closure of string * ANF.t * env

  and kont = Halt | Arg of string * ANF.t * env * kont

  let to_value (env : env) : ANF.value -> value = function
    | Var v ->
        Map.find_exn env v
    | Int i ->
        Int i
    | Bool b ->
        Bool b
    | Lambda (arg, body) ->
        Closure (arg, body, env)

  let value_to_string : value -> string = function
    | Int i ->
        Int.to_string i
    | Bool b ->
        Bool.to_string b
    | Closure _ ->
        "<closure>"

  let step : t -> t = function
    | Value v, env, Arg (x, next_code, env', k) ->
        let env'' = Map.set env' ~key:x ~data:(to_value env v) in
        (next_code, env'', k)
    | LetValue (x, v, body), env, k ->
        let env' = Map.set env ~key:x ~data:(to_value env v) in
        (body, env', k)
    | TailIf (cond, if_true, if_false), env, k -> (
      match to_value env cond with
      | Bool true ->
          (if_true, env, k)
      | Bool false ->
          (if_false, env, k)
      | _ ->
          failwith "passed a non-boolean value to if" )
    | TailApply (fn, arg), env, k -> (
      match to_value env fn with
      | Closure (arg_var, closure_body, env') ->
          let env'' = Map.set env' ~key:arg_var ~data:(to_value env arg) in
          (closure_body, env'', k)
      | _ ->
          failwith "applied a non-closure value" )
    | LetApply (x, (fn, arg), body), env, k -> (
      match to_value env fn with
      | Closure (arg_var, closure_body, env') ->
          let env'' = Map.set env' ~key:arg_var ~data:(to_value env arg) in
          (closure_body, env'', Arg (x, body, env, k))
      | _ ->
          failwith "applied a non-closure value" )
    | TailPlus (a, b), env, Arg (x, next_code, env', k) -> (
      match (to_value env a, to_value env b) with
      | Int a, Int b ->
          let env'' = Map.set env' ~key:x ~data:(Int (a + b)) in
          (next_code, env'', k)
      | _ ->
          failwith "added a non-int value" )
    | LetPlus (x, (a, b), body), env, k -> (
      match (to_value env a, to_value env b) with
      | Int a, Int b ->
          let env' = Map.set env ~key:x ~data:(Int (a + b)) in
          (body, env', k)
      | _ ->
          failwith "added a non-int value" )
    | TailPlus _, _, _ | Value _, _, _ ->
        failwith "invalid state"

  let inject term : t =
    let env = Map.empty (module String) in
    let k = Arg ("__halt__", Value (Var "__halt__"), env, Halt) in
    (term, env, k)

  let evaluate term =
    let rec go : t -> value = function
      | Value v, env, Halt ->
          to_value env v
      | next ->
          go (step next)
    in
    go (inject term)
end

let direct_to_anf expr =
  let fresh =
    let last_num = ref 0 in
    fun prefix ->
      last_num := !last_num + 1 ;
      Printf.sprintf "%s%d" prefix !last_num
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
