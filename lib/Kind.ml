open Base

type t = Star | Row | Arrow of t * t

let rec to_string = function
  | Star ->
      "*"
  | Row ->
      "Row"
  | Arrow (a, b) ->
      Printf.sprintf "%s -> %s" (to_string a) (to_string b)

let rec equal a b =
  match (a, b) with
  | Star, Star ->
      true
  | Row, Row ->
      true
  | Arrow (a1, b1), Arrow (a2, b2) ->
      equal a1 b1 && equal a2 b2
  | _ ->
      false

let star = Bindlib.box Star

let row = Bindlib.box Row

let arrow = Bindlib.box_apply2 (fun a b -> Arrow (a, b))

let rec lift = function
  | Star ->
      star
  | Row ->
      row
  | Arrow (a, b) ->
      arrow (lift a) (lift b)
