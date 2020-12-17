open Core
open Utils

module Type = struct
  type t =
    | Var of string
    | Int
    | Unit
    | Function of t * t
    | Sum of t * t
    | Pair of t * t

  let rec to_string' = function
    | Var x -> 100, x
    | Int -> 100, "int"
    | Unit -> 100, "()"
    | Function (a, b) -> 40, (to_string' a |> add_paren_if_needed 41) ^ " -> " ^ (to_string' b |> add_paren_if_needed 40)
    | Sum (a, b) -> 10, (to_string' a |> add_paren_if_needed 10) ^ " + " ^ (to_string' b |> add_paren_if_needed 10)
    | Pair (a, b) -> 20, (to_string' a |> add_paren_if_needed 20) ^ " * " ^ (to_string' b |> add_paren_if_needed 20)

  let to_string t = let _, s = to_string' t in s
end

module Term = struct
  type op =
    | Int of int
    | Add
    | Leq

  type t =
    | Var of string
    | Const of op
    | Lambda of string * t
    | App of t * t
    | Unit
    | Inl of t
    | Inr of t
    | Case of t * string * t * string * t
    | Pair of t * t
    | PatternMatch of t * string * string * t
    | Fix of string * t
    | TypeAssert of t * Type.t
end

