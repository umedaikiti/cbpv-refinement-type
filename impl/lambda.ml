open Core
open Utils

type type_t =
  | TyVar of string
  | IntType
  | UnitType
  | FunctionType of type_t * type_t
  | SumType of type_t * type_t
  | PairType of type_t * type_t

type op =
  | Int of int
  | Add

type term =
  | Var of string
  | Const of op
  | Lambda of string * term
  | App of term * term
  | Unit
  | Inl of term
  | Inr of term
  | Case of term * string * term * string * term
  | Pair of term * term
  | PatternMatch of term * string * string * term

let rec type_to_string' = function
  | TyVar x -> 100, x
  | IntType -> 100, "int"
  | UnitType -> 100, "()"
  | FunctionType (a, b) -> 40, (type_to_string' a |> add_paren_if_needed 41) ^ " -> " ^ (type_to_string' b |> add_paren_if_needed 40)
  | SumType (a, b) -> 10, (type_to_string' a |> add_paren_if_needed 10) ^ " + " ^ (type_to_string' b |> add_paren_if_needed 10)
  | PairType (a, b) -> 20, (type_to_string' a |> add_paren_if_needed 20) ^ " * " ^ (type_to_string' b |> add_paren_if_needed 20)

let type_to_string t = let _, s = type_to_string' t in s
