open Core
open Logic

type value =
  | EmptyType
  | RefinedUnitType of string * Formula.t
  | RefinedIntType of string * Formula.t
  | PairType of string * value * value
  | SumType of value * value
  | UType of computation
and computation =
  | FunctionType of string * value * computation
  | FType of value

let rec value_erasure = function
  | EmptyType -> Syntax.Type.EmptyType
  | RefinedUnitType _ -> Syntax.Type.UnitType
  | RefinedIntType _ -> Syntax.Type.IntType
  | PairType (_, a, b) -> Syntax.Type.PairType (value_erasure a, value_erasure b)
  | SumType (a, b) -> Syntax.Type.SumType (value_erasure a, value_erasure b)
  | UType c -> Syntax.Type.UType (computation_erasure c)
and computation_erasure = function
  | FunctionType (_, a, c) -> Syntax.Type.FunctionType (value_erasure a, computation_erasure c)
  | FType a -> Syntax.Type.FType (value_erasure a)

let rec value_to_string = function
  | EmptyType -> "empty"
  | RefinedUnitType (v, p) -> Printf.sprintf "{ %s : unit | %s }" v (Formula.to_string p)
  | RefinedIntType (v, p) -> Printf.sprintf "{ %s : int | %s }" v (Formula.to_string p)
  | PairType (x, a, b) -> Printf.sprintf "(%s : %s) * %s" x (value_to_string a) (value_to_string b)
  | SumType (a, b) -> Printf.sprintf "%s + %s" (value_to_string a) (value_to_string b)
  | UType c -> "U " ^ computation_to_string c
and computation_to_string = function
  | FType a -> "F " ^ value_to_string a
  | FunctionType (x, a, c) -> Printf.sprintf "(%s : %s) -> %s" x (value_to_string a) (computation_to_string c)

let rec value_subst map = function
  | EmptyType -> EmptyType
  | RefinedUnitType (x, p) -> RefinedUnitType (x, Formula.subst_term map p)
  | RefinedIntType (x, p) -> RefinedIntType (x, Formula.subst_term map p)
  | PairType (x, a, b) -> PairType (x, value_subst map a, value_subst map b) (* todo: check that x is fresh *)
  | SumType (a, b) -> SumType (value_subst map a, value_subst map b)
  | UType c -> UType (computation_subst map c)
and computation_subst map = function
  | FunctionType (x, a, c) -> FunctionType (x, value_subst map a, computation_subst map c) (* todo: check that x is fresh *)
  | FType a -> FType (value_subst map a)
