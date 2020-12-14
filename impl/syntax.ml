open Core
open Utils

module Type = struct
  type value =
    | ValTyVar of string
    | UnitType
    | IntType
    | PairType of value * value
    | SumType of value * value
    | UType of computation
  and computation =
    | CompTyVar of string
    | FunctionType of value * computation
    | FType of value

  let rec is_pure = function
    | UnitType | IntType -> true
    | PairType (a, b) | SumType (a, b) -> is_pure a && is_pure b
    | _ -> false

  (* free variables *)
  let rec value_fv = function
    | ValTyVar id -> Set.singleton (module String) id, Set.empty (module String)
    | UnitType -> Set.empty (module String), Set.empty (module String)
    | IntType -> Set.empty (module String), Set.empty (module String)
    | PairType (a, b) ->
        let av, ac = value_fv a in
        let bv, bc = value_fv b in
        Set.union av bv, Set.union ac bc
    | SumType (a, b) ->
        let av, ac = value_fv a in
        let bv, bc = value_fv b in
        Set.union av bv, Set.union ac bc
    | UType c -> computation_fv c
  and computation_fv = function
    | CompTyVar id -> Set.empty (module String), Set.singleton (module String) id
    | FunctionType (a, c) ->
        let av, ac = value_fv a in
        let cv, cc = computation_fv c in
        Set.union av cv, Set.union ac cc
    | FType a -> value_fv a

  let rec value_to_string' = function
    | ValTyVar id -> 100, id
    | UnitType -> 100, "unit"
    | IntType -> 100, "int"
    | PairType (a, b) -> 20, (value_to_string' a |> add_paren_if_needed 20) ^ " * " ^ (value_to_string' b |> add_paren_if_needed 20)
    | SumType (a, b) -> 10, (value_to_string' a |> add_paren_if_needed 10) ^ " + " ^ (value_to_string' b |> add_paren_if_needed 10)
    | UType c -> 40, "U " ^ (computation_to_string' c |> add_paren_if_needed 40)
  and computation_to_string' = function
    | CompTyVar id -> 100, id
    | FunctionType (a, c) -> 30, (value_to_string' a |> add_paren_if_needed 30) ^ " -> " ^ (computation_to_string' c |> add_paren_if_needed 30)
    | FType a -> 40, "F " ^ (value_to_string' a |> add_paren_if_needed 40)

  let value_to_string ty = let _, s = value_to_string' ty in s
  let computation_to_string ty = let _, s = computation_to_string' ty in s

  module Substitution = struct
    type value_t = (string,value,String.comparator_witness) Map.t
    type computation_t = (string,computation,String.comparator_witness) Map.t
    let empty = (Map.empty (module String), Map.empty (module String))
    let lookup_value m id =
      match Map.find m id with
      | Some x -> x
      | None -> ValTyVar id
    let lookup_computation m id =
      match Map.find m id with
      | Some x -> x
      | None -> CompTyVar id
    let rec value_subst (mv, mc) = function
      | ValTyVar id -> lookup_value mv id
      | UnitType -> UnitType
      | IntType -> IntType
      | PairType (a, b) -> PairType (value_subst (mv, mc) a, value_subst (mv, mc) b)
      | SumType (a, b) -> SumType (value_subst (mv, mc) a, value_subst (mv, mc) b)
      | UType c -> UType (computation_subst (mv, mc) c)
    and computation_subst (mv, mc) = function
      | CompTyVar id -> lookup_computation mc id
      | FunctionType (a, c) -> FunctionType (value_subst (mv, mc) a, computation_subst (mv, mc) c)
      | FType a -> FType (value_subst (mv, mc) a)
    let compose (mv1, mc1) (mv2, mc2) =
      let mv = Map.merge mv1 mv2 ~f:(fun ~key -> function
        | `Left t | `Both (t, _) -> Some (value_subst (mv2, mc2) t)
        | `Right t -> Some t) in
      let mc = Map.merge mc1 mc2 ~f:(fun ~key -> function
        | `Left t | `Both (t, _) -> Some (computation_subst (mv2, mc2) t)
        | `Right t -> Some t) in
      mv, mc
    let constraints_of (mv, mc) =
      let cv = Map.to_alist mv |> List.map ~f:(fun (v, t) -> (ValTyVar v, t)) in
      let cc = Map.to_alist mc |> List.map ~f:(fun (v, t) -> (CompTyVar v, t)) in
      cv, cc
  end
end

module Term = struct
  type constants =
    | Int of int
    | Add
  type value =
    | TmVar of string
    | Unit
    | Const of constants
    | Pair of value * value
    | Inl of value * Type.value
    | Inr of value * Type.value
    | Thunk of computation
  and computation =
    | Return of value
    | SeqComp of computation * string * Type.value * computation
    | Force of value * Type.computation
    | Lambda of string * Type.value * computation
    | App of computation * value * Type.computation
    | PatternMatch of value * string * Type.value * string * Type.value * computation
    | Case of value * string * Type.value * computation * string * Type.value * computation
    | Fix of string * Type.computation * computation

  let constant_to_string = function
    | Int n -> string_of_int n
    | Add -> "(+)"

  let type_of_operation arg_types body_type =
    Type.UType (List.fold_right arg_types ~f:(fun arg body -> Type.FunctionType (arg, body)) ~init:(Type.FType body_type))

  let type_of_const = function
    | Int n -> Type.IntType
    | Add -> type_of_operation [Type.IntType; Type.IntType] Type.IntType


  let rec value_to_string = function
    | TmVar id -> id
    | Unit -> "()"
    | Const c -> constant_to_string c
    | Pair (v, w) -> "(" ^ value_to_string v ^ ", " ^ value_to_string w ^ ")"
    | Inl (v, _) -> "inl " ^ value_to_string v
    | Inr (v, _) -> "inr " ^ value_to_string v
    | Thunk c -> "thunk (" ^ computation_to_string c ^ ")"
  and computation_to_string = function
    | Return v -> "return (" ^ value_to_string v ^ ")"
    | SeqComp (m, x, a, n) -> computation_to_string m ^ " to " ^ x ^ " : " ^ Type.value_to_string a ^ " in " ^ computation_to_string n
    | Force (v, c) -> "force(" ^ Type.computation_to_string c ^ ", " ^ value_to_string v ^ ")"
    | Lambda (x, a, m) -> "fun " ^ x ^ " : " ^ Type.value_to_string a ^ " => " ^ computation_to_string m
    | App (c, v, _ty) -> computation_to_string c ^ " @ " ^ value_to_string v (* ^ " : " ^ Type.computation_to_string ty *)
    | PatternMatch (v, x, a, y, b, m) -> "pm " ^ value_to_string v ^ " to (" ^ x ^ " : " ^ Type.value_to_string a ^ ", " ^ y ^ " : " ^ Type.value_to_string b ^ " in " ^ computation_to_string m ^ ")"
    | Case (v, x, a, m, y, b, n) -> Printf.sprintf "case %s of [inl (%s : %s) -> %s; inr (%s : %s) -> %s]" (value_to_string v) x (Type.value_to_string a) (computation_to_string m) y (Type.value_to_string b) (computation_to_string n)
    | Fix (x, c, m) -> Printf.sprintf "fix (%s : U %s). %s" x (Type.computation_to_string c) (computation_to_string m)

  (*let rec free_type_var_in_value and free_type_var_in_computation*)
  let rec value_free_term_var = function
    | TmVar x -> Set.singleton (module String) x
    | Unit
    | Const _ -> Set.empty (module String)
    | Pair (v, w) -> Set.union (value_free_term_var v) (value_free_term_var w)
    | Inl (v, _) -> value_free_term_var v
    | Inr (v, _) -> value_free_term_var v
    | Thunk c -> computation_free_term_var c
  and computation_free_term_var = function
    | Return v -> value_free_term_var v
    | SeqComp (m, x, _, n) -> Set.union (computation_free_term_var m) (Set.remove (computation_free_term_var n) x)
    | Force (v, _) -> value_free_term_var v
    | Lambda (x, _, m) -> Set.remove (computation_free_term_var m) x
    | App (m, v, _) -> Set.union (computation_free_term_var m) (value_free_term_var v)
    | PatternMatch (v, x, _, y, _, m) -> Set.union (value_free_term_var v) (Set.remove (Set.remove (computation_free_term_var m) x) y)
    | Case (v, x, _, m, y, _, n) -> Set.union (value_free_term_var v) (Set.union (Set.remove (computation_free_term_var m) x) (Set.remove (computation_free_term_var n) y))
    | Fix (x, _, m) -> Set.remove (computation_free_term_var m) x

  let rec value_subst_type m = function
    | TmVar x -> TmVar x
    | Unit -> Unit
    | Const c -> Const c
    | Pair (v, w) -> Pair (value_subst_type m v, value_subst_type m w)
    | Inl (v, b) -> Inl (value_subst_type m v, Type.Substitution.value_subst m b)
    | Inr (v, a) -> Inr (value_subst_type m v, Type.Substitution.value_subst m a)
    | Thunk c -> Thunk (computation_subst_type m c)
  and computation_subst_type map = function
    | Return v -> Return (value_subst_type map v)
    | SeqComp (m, x, a, n) -> SeqComp (computation_subst_type map m, x, Type.Substitution.value_subst map a, computation_subst_type map n)
    | Force (v, c) -> Force (value_subst_type map v, Type.Substitution.computation_subst map c)
    | Lambda (x, a, m) -> Lambda (x, Type.Substitution.value_subst map a, computation_subst_type map m)
    | App (c, v, ty) -> App (computation_subst_type map c, value_subst_type map v, Type.Substitution.computation_subst map ty)
    | PatternMatch (v, x, a, y, b, m) -> PatternMatch (value_subst_type map v, x, Type.Substitution.value_subst map a, y, Type.Substitution.value_subst map b, computation_subst_type map m)
    | Case (v, x, a, m, y, b, n) -> Case (value_subst_type map v, x, Type.Substitution.value_subst map a, computation_subst_type map m, y, Type.Substitution.value_subst map b, computation_subst_type map n)
    | Fix (x, c, m) -> Fix (x, Type.Substitution.computation_subst map c, computation_subst_type map m)

  let map_fv map =
    Map.to_alist map
    |> List.map ~f:(fun (key, data) -> Set.add (value_free_term_var data) key)
    |> Set.union_list (module String)

  let rec value_subst_term map = function
    | TmVar x -> (match Map.find map x with Some t -> t | None -> TmVar x)
    | Unit -> Unit
    | Const c -> Const c
    | Pair (v, w) -> Pair (value_subst_term map v, value_subst_term map w)
    | Inl (v, b) -> Inl (value_subst_term map v, b)
    | Inr (v, a) -> Inr (value_subst_term map v, a)
    | Thunk c -> Thunk (computation_subst_term map c)
  and computation_subst_term map = function
    | Return v -> Return (value_subst_term map v)
    | SeqComp (m, x, a, n) ->
        let x' = Utils.mk_fresh_name x (map_fv map) in
        let map' = Map.update map x ~f:(fun _ -> TmVar x') in
        SeqComp (computation_subst_term map m, x', a, computation_subst_term map' n)
    | Force (v, c) -> Force (value_subst_term map v, c)
    | Lambda (x, a, m) ->
        let x' = Utils.mk_fresh_name x (map_fv map) in
        let map' = Map.update map x ~f:(fun _ -> TmVar x') in
        Lambda (x', a, computation_subst_term map' m)
    | App (c, v, ty) -> App (computation_subst_term map c, value_subst_term map v, ty)
    | PatternMatch (v, x, a, y, b, m) ->
        assert String.(x <> y);
        let y' = Utils.mk_fresh_name y (map_fv map) in
        let x' = Utils.mk_fresh_name x (Set.add (map_fv map) y') in
        let map' = Map.update (Map.update map x ~f:(fun _ -> TmVar x')) y ~f:(fun _ -> TmVar y') in
        PatternMatch (value_subst_term map v, x', a, y', b, computation_subst_term map' m)
    | Case (v, x, a, m, y, b, n) ->
        let x' = Utils.mk_fresh_name x (map_fv map) in
        let map_m = Map.update map x ~f:(fun _ -> TmVar x') in
        let y' = Utils.mk_fresh_name y (map_fv map) in
        let map_n = Map.update map x ~f:(fun _ -> TmVar y') in
        Case (value_subst_term map v, x', a, computation_subst_term map_m m, y', b, computation_subst_term map_n n)
    | Fix (x, c, m) ->
        let x' = Utils.mk_fresh_name x (map_fv map) in
        let map' = Map.update map x ~f:(fun _ -> TmVar x') in
        Fix (x', c, computation_subst_term map' m)

  let rec value_elim_shadow ?(used = Set.empty (module String)) ?(map = Map.empty (module String)) = function
    | TmVar x -> TmVar (match Map.find map x with Some x' -> x' | None -> x)
    | Unit -> Unit
    | Const c -> Const c
    | Pair (v, w) -> Pair (value_elim_shadow ~used ~map v, value_elim_shadow ~used ~map w)
    | Inl (v, b) -> Inl (value_elim_shadow ~used ~map v, b)
    | Inr (v, a) -> Inr (value_elim_shadow ~used ~map v, a)
    | Thunk c -> Thunk (computation_elim_shadow ~used ~map c)
  and computation_elim_shadow ?(used = Set.empty (module String)) ?(map = Map.empty (module String)) = function
    | Return v -> Return (value_elim_shadow ~used ~map v)
    | SeqComp (m, x, a, n) ->
        let x' = Utils.mk_fresh_name x used in
        let used' = Set.add used x' in
        let map' = Map.update map x ~f:(fun _ -> x') in
        SeqComp (computation_elim_shadow ~used ~map m, x', a, computation_elim_shadow ~used:used' ~map:map' n)
    | Force (v, c) -> Force (value_elim_shadow ~used ~map v, c)
    | Lambda (x, a, m) ->
        let x' = Utils.mk_fresh_name x used in
        let used' = Set.add used x' in
        let map' = Map.update map x ~f:(fun _ -> x') in
        Lambda (x', a, computation_elim_shadow ~used:used' ~map:map' m)
    | App (m, v, ty) -> App (computation_elim_shadow ~used ~map m, value_elim_shadow ~used ~map v, ty)
    | PatternMatch (v, x, a, y, b, m) ->
        let x' = Utils.mk_fresh_name x used in
        let used' = Set.add used x' in
        let map' = Map.update map x ~f:(fun _ -> x') in
        let y' = Utils.mk_fresh_name y used' in
        let used'' = Set.add used' y' in
        let map'' = Map.update map' y ~f:(fun _ -> y') in
        PatternMatch (value_elim_shadow ~used ~map v, x', a, y', b, computation_elim_shadow ~used:used'' ~map:map'' m)
    | Case (v, x, a, m, y, b, n) ->
        let x' = Utils.mk_fresh_name x used in
        let used' = Set.add used x' in
        let map' = Map.update map x ~f:(fun _ -> x') in
        let m' = computation_elim_shadow ~used:used' ~map:map' m in
        let y' = Utils.mk_fresh_name y used in
        let used' = Set.add used y' in
        let map' = Map.update map y ~f:(fun _ -> y') in
        let n' = computation_elim_shadow ~used:used' ~map:map' n in
        Case (value_elim_shadow ~used ~map v, x', a, m', y', b, n')
    | Fix (x, c, m) ->
        let x' = Utils.mk_fresh_name x used in
        let used' = Set.add used x' in
        let map' = Map.update map x ~f:(fun _ -> x') in
        Fix (x', c, computation_elim_shadow ~used:used' ~map:map' m)

  let rec value_simplify = function
    | TmVar x -> TmVar x
    | Unit -> Unit
    | Const c -> Const c
    | Pair (v, w) -> Pair (value_simplify v, value_simplify w)
    | Inl (v, b) -> Inl (value_simplify v, b)
    | Inr (v, a) -> Inr (value_simplify v, a)
    | Thunk c -> Thunk (computation_simplify c)
  and computation_simplify = function
    | Return v -> Return (value_simplify v)
    | SeqComp (m, x, a, n) ->
        (match computation_simplify m, computation_simplify n with
        | Return v, n' -> computation_simplify (computation_subst_term (Map.singleton (module String) x v) n')
        | m', Return (TmVar x') when String.(x = x') -> m'
        | m', n' -> SeqComp (m', x, a, n'))
    | Force (Thunk m, c) -> computation_simplify m
    | Force (v, c) -> Force (value_simplify v, c)
    | Lambda (x, a, m) -> Lambda (x, a, computation_simplify m)
    | App (c, v, ty) -> App (computation_simplify c, value_simplify v, ty) (* beta reduction? *)
    | PatternMatch (v, x, a, y, b, m) -> PatternMatch (value_simplify v, x, a, y, b, computation_simplify m) (* beta reduction? *)
    | Case (v, x, a, m, y, b, n) -> Case (value_simplify v, x, a, computation_simplify m, y, b, computation_simplify n) (* beta reduction? *)
    | Fix (x, c, m) -> Fix (x, c, computation_simplify m)
end

let type_var_counter = ref 0
let mk_fresh_value_type_var () =
  Type.ValTyVar ("#tyv" ^ string_of_int (inc_counter type_var_counter))
let mk_fresh_computation_type_var () =
  Type.CompTyVar ("#tyv" ^ string_of_int (inc_counter type_var_counter))

let term_var_counter = ref 0
let mk_fresh_term_var () =
  "#tmv" ^ string_of_int (inc_counter term_var_counter)


