open Core
open Syntax
open Syntax.Type

module Constraints = struct
  type t = (Type.value * Type.value) list * (Type.computation * Type.computation) list
  let append (cv1, cc1) (cv2, cc2) = cv1 @ cv2, cc1 @ cc2
end

let rec unify' (mv, mc) = function
  | [], [] -> Some (mv, mc)
  | [], (CompTyVar id, CompTyVar id')::cc when String.(id = id') -> unify' (mv, mc) ([], cc)
  | [], (CompTyVar id, t)::cc ->
      (match Map.find mc id with
      | Some s -> unify' (mv, mc) ([], (s, t)::cc)
      | None ->
          let t = Substitution.computation_subst (mv, mc) t in
          if Set.mem (let _, cv = computation_fv t in cv) id then
            None
          else
            let m' = Map.empty (module String), Map.singleton (module String) id t in
            unify' (Substitution.compose (mv, mc) m') ([], cc))
  | [], (t, CompTyVar id)::cc -> unify' (mv, mc) ([], (CompTyVar id, t)::cc) (* swap *)
  | [], (FunctionType (vt1, ct1), FunctionType (vt2, ct2))::cc -> unify' (mv, mc) ([(vt1, vt2)], (ct1, ct2)::cc)
  | [], (FType t1, FType t2)::cc -> unify' (mv, mc) ([(t1, t2)], cc)
  | [], _::cc -> None
  | (ValTyVar id, ValTyVar id')::cv, cc when String.(id = id') -> unify' (mv, mc) (cv, cc)
  | (ValTyVar id, t)::cv, cc ->
      (match Map.find mv id with
      | Some s -> unify' (mv, mc) ((s, t)::cv, cc)
      | None ->
          let t = Substitution.value_subst (mv, mc) t in
          if Set.mem (let vv, _ = value_fv t in vv) id then
            None
          else
            let m' = Map.singleton (module String) id t, Map.empty (module String) in
            unify' (Substitution.compose (mv, mc) m') (cv, cc))
  | (t, ValTyVar id)::cv, cc -> unify' (mv, mc) ((ValTyVar id, t)::cv, cc)
  | (UnitType, UnitType)::cv, cc -> unify' (mv, mc) (cv, cc)
  | (IntType, IntType)::cv, cc -> unify' (mv, mc) (cv, cc)
  | (PairType (a1, b1), PairType (a2, b2))::cv, cc -> unify' (mv, mc) ((a1, a2)::(b1, b2)::cv, cc)
  | (SumType (a1, b1), SumType (a2, b2))::cv, cc -> unify' (mv, mc) ((a1, a2)::(b1, b2)::cv, cc)
  | (UType c1, UType c2)::cv, cc -> unify' (mv, mc) (cv, (c1, c2)::cc)
  | _::cv, cc -> None

let unify = unify' Substitution.empty

