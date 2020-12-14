open Core
open Syntax
open Unification

module UnderlyingContext = Context.MapContext (struct type t = Type.value end)

let rec value_infer ctx = function
  | Term.TmVar id -> Type.Substitution.empty, Option.value_exn (UnderlyingContext.find ctx id)
  | Term.Unit -> Type.Substitution.empty, Type.UnitType
  | Term.Const c -> Type.Substitution.empty, Term.type_of_const c
  | Term.Pair (s, t) ->
      let ms, ts = value_infer ctx s in
      let mt, tt = value_infer ctx t in
      let constraints = Constraints.append (Type.Substitution.constraints_of ms) (Type.Substitution.constraints_of mt) in
      (match Unification.unify Type.Substitution.empty constraints with
      | Some m -> m, Type.PairType (ts, tt)
      | None -> assert false)
  | Term.Inl (v, ty) ->
      let mv, tyv = value_infer ctx v in
      mv, Type.SumType (tyv, ty)
  | Term.Inr (v, ty) ->
      let mv, tyv = value_infer ctx v in
      mv, Type.SumType (ty, tyv)
  | Term.Thunk t ->
      let m, ty = computation_infer ctx t in
      m, Type.UType ty
and computation_infer ctx = function
  | Return v ->
      let m, ty = value_infer ctx v in
      m, Type.FType ty
  | SeqComp (c1, id, ty, c2) ->
      let m1, ty1 = computation_infer ctx c1 in
      let m2, ty2 = computation_infer (UnderlyingContext.add ctx id ty) c2 in
      let constraints_v, constraints_c = Constraints.append (Type.Substitution.constraints_of m1) (Type.Substitution.constraints_of m2) in
      (match unify Type.Substitution.empty (constraints_v, (Type.FType ty, ty1)::constraints_c) with
      | Some m -> m, ty2
      | None -> assert false)
  | Force (v, ty) ->
      let m, vty = value_infer ctx v in
      let constraints_v, constraints_c = Type.Substitution.constraints_of m in
      (match unify Type.Substitution.empty ((Type.UType ty, vty)::constraints_v, constraints_c) with
      | Some m -> m, ty
      | None -> assert false)
  | Lambda (id, ty, c) ->
      let m, ty' = computation_infer (UnderlyingContext.add ctx id ty) c in
      m, Type.FunctionType (ty, ty')
  | App (c, v, ty) ->
      let mc, tyc = computation_infer ctx c in
      let mv, tyv = value_infer ctx v in
      let constraints = [], [(Type.FunctionType (tyv, ty), tyc)] in
      let constraints = Constraints.append constraints (Type.Substitution.constraints_of mc) in
      let constraints = Constraints.append constraints (Type.Substitution.constraints_of mv) in
      (match unify Type.Substitution.empty constraints with
      | Some m -> m, ty
      | None -> assert false)
  | PatternMatch (v, x, a, y, b, c) ->
      let mv, tyv = value_infer ctx v in
      let mc, tyc = computation_infer (UnderlyingContext.add (UnderlyingContext.add ctx x a) y b) c in
      let constraints = [(Type.PairType (a, b), tyv)], [] in
      let constraints = Constraints.append constraints (Type.Substitution.constraints_of mc) in
      let constraints = Constraints.append constraints (Type.Substitution.constraints_of mv) in
      (match unify Type.Substitution.empty constraints with
      | Some m -> m, tyc
      | None -> assert false)
  | Case (v, x, a, m, y, b, n) ->
      let mv, tyv = value_infer ctx v in
      let mm, tym = computation_infer (UnderlyingContext.add ctx x a) m in
      let mn, tyn = computation_infer (UnderlyingContext.add ctx y b) n in
      let constraints = [(tyv, Type.SumType (a, b))], [(tym, tyn)] in
      let constraints = Constraints.append constraints (Type.Substitution.constraints_of mv) in
      let constraints = Constraints.append constraints (Type.Substitution.constraints_of mm) in
      let constraints = Constraints.append constraints (Type.Substitution.constraints_of mn) in
      Option.value_exn (unify Type.Substitution.empty constraints), tym
  | Fix (x, c, m) ->
      let map, ty = computation_infer (UnderlyingContext.add ctx x (Type.UType c)) m in
      let constraints = Constraints.append ([], [(c, ty)]) (Type.Substitution.constraints_of map) in
      Option.value_exn (unify Type.Substitution.empty constraints), c



