open Core
open Syntax
open Unification

module UnderlyingContext = Context.MapContext (struct type t = Type.value end)

let rec value_infer ctx = function
  | Term.TmVar id -> Option.(UnderlyingContext.find ctx id >>= fun ty -> return (Type.Substitution.empty, ty))
  | Term.Unit -> Some (Type.Substitution.empty, Type.UnitType)
  | Term.Const c -> Some (Type.Substitution.empty, Term.type_of_const c)
  | Term.Pair (s, t) ->
      Option.(value_infer ctx s >>= fun (ms, ts) ->
        value_infer ctx t >>= fun (mt, tt) ->
        let constraints = Constraints.append (Type.Substitution.constraints_of ms) (Type.Substitution.constraints_of mt) in
        Unification.unify constraints >>= fun m ->
        return (m, Type.PairType (ts, tt)))
  | Term.Inl (v, ty) ->
      Option.(value_infer ctx v >>= fun (mv, tyv) ->
        return (mv, Type.SumType (tyv, ty)))
  | Term.Inr (v, ty) ->
      Option.(value_infer ctx v >>= fun (mv, tyv)->
        return (mv, Type.SumType (ty, tyv)))
  | Term.Thunk t ->
      Option.(computation_infer ctx t >>= fun (m, ty) ->
        return (m, Type.UType ty))
and computation_infer ctx = function
  | Return v ->
      Option.(value_infer ctx v >>= fun (m, ty) ->
        return (m, Type.FType ty))
  | SeqComp (c1, id, ty, c2) ->
      Option.(computation_infer ctx c1 >>= fun (m1, ty1) ->
        computation_infer (UnderlyingContext.add ctx id ty) c2 >>= fun (m2, ty2) ->
        let constraints_v, constraints_c = Constraints.append (Type.Substitution.constraints_of m1) (Type.Substitution.constraints_of m2) in
        unify (constraints_v, (Type.FType ty, ty1)::constraints_c) >>= fun m ->
        return (m, ty2))
  | Force (v, ty) ->
      Option.(value_infer ctx v >>= fun (m, tyv) ->
        let constraints_v, constraints_c = Type.Substitution.constraints_of m in
        unify ((Type.UType ty, tyv)::constraints_v, constraints_c) >>= fun m ->
        return (m, ty))
  | Lambda (id, ty, c) ->
      Option.(computation_infer (UnderlyingContext.add ctx id ty) c >>= fun (m, ty') ->
        return (m, Type.FunctionType (ty, ty')))
  | App (c, v, ty) ->
      Option.(computation_infer ctx c >>= fun (mc, tyc) ->
        value_infer ctx v >>= fun (mv, tyv) ->
        let constraints = [], [(Type.FunctionType (tyv, ty), tyc)] in
        let constraints = Constraints.append constraints (Type.Substitution.constraints_of mc) in
        let constraints = Constraints.append constraints (Type.Substitution.constraints_of mv) in
        unify constraints >>= fun m ->
        return (m, ty))
  | PatternMatch (v, x, a, y, b, c) ->
      Option.(value_infer ctx v >>= fun (mv, tyv) ->
        computation_infer (UnderlyingContext.add (UnderlyingContext.add ctx x a) y b) c >>= fun (mc, tyc) ->
        let constraints = [(Type.PairType (a, b), tyv)], [] in
        let constraints = Constraints.append constraints (Type.Substitution.constraints_of mc) in
        let constraints = Constraints.append constraints (Type.Substitution.constraints_of mv) in
        unify constraints >>= fun m ->
        return (m, tyc))
  | Case (v, x, a, m, y, b, n) ->
      Option.(value_infer ctx v >>= fun (mv, tyv) ->
        computation_infer (UnderlyingContext.add ctx x a) m >>= fun (mm, tym) ->
        computation_infer (UnderlyingContext.add ctx y b) n >>= fun (mn, tyn) ->
        let constraints = [(tyv, Type.SumType (a, b))], [(tym, tyn)] in
        let constraints = Constraints.append constraints (Type.Substitution.constraints_of mv) in
        let constraints = Constraints.append constraints (Type.Substitution.constraints_of mm) in
        let constraints = Constraints.append constraints (Type.Substitution.constraints_of mn) in
        unify constraints >>= fun map ->
        return (map, tym))
  | Fix (x, c, m) ->
      Option.(computation_infer (UnderlyingContext.add ctx x (Type.UType c)) m >>= fun (map, ty) ->
        let constraints = Constraints.append ([], [(c, ty)]) (Type.Substitution.constraints_of map) in
        unify constraints >>= fun map ->
        return (map, c))
  | Explode (v, c) ->
      Option.(value_infer ctx v >>= fun (map, ty) ->
        let constraints = Constraints.append (Type.Substitution.constraints_of map) ([(ty, Type.EmptyType)], []) in
        unify constraints >>= fun map ->
        return (map, c))
  | GenOp (op, v) ->
      Option.(value_infer ctx v >>= fun (map, ty) ->
      let type_in, type_out = Term.type_of_alg_op op in
      let constraints = Constraints.append (Type.Substitution.constraints_of map) ([(ty, type_in)], []) in
      unify constraints >>= fun map ->
      return (map, Type.FType type_out))
  | CompTypeAssert (m, c) ->
      Option.(computation_infer ctx m >>= fun (map, ty) ->
      let constraints = Constraints.append (Type.Substitution.constraints_of map) ([], [(ty, c)]) in
      unify constraints >>= fun map ->
      return (map, c))

