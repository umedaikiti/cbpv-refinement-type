open Core
open Syntax
open Logic

let rec simplify_constraint' ctx fml =
  match ctx with
  | [] -> [([], fml)]
  | (x, Type.SumType (a, b))::ctx' ->
      let fml_inl = Formula.subst_term (Map.singleton (module String) x (Term.Inl (Term.TmVar x))) fml in
      let fml_inr = Formula.subst_term (Map.singleton (module String) x (Term.Inr (Term.TmVar x))) fml in
      let cl = simplify_constraint' ((x, a)::ctx') fml_inl in
      let cr = simplify_constraint' ((x, b)::ctx') fml_inr in
      cl @ cr
  | (x, Type.PairType (a, b))::ctx' ->
      let y = mk_fresh_term_var () in
      let z = mk_fresh_term_var () in
      let fml' = Formula.subst_term (Map.singleton (module String) x (Term.Pair (Term.TmVar y, Term.TmVar z))) fml in
      simplify_constraint' ((y, a)::(z, b)::ctx') fml'
  | (x, Type.UnitType)::ctx' ->
      let fml = Formula.subst_term (Map.singleton (module String) x (Term.Unit)) fml in
      simplify_constraint' ctx' fml
  | (x, a)::ctx' ->
      simplify_constraint' ctx' fml |> List.map ~f:(fun (c, f) -> ((x, a)::c, f))

let simplify_constraint (ctx, fml) = simplify_constraint' ctx fml

let rec simplify_equalities_equal v u =
  match v, u with
  | Term.Unit, Term.Unit -> []
  | Term.Inl v, Term.Inl u -> simplify_equalities_equal v u
  | Term.Inr v, Term.Inr u -> simplify_equalities_equal v u
  | Term.Pair (v1, v2), Term.Pair (u1, u2) -> simplify_equalities_equal v1 u1 @ simplify_equalities_equal v2 u2
  | _, _ -> [Formula.Equal (v, u)]

let rec simplify_equalities =
  function
  | Formula.Equal (v, u) -> Formula.And (simplify_equalities_equal v u)
  | PVar (p, args) -> PVar (p, args)
  | True -> True
  | False -> False
  | And l -> And (List.map ~f:simplify_equalities l)
  | Or l -> Or (List.map ~f:simplify_equalities l)
  | Implies (p, q) -> Implies (simplify_equalities p, simplify_equalities q)

