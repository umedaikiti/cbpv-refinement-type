open Core
open Syntax
open Refinement

module RefinementContext = struct
  include Context.ListContext (struct type t = Refinement.value end)

  let rec erase_purify ctx =
    List.map ctx ~f:(fun (x, a) -> (x, value_erasure a))
    |> List.filter ~f:(fun (x, a) -> Type.is_pure a)

  let collect_predicates =
    List.filter_map ~f:(fun (x, a) -> match a with
      | RefinedUnitType (v, p) -> Some Logic.(Formula.rename_term_var v x p)
      | RefinedIntType (v, p) -> Some Logic.(Formula.rename_term_var v x p)
      | _ -> None)
end

(* ctx |- a <: b *)
let rec subtype_value ctx a b =
  let open Logic in
  match a, b with
  | RefinedUnitType (v, p), RefinedUnitType (u, q) ->
      let q = Formula.rename_term_var u v q in
      [(RefinementContext.add (RefinementContext.erase_purify ctx) v Type.UnitType, Formula.Implies (Formula.And (p :: RefinementContext.collect_predicates ctx), q))]
  | RefinedIntType (v, p), RefinedIntType (u, q) ->
      let q = Formula.rename_term_var u v q in
      [(RefinementContext.add (RefinementContext.erase_purify ctx) v Type.IntType, Formula.Implies (Formula.And (p :: RefinementContext.collect_predicates ctx), q))]
  | PairType (x, a, b), PairType (y, c, d) ->
      let d = Refinement.value_subst (Map.singleton (module String) y (Term.TmVar x)) d in
      subtype_value ctx a c @ subtype_value (RefinementContext.add ctx x a) b d
  | SumType (a, b), SumType (c, d) -> subtype_value ctx a c @ subtype_value ctx b d
  | UType c, UType d -> subtype_computation ctx c d
  | _, _ -> failwith "mismatch of underlying types"
and subtype_computation ctx a b =
  let open Logic in
  match a, b with
  | FunctionType (x, a, c), FunctionType (y, b, d) ->
      let d = Refinement.computation_subst (Map.singleton (module String) y (Term.TmVar x)) d in
      subtype_value ctx b a @ subtype_computation (RefinementContext.add ctx y b) c d
  | FType a, FType b -> subtype_value ctx a b
  | _, _ -> failwith "mismatch of underlying types"

let rec refinement_template_value ?(default_name = "v") ctx =
  let open Logic in
  function
    | Type.UnitType ->
        let vars, _ = RefinementContext.erase_purify ctx |> List.unzip in
        let dummy = Utils.mk_fresh_name default_name (Set.of_list (module String) vars) in
        let args = List.map vars ~f:(fun x -> Term.TmVar x) in
        RefinedUnitType (dummy, Formula.PVar (mk_fresh_pvar (), args))
    | Type.IntType ->
        let vars, _ = RefinementContext.erase_purify ctx |> List.unzip in
        let x = Utils.mk_fresh_name default_name (Set.of_list (module String) vars) in
        let args = List.map (x :: vars) ~f:(fun x -> Term.TmVar x) in
        RefinedIntType (x, Formula.PVar (mk_fresh_pvar (), args))
    | Type.SumType (a, b) -> Refinement.SumType (refinement_template_value ctx a, refinement_template_value ctx b)
    | Type.PairType (a, b) ->
        let x = Utils.mk_fresh_name "x" (Set.of_list (module String) (RefinementContext.vars ctx)) in
        let a' = refinement_template_value ~default_name:x ctx a in
        let b' = refinement_template_value (RefinementContext.add ctx x a') b in
        PairType (x, a', b')
    | Type.UType c -> UType (refinement_template_computation ctx c)
    | Type.ValTyVar _ -> failwith "type variables are not allowed"
  and refinement_template_computation ctx = function
    | Type.FunctionType (a, c) ->
        let x = Utils.mk_fresh_name "x" (Set.of_list (module String) (RefinementContext.vars ctx)) in
        let a' = refinement_template_value ~default_name:x ctx a in
        let c' = refinement_template_computation (RefinementContext.add ctx x a') c in
        FunctionType (x, a', c')
    | Type.FType a -> FType (refinement_template_value ctx a)
    | Type.CompTyVar _ -> failwith "type variables are not allowed"

let refinement_type_of_operation args body_type =
  UType (List.fold_right args ~f:(fun (var, ty) body -> FunctionType (var, ty, body)) ~init:(FType body_type))

let refinement_type_of_const = function
  | Term.Int n -> 
      let x = mk_fresh_term_var () in
      RefinedIntType (x, Logic.(Formula.Equal (Term.TmVar x, Term.Operation (Term.Int n, []))))
  | Term.Add ->
      let x = mk_fresh_term_var () in
      let y = mk_fresh_term_var () in
      let z = mk_fresh_term_var () in
      refinement_type_of_operation [(x, RefinedIntType (x, Logic.Formula.True)); (y, RefinedIntType (y, Logic.Formula.True))] (RefinedIntType (z, Logic.(Formula.Equal (TmVar z, Operation (Add, [TmVar x; TmVar y])))))

(* constraints = context & predicate in the context *)
let rec value_verification_condition ctx = function
  | Term.Unit -> ([], RefinedUnitType (mk_fresh_term_var (), True))
  | Term.Const c -> ([], refinement_type_of_const c)
  | Term.TmVar x ->
      (match RefinementContext.find ctx x with
      | Some (RefinedUnitType (v, _)) ->
          let v = Utils.mk_fresh_name x (Set.of_list (module String) (RefinementContext.vars ctx)) in
          ([], RefinedUnitType (v, True))
      | Some (RefinedIntType (v, _)) ->
          let v = Utils.mk_fresh_name x (Set.of_list (module String) (RefinementContext.vars ctx)) in
          ([], RefinedIntType (v, Logic.(Equal (Term.TmVar v, Term.TmVar x))))
      | Some a -> ([], a)
      | _ -> failwith "variable not found in context")
  | Term.Pair (v, w) ->
      let constraints_v, a = value_verification_condition ctx v in
      let x = mk_fresh_term_var () in
      let constraints_w, b = value_verification_condition (RefinementContext.add ctx x a) w in
      constraints_v @ constraints_w, PairType (x, a, b)
  | Term.Inl (v, b) ->
      let constraints, a = value_verification_condition ctx v in
      let b = refinement_template_value ctx b in
      constraints, SumType (a, b)
  | Term.Inr (v, a) ->
      let constraints, b = value_verification_condition ctx v in
      let a = refinement_template_value ctx a in
      constraints, SumType (a, b)
  | Term.Thunk c ->
      let constraints, ty = computation_verification_condition ctx c in
      constraints, UType ty
and computation_verification_condition ctx = function
  | Term.Return v ->
      let c, ty = value_verification_condition ctx v in
      c, Refinement.FType ty
  | Term.Lambda (x, a, m) ->
      let a' = refinement_template_value ~default_name:x ctx a in
      let constraints, ty = computation_verification_condition (RefinementContext.add ctx x a') m in
       constraints, Refinement.FunctionType (x, a', ty)
  | Term.App (m, v, _) ->
      let constraints_m, tym = computation_verification_condition ctx m in
      let constraints_v, tyv = value_verification_condition ctx v in
      (match tym with
        | Refinement.FunctionType (x, a, c) ->
            let constraints_sub = subtype_value ctx tyv a in
            constraints_m @ constraints_v @ constraints_sub, computation_subst (Map.singleton (module String) x (Logic.Term.of_pure_cbpv_term v)) c
        | _ -> failwith "illegal application")
  | Term.Force (v, _) ->
      let constraints, ty = value_verification_condition ctx v in
      (match ty with
        | Refinement.UType c -> constraints, c
        | _ -> failwith "type mismatch")
  | Term.PatternMatch (v, x, _, y, _, m) ->
      let constraints_v, tyv = value_verification_condition ctx v in
      (match tyv with
      | Refinement.PairType (x', a, b) ->
          let b = Refinement.value_subst (Map.singleton (module String) x' (Logic.Term.TmVar x)) b in
          let constraints_m, tym = computation_verification_condition (RefinementContext.add (RefinementContext.add ctx x a) y b) m in
          constraints_v @ constraints_m, tym
      | _ -> failwith "type mismatch")
  | Term.SeqComp (m, x, _, n) ->
      let constraints_m, tym = computation_verification_condition ctx m in
      (match tym with
      | Refinement.FType a ->
          let constraints_n, tyn = computation_verification_condition (RefinementContext.add ctx x a) n in
          constraints_m @ constraints_n, tyn
      | _ -> failwith "type mismatch")
  | Term.Case (v, x, _, m, y, _, n) ->
      let constraints_v, tyv = value_verification_condition ctx v in
      (match tyv with
      | Refinement.SumType (a, b) ->
          let constraints_m, tym = computation_verification_condition (RefinementContext.add ctx x a) m in
          let constraints_n, tyn = computation_verification_condition (RefinementContext.add ctx y b) n in
          let underlying_type = computation_erasure tym in
          (* assert (computation_erasure tym = computation_erasure tyn); (*todo: equality up to alpha conversion*) *)
          let ty = refinement_template_computation ctx underlying_type in
          let constraints_sub_m = subtype_computation (RefinementContext.add ctx x a) tym ty in
          let constraints_sub_n = subtype_computation (RefinementContext.add ctx y b) tyn ty in
          constraints_m @ constraints_n @ constraints_sub_m @ constraints_sub_n, ty
      | _ -> failwith "type mismatch")
  | Fix (x, c, m) ->
      let c' = refinement_template_computation ctx c in
      let constraints, ty = computation_verification_condition (RefinementContext.add ctx x (Refinement.UType c')) m in
      let constraints_sub = subtype_computation ctx ty c' in
      constraints @ constraints_sub, c'


