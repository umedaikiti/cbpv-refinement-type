open Core
open Syntax
open Unification
open HindleyMilner
open Refinement
open Translate

module ListContext = struct
  type 'a t = (string * 'a) list
  let add ctx x a = (x, a) :: ctx
  let find ctx x =
    List.find_map ctx ~f:(fun (x', a) -> if String.(x = x') then Some a else None)
end

let rec erase_purify ctx =
  List.map ctx ~f:(fun (x, a) -> (x, value_erasure a))
  |> List.filter ~f:(fun (x, a) -> Type.is_pure a)

let collect_predicates =
  List.filter_map ~f:(fun (x, a) -> match a with
    | RefinedUnitType (_, p) -> Some p
    | RefinedIntType (_, p) -> Some p
    | _ -> None)

(* ctx |- a <: b *)
let rec subtype_value ctx a b =
  let open Logic in
  match a, b with
  | RefinedUnitType (v, p), RefinedUnitType (u, q) ->
      let q = Formula.rename_term_var u v q in
      [(ListContext.add (erase_purify ctx) v Type.UnitType, Formula.Implies (Formula.And (p :: collect_predicates ctx), q))]
  | RefinedIntType (v, p), RefinedIntType (u, q) ->
      let q = Formula.rename_term_var u v q in
      [(ListContext.add (erase_purify ctx) v Type.IntType, Formula.Implies (Formula.And (p :: collect_predicates ctx), q))]
  | PairType (x, a, b), PairType (y, c, d) ->
      let d = Refinement.value_subst (Map.singleton (module String) y (Term.TmVar x)) d in
      subtype_value ctx a c @ subtype_value (ListContext.add ctx x a) b d
  | SumType (a, b), SumType (c, d) -> subtype_value ctx a c @ subtype_value ctx b d
  | UType c, UType d -> subtype_computation ctx c d
  | _, _ -> failwith "mismatch of underlying types"
and subtype_computation ctx a b =
  let open Logic in
  match a, b with
  | FunctionType (x, a, c), FunctionType (y, b, d) ->
      let d = Refinement.computation_subst (Map.singleton (module String) y (Term.TmVar x)) d in
      subtype_value ctx b a @ subtype_computation (ListContext.add ctx y b) c d
  | FType a, FType b -> subtype_value ctx a b
  | _, _ -> failwith "mismatch of underlying types"

let rec refinement_template_value ctx =
  let open Logic in
  function
    | Type.UnitType ->
        let dummy = mk_fresh_term_var () in
        let vars, _ = erase_purify ctx |> List.unzip in
        let args = List.map vars ~f:(fun x -> Term.TmVar x) in
        RefinedUnitType (dummy, Formula.PVar (mk_fresh_pvar (), args))
    | Type.IntType ->
        let x = mk_fresh_term_var () in
        let vars, _ = erase_purify ctx |> List.unzip in
        let args = List.map (x :: vars) ~f:(fun x -> Term.TmVar x) in
        RefinedIntType (x, Formula.PVar (mk_fresh_pvar (), args))
    | Type.SumType (a, b) -> Refinement.SumType (refinement_template_value ctx a, refinement_template_value ctx b)
    | Type.PairType (a, b) ->
        let a' = refinement_template_value ctx a in
        let x = mk_fresh_term_var () in
        let b' = refinement_template_value (ListContext.add ctx x a') b in
        PairType (x, a', b')
    | Type.UType c -> UType (refinement_template_computation ctx c)
    | Type.ValTyVar _ -> failwith "type variables are not allowed"
  and refinement_template_computation ctx = function
    | Type.FunctionType (a, c) ->
        let x = mk_fresh_term_var () in
        let a' = refinement_template_value ctx a in
        let c' = refinement_template_computation (ListContext.add ctx x a') c in
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
      (match ListContext.find ctx x with
      | Some (RefinedUnitType (v, _)) -> ([], RefinedUnitType (v, True))
      | Some (RefinedIntType (v, _)) -> ([], RefinedIntType (v, Logic.(Equal (Term.TmVar v, Term.TmVar x))))
      | Some a -> ([], a)
      | _ -> failwith "variable not found in context")
  | Term.Pair (v, w) ->
      let constraints_v, a = value_verification_condition ctx v in
      let x = mk_fresh_term_var () in
      let constraints_w, b = value_verification_condition (ListContext.add ctx x a) w in
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
      let a' = refinement_template_value ctx a in
      let constraints, ty = computation_verification_condition (ListContext.add ctx x a') m in
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
          let constraints_m, tym = computation_verification_condition (ListContext.add (ListContext.add ctx x a) y b) m in
          constraints_v @ constraints_m, tym
      | _ -> failwith "type mismatch")
  | Term.SeqComp (m, x, _, n) ->
      let constraints_m, tym = computation_verification_condition ctx m in
      (match tym with
      | Refinement.FType a ->
          let constraints_n, tyn = computation_verification_condition (ListContext.add ctx x a) n in
          constraints_m @ constraints_n, tyn
      | _ -> failwith "type mismatch")
  | Term.Case (v, x, _, m, y, _, n) ->
      let constraints_v, tyv = value_verification_condition ctx v in
      (match tyv with
      | Refinement.SumType (a, b) ->
          let constraints_m, tym = computation_verification_condition (ListContext.add ctx x a) m in
          let constraints_n, tyn = computation_verification_condition (ListContext.add ctx y b) n in
          let underlying_type = computation_erasure tym in
          (* assert (computation_erasure tym = computation_erasure tyn); (*todo: equality up to alpha conversion*) *)
          let ty = refinement_template_computation ctx underlying_type in
          let constraints_sub_m = subtype_computation (ListContext.add ctx x a) tym ty in
          let constraints_sub_n = subtype_computation (ListContext.add ctx y b) tyn ty in
          constraints_m @ constraints_n @ constraints_sub_m @ constraints_sub_n, ty
      | _ -> failwith "type mismatch")
  | Fix (x, c, m) ->
      let c' = refinement_template_computation ctx c in
      let constraints, ty = computation_verification_condition (ListContext.add ctx x (Refinement.UType c')) m in
      let constraints_sub = subtype_computation ctx ty c' in
      constraints @ constraints_sub, c'

let rec simplify_constraint' ctx fml =
  let open Logic in
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
  let open Logic in
  match v, u with
  | Term.Unit, Term.Unit -> []
  | Term.Inl v, Term.Inl u -> simplify_equalities_equal v u
  | Term.Inr v, Term.Inr u -> simplify_equalities_equal v u
  | Term.Pair (v1, v2), Term.Pair (u1, u2) -> simplify_equalities_equal v1 u1 @ simplify_equalities_equal v2 u2
  | _, _ -> [Formula.Equal (v, u)]

let rec simplify_equalities =
  let open Logic in
  function
  | Formula.Equal (v, u) -> Formula.And (simplify_equalities_equal v u)
  | PVar (p, args) -> PVar (p, args)
  | True -> True
  | And l -> And (List.map ~f:simplify_equalities l)
  | Implies (p, q) -> Implies (simplify_equalities p, simplify_equalities q)

let ctx_to_string ctx =
  Map.to_alist ctx
  |> List.map ~f:(fun (x, a) -> x ^ " : " ^ Type.value_to_string a)
  |> String.concat ~sep:", "


let infer_cbv ctx t =
  let context_to_string type_to_string ctx =
    List.map ~f:(fun (x, a) -> x ^ " : " ^ type_to_string a) ctx
    |> String.concat ~sep:", " in
(*  print_endline "Input:";
  print_endline (context_to_string ctx ^ " |- " ^ )*)
  let t' = Translate.cbv_term t |> Term.computation_simplify in
  let ctx = List.map ~f:(fun (x, a) -> x, Translate.cbv_type a) ctx in
  print_endline "CBV translation:";
  print_endline (context_to_string Type.value_to_string ctx ^ " |- " ^ Term.computation_to_string t' ^ " : ?");
  let m, ty = computation_infer (Map.of_alist_exn (module String) ctx) t' in
  let t'' = Term.computation_subst_type m t' in
  let ctx = List.map ~f:(fun (x, a) -> x, Type.Substitution.value_subst m a) ctx in
  print_endline "HM inference:";
  print_endline (context_to_string Type.value_to_string ctx ^ " |- " ^ Term.computation_to_string t'' ^ " : " ^ Type.computation_to_string (Type.Substitution.computation_subst m ty));
  let rec ctx_template ctx = function
    | [] -> []
    | (x, a)::ctx' ->
        let a' = refinement_template_value ctx a in
        (x, a') :: ctx_template ((x, a')::ctx) ctx' in
  let rctx = ctx_template [] ctx in
  let c, ty = computation_verification_condition rctx t'' in
  rctx, t'', ty, c

let _ =
  let open Lambda in
  let ctx = [("x", IntType); ("f", FunctionType (TyVar "a", TyVar "b"))] in
  let t = App (App (Const Add, Const (Int 1)), App (Var "f", Var "x")) in
  let rctx, t, ty, c = infer_cbv ctx t in
  print_endline "Result:";
  print_endline (List.map ~f:(fun (x, a) -> x ^ " : " ^ Refinement.value_to_string a) rctx |> String.concat ~sep:", ");
  print_endline (Term.computation_to_string t);
  print_endline (Refinement.computation_to_string ty);
  print_endline "Constraints:";
  List.iter c ~f:(fun (ctx, fml) ->
    let ctx_s = List.map ~f:(fun (x, a) -> x ^ " : " ^ Type.value_to_string a) ctx |> String.concat ~sep:", " in
    print_endline (ctx_s ^ " |- " ^ Logic.Formula.to_string fml));
  let ctx = Map.of_alist_exn (module String) [("f", Type.ValTyVar "a"); ("x", Type.ValTyVar "b")] in
  let term = Term.App (Term.Force (Term.TmVar "f", Type.CompTyVar "c"), Term.TmVar "x", Type.CompTyVar "d") in
  let m, ty = computation_infer ctx term in
  print_endline (Term.computation_to_string term);
  print_endline (Type.computation_to_string (Type.Substitution.computation_subst m ty));
  print_endline (ctx_to_string (Map.map ~f:(Type.Substitution.value_subst m) ctx))
