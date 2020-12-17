open Core
open Syntax
open Unification
open HindleyMilner
open Translate
open Infer

let context_to_string type_to_string ctx =
  List.map ~f:(fun (x, a) -> x ^ " : " ^ type_to_string a) ctx
  |> String.concat ~sep:", "

let cbv_translate ctx t =
  let used = List.map ~f:(fun (x, _) -> x) ctx |> Set.of_list (module String) in
  let t' = Term.computation_elim_shadow ~used (Translate.cbv_term used t |> Term.computation_simplify) in
  let ctx = List.map ~f:(fun (x, a) -> x, Translate.cbv_type a) ctx in
  print_endline "CBV translation:";
  print_endline (context_to_string Type.value_to_string ctx ^ " |- " ^ Term.computation_to_string t' ^ " : ?");
  ctx, t'

let hm_infer ctx t =
  let m, ty = computation_infer (Map.of_alist_exn (module String) ctx) t in
  let t' = Term.computation_subst_type m t in
  let ctx = List.map ~f:(fun (x, a) -> x, Type.Substitution.value_subst m a) ctx in
  print_endline "HM inference:";
  print_endline (context_to_string Type.value_to_string ctx ^ " |- " ^ Term.computation_to_string t' ^ " : " ^ Type.computation_to_string (Type.Substitution.computation_subst m ty));
  ctx, t', ty

let refinement_infer ctx t =
  let rec ctx_template ctx = function
    | [] -> []
    | (x, a)::ctx' ->
        let a' = refinement_template_value ~default_name:x ctx a in
        (x, a') :: ctx_template ((x, a')::ctx) ctx' in
  let rctx = ctx_template [] ctx in
  let c, ty = computation_verification_condition rctx t in
  print_endline "Result:";
  print_endline (context_to_string Refinement.value_to_string rctx ^ " |- " ^ Term.computation_to_string t ^ " : " ^ Refinement.computation_to_string ty);
  print_endline "Constraints:";
  List.iter c ~f:(fun (ctx, fml) -> print_endline (context_to_string Type.value_to_string ctx ^ " |- " ^ Logic.Formula.to_string fml));
  rctx, ty, c

let _ =
  let ctx = Lambda.Type.([("x", Int); ("f", Function (Var "a", Var "b"))]) in
  let t = Lambda.Term.(App (App (Const Add, Const (Int 1)), App (Var "f", Var "x"))) in
  let ctx, t = cbv_translate ctx t in
  let ctx, t, _ = hm_infer ctx t in
  let _ = refinement_infer ctx t in
  let ctx = [("x", Type.ValTyVar "a")] in
  let term = Term.(SeqComp(GenOp (Nondet, Unit), "y", Type.ValTyVar "b", Case (TmVar "y", "z", Type.ValTyVar "c", Return (Const (Int 0)), "z", Type.ValTyVar "d", Return (TmVar "x")))) in
  let ctx, t, _ = hm_infer ctx term in
  let _ = refinement_infer ctx t in
  let ctx = Lambda.Type.([("x", Int)]) in
  let t = Lambda.Term.(Case (App (App (Const Leq, Const (Int 0)), Var "x"), "y", Var "x", "y", Const (Int 0))) in
  let ctx, t = cbv_translate ctx t in
  let ctx, t, _ = hm_infer ctx t in
  let _ = refinement_infer ctx t in
  ()
