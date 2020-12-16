open Core
open Syntax
open Unification
open HindleyMilner
open Translate
open Infer

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
  let used = List.map ~f:(fun (x, _) -> x) ctx |> Set.of_list (module String) in
  let t' = Term.computation_elim_shadow ~used (Translate.cbv_term used t) (*|> Term.computation_simplify*) in
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
        let a' = refinement_template_value ~default_name:x ctx a in
        (x, a') :: ctx_template ((x, a')::ctx) ctx' in
  let rctx = ctx_template [] ctx in
  let c, ty = computation_verification_condition rctx t'' in
  rctx, t'', ty, c

let _ =
  let ctx = Lambda.Type.([("x", Int); ("f", Function (Var "a", Var "b"))]) in
  let t = Lambda.Term.(App (App (Const Add, Const (Int 1)), App (Var "f", Var "x"))) in
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
