open Core
open Lambda
open Syntax

let rec cbv_type = function
  | Lambda.TyVar x -> Type.ValTyVar x
  | Lambda.IntType -> Type.IntType
  | Lambda.UnitType -> UnitType
  | Lambda.FunctionType (a, b) -> UType (FunctionType (cbv_type a, FType (cbv_type b)))
  | Lambda.SumType (a, b) -> SumType (cbv_type a, cbv_type b)
  | Lambda.PairType (a, b) -> PairType (cbv_type a, cbv_type b)


(* func : a0 -> .. -> an -> F b ==> return_thunk_lambda_app func [(x0, a0); ..; (xn : an)] b : FU(a0 -> ... FU(an -> Fb)) *)
let return_thunk_lambda_app func args body_ty =
  let rec app_repeat args func =
    match args with
    | [] -> func
    | (x, _)::args' ->
        let func' = Term.App (func, Term.TmVar x, List.fold_right args' ~f:(fun (_, b) ty -> Type.FunctionType (b, ty)) ~init:(Type.FType body_ty)) in
        app_repeat args' func' in
  List.fold_right args ~f:(fun (x, ty) body -> Term.Return (Term.Thunk (Term.Lambda (x, ty, body)))) ~init:(app_repeat args func)

let op_cbv_term_default op args ret_ty =
  return_thunk_lambda_app (Term.Force (Term.Const op, List.fold_right args ~f:(fun (_, b) ty -> Type.FunctionType (b, ty)) ~init:(Type.FType ret_ty))) args ret_ty

let op_cbv_term = function
  | Int n -> Term.Return (Term.Const (Term.Int n))
(*  | Add -> Term.Return (Term.Thunk (Term.Lambda ("#x", Type.IntType, Term.Return (Term.Thunk (Term.Lambda ("#y", Type.IntType, Term.App (Term.App(Term.Force (Term.Const Term.Add, Type.(FunctionType (IntType, FunctionType(IntType, FType IntType)))), Term.TmVar "#x", Type.(FunctionType (IntType, FType IntType))), Term.TmVar "#y", Type.FType Type.IntType)))))))*)
(*  | Add -> return_thunk_lambda_app (Term.Force (Term.Const Term.Add, Type.(FunctionType (IntType, FunctionType(IntType, FType IntType))))) [("#x", Type.IntType); ("#y", Type.IntType)] Type.IntType*)
  | Add -> op_cbv_term_default Term.Add [("x", Type.IntType); ("y", Type.IntType)] Type.IntType

let rec cbv_term = function
  | Var x -> Term.Return (Term.TmVar x)
  | Lambda (x, m) -> Term.Return (Term.Thunk (Term.Lambda (x, mk_fresh_value_type_var (), cbv_term m)))
  | App (m, n) ->
      let f = mk_fresh_term_var () in
      let x = mk_fresh_term_var () in
      Term.SeqComp (cbv_term m, f, mk_fresh_value_type_var (), Term.SeqComp (cbv_term n, x, mk_fresh_value_type_var (), Term.App (Term.Force (Term.TmVar f, mk_fresh_computation_type_var ()), Term.TmVar x, mk_fresh_computation_type_var ())))
  | Unit -> Term.Return Term.Unit
  | Const op -> op_cbv_term op
  | Inl m ->
      let x = mk_fresh_term_var () in
      Term.SeqComp (cbv_term m, x, mk_fresh_value_type_var (), Term.Return (Term.Inl (Term.TmVar x, mk_fresh_value_type_var ())))
  | Inr m ->
      let x = mk_fresh_term_var () in
      Term.SeqComp (cbv_term m, x, mk_fresh_value_type_var (), Term.Return (Term.Inr (Term.TmVar x, mk_fresh_value_type_var ())))
  | Case (v, x, m, y, n) ->
      let z = mk_fresh_term_var () in
      Term.SeqComp (cbv_term v, z, mk_fresh_value_type_var (), Term.Case (Term.TmVar z, x, mk_fresh_value_type_var (), cbv_term m, y, mk_fresh_value_type_var (), cbv_term n))
  | Pair (v, w) ->
      let x = mk_fresh_term_var () in
      let y = mk_fresh_term_var () in
      Term.SeqComp (cbv_term v, x, mk_fresh_value_type_var (), Term.SeqComp (cbv_term w, y, mk_fresh_value_type_var (), Term.Return (Term.Pair (Term.TmVar x, Term.TmVar y))))
  | PatternMatch (v, x, y, m) ->
      let z = mk_fresh_term_var () in
      Term.SeqComp (cbv_term v, z, mk_fresh_value_type_var (), Term.PatternMatch (Term.TmVar z, x, mk_fresh_value_type_var (), y, mk_fresh_value_type_var (), cbv_term m))


let op_cbn_term = function
  | Int n -> Term.Return (Term.Const (Term.Int n))
  | Add -> failwith "unimplemented"

let rec cbn_term = function
  | Var x -> Term.Force (Term.TmVar x, mk_fresh_computation_type_var ())
  | Lambda (x, m) -> Term.Lambda (x, mk_fresh_value_type_var (), cbn_term m)
  | App (m, n) -> Term.App (cbn_term m, Term.Thunk (cbn_term n), mk_fresh_computation_type_var ())
  | Const op -> op_cbn_term op
  | Unit -> Term.Return Term.Unit
  | Inl m -> Term.Return (Term.Inl (Term.Thunk (cbn_term m), mk_fresh_value_type_var ()))
  | Inr m -> Term.Return (Term.Inr (Term.Thunk (cbn_term m), mk_fresh_value_type_var ()))
  | Case (v, x, m, y, n) ->
      let z = mk_fresh_term_var () in
      Term.SeqComp (cbn_term v, z, mk_fresh_value_type_var (), Term.Case (Term.TmVar z, x, mk_fresh_value_type_var (), cbn_term m, y, mk_fresh_value_type_var (), cbn_term n))
  | Pair (v, w) -> Term.Return (Term.Pair (Term.Thunk (cbn_term v), Term.Thunk (cbn_term w)))
  | PatternMatch (v, x, y, m) ->
      let z = mk_fresh_term_var () in
      Term.SeqComp (cbn_term v, z, mk_fresh_value_type_var (), Term.PatternMatch (Term.TmVar z, x, mk_fresh_value_type_var (), y, mk_fresh_value_type_var (), cbn_term m))
