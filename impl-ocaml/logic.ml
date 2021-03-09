open Core
open Syntax
open Utils

module Term = struct
  type op =
    | Int of int
    | Add
  type t =
    | TmVar of string
    | Unit
    | Pair of t * t
    | Inl of t
    | Inr of t
    | Operation of op * t list
  let rec subst map = function
    | TmVar x -> (match Map.find map x with Some tm -> tm | None -> TmVar x)
    | Unit -> Unit
    | Pair (t1, t2) -> Pair (subst map t1, subst map t2)
    | Inl t -> Inl (subst map t)
    | Inr t -> Inr (subst map t)
    | Operation (o, args) -> Operation (o, List.map ~f:(subst map) args)
  let of_const = function
    | Syntax.Term.Int n -> Operation (Int n, [])
    | Add
    | Leq -> failwith "impure"
  let rec of_pure_cbpv_term = function
    | Syntax.Term.TmVar x -> TmVar x
    | Unit -> Unit
    | Pair (v, w) -> Pair (of_pure_cbpv_term v, of_pure_cbpv_term w)
    | Inl (v, _) -> Inl (of_pure_cbpv_term v)
    | Inr (v, _) -> Inr (of_pure_cbpv_term v)
    | Const c -> of_const c
    | Thunk _ -> failwith "impure"

  let operation_to_string op args =
    match op, args with
    | Int n, [] -> 100, string_of_int n
    | Int _, _ -> failwith "invalid arguments"
    | Add, [x; y] -> 20, add_paren_if_needed 20 x ^ " + " ^ add_paren_if_needed 20 y
    | Add, _ -> failwith "invalid arguments"

  let rec to_string' = function
    | TmVar x -> 100, x
    | Unit -> 100, ""
    | Pair (t1, t2) ->
        let _, s1 = to_string' t1 in
        let _, s2 = to_string' t2 in
        100, Printf.sprintf "(%s, %s)" s1 s2
    | Inl t -> 10, "Inl " ^ add_paren_if_needed 10 (to_string' t)
    | Inr t -> 10, "Inr " ^ add_paren_if_needed 10 (to_string' t)
    | Operation (op, args) -> operation_to_string op (List.map ~f:to_string' args)
  let to_string t = let _, s = to_string' t in s
end

let pvar_counter = ref 0
let inc_counter c =
  let n = !c in
  c := n + 1;
  n
let mk_fresh_pvar () = "#pvar" ^ string_of_int (inc_counter pvar_counter)

module Formula = struct
  type t =
    | PVar of string * Term.t list
    | True
    | False
    | Equal of Term.t * Term.t
    | Leq of Term.t * Term.t
    | And of t list
    | Or of t list
    | Implies of t * t

  let rec subst_term map = function
    | PVar (p, args) -> PVar (p, List.map ~f:(Term.subst map) args)
    | True -> True
    | False -> False
    | Equal (v1, v2) -> Equal (Term.subst map v1, Term.subst map v2)
    | Leq (v1, v2) -> Leq (Term.subst map v1, Term.subst map v2)
    | And fmls -> And (List.map ~f:(subst_term map) fmls)
    | Or fmls -> Or (List.map ~f:(subst_term map) fmls)
    | Implies (p, q) -> Implies (subst_term map p, subst_term map q)

  (* t[y/x] *)
  let rename_term_var x y t = subst_term (Map.singleton (module String) x (Term.TmVar y)) t

  let rec to_string' = function
    | PVar (p, args) -> 100, Printf.sprintf "%s(%s)" p (List.map ~f:Term.to_string args |> String.concat ~sep:", ")
    | True -> 100, "true"
    | False -> 100, "false"
    | Equal (x, y) -> 100, Term.to_string x ^ " = " ^ Term.to_string y
    | Leq (x, y) -> 100, Term.to_string x ^ " <= " ^ Term.to_string y
    | And fmls -> 30, List.map ~f:(fun f -> to_string' f |> Utils.add_paren_if_needed 30) fmls |> String.concat ~sep:" /\\ "
    | Or fmls -> 20, List.map ~f:(fun f -> to_string' f |> Utils.add_paren_if_needed 20) fmls |> String.concat ~sep:" \\/ "
    | Implies (p, q) -> 10, (to_string' p |> add_paren_if_needed 10) ^ " => " ^ (to_string' q |> add_paren_if_needed 10)
  let to_string f = let _, s = to_string' f in s
end


