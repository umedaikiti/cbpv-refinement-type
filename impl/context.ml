open Core

module ListContext (Type : sig type t end) = struct
  type t = (string * Type.t) list
  let add ctx x a = (x, a) :: ctx
  let find ctx x =
    List.find_map ctx ~f:(fun (x', a) -> if String.(x = x') then Some a else None)
end

module MapContext (Type : sig type t end) = struct
  type t = (string, Type.t, String.comparator_witness) Map.t
  let add ctx x a = Map.update ctx x ~f:(fun _ -> a)
  let find = Map.find
end
