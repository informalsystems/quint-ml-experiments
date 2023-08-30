module Term

open Quint.Set
open Quint.Map

let ( |> ) x f = f x

type typ  =
  | Int : typ
  | Str : typ
  | Set : typ     -> typ
  | Map : k:typ   -> v:typ   -> typ
  | Opr : src:typ -> tgt:typ -> typ

let rec denote_type
  : typ -> Type = function
  | Int -> int
  | Str -> string
  | Set t       -> set_t (denote_type t)
  | Map k v     -> map (denote_type k) (denote_type v)
  | Opr src tgt -> (denote_type src) -> (denote_type tgt)

// TODO: How to enforce that operators cannot be values? Or do we just allow it?

  // | Opr a b -> (denote_type a) -> (denote_type b)
// let () = FStar.IO.
