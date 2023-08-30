module Quint.Map

open FStar.Order
open Quint.Ordered
module Set = Quint.Set
let set #a {| ordered a |} (l: list a) = Set.set l

type entry k v = (k * v)

instance ordered_entry #k #v {| ordered k |} : ordered (entry k v) = {
  compare = (fun (k1, _) (k2, _) -> compare k1 k2)
}

// A map is implemented as an (ordered) set where is equality is defined only by
// the ordering on the key.
type t k v = Set.t (entry k v)

let empty
  #k #v {| ordered k |}
  : t k v
  = set []

let put
  #k #v {|ordered k |}
  : k -> v -> t k v ->  t k v
  = fun key value m -> Set.add (key, value) m

let get
  #k #v {| ordered k |}
  : k -> t k v -> option v
  = fun key (Set.Set s) ->
    match FStar.List.Tot.find (fun (key', _) -> compare key' key = Eq) s with
    | Some (_, v) -> Some v
    | None -> None
