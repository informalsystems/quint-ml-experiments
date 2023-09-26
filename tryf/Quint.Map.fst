module Quint.Map

open FStar.Order
open Quint.Ordered
open Quint.Show
module List = FStar.List.Tot

module Set = Quint.Set
let set #a {| ordered a |} (l: list a) = Set.set l

type entry k_t v_t = | E : k:k_t -> v:v_t -> entry k_t v_t

instance ordered_entry #k #v {| ordered k |} : ordered (entry k v) = {
  compare = (fun x y -> compare x.k y.k)
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
  = fun key value m -> Set.add (E key value) m

let get
  #k #v {| ordered k |}
  : k -> t k v -> option v
  = fun key (Set.Set s) ->
    match FStar.List.Tot.find (fun x -> compare x.k key = Eq) s with
    | Some y -> Some y.v
    | None -> None

let v
  #k #v {| ordered k|}
  (l:list (k * v))
  : t k v
  = Set.set (List.map (fun (k, v) -> E k v) l)

let to_list #k #v
  (m:t k v)
  : list (k * v)
  = List.map (fun x -> (x.k, x.v)) m.ls

let _ex_v = assert_norm (
  compare
    (to_list (v [(0, 0), "0,0"; (0, 1), "0,1"; (0, 2), "0,2"]))
    [(0, 0), "0,0"; (0, 1), "0,1"; (0, 2), "0,2"]
  = Eq
)

let _ex_get = assert_norm (
  get (0, 1) (v [(0, 0), "0,0"; (0, 1), "0,1"; (0, 2), "0,2"])
  =
  Some "0,1"
)

let string_of_map #k #v {|show k|} {|show v|} (m:t k v): string =
  let rec aux = function
    | [] -> ")"
    | (k', v') :: xs ->
      to_string k' ^ " -> " ^ to_string v' ^ ", " ^ aux xs
  in
  "Map(" ^ aux (to_list m)

instance show_map #k #v {|show k|} {|show v|} : show (t k v) = {
  to_string = string_of_map
}
