
module Quint.Ordered

open FStar.Order

class ordered (a:Type) = {
  compare : a -> a -> order;
  // [@@@TC.no_method]
  // properties : unit -> Lemma (is_total compare)
}

instance ordered_int : ordered int = {
  compare = compare_int;
  // properties = fun () -> ()
}

instance ordered_nat : ordered nat = {
  compare = compare_int
}

let rec compare_lists #a {| ordered a |} : list a -> list a -> order =
  fun xs ys ->
  match xs, ys with
  | [], [] -> Eq
  | _::_, [] -> Gt
  | [], _::_ -> Lt
  | x::xs', y::ys' ->
    match compare x y with
    | Eq -> compare_lists  xs' ys'
    | Lt -> Lt
    | Gt -> Gt


instance ordered_list (#a:Type) (o:ordered a) : ordered (list a) = {
  compare = compare_lists;
}

let compare_pair
  #a #b {| ordered a |} {| ordered b |}
  : (a * b) -> (a * b) -> order
  = fun (a1, b1) (a2, b2) ->
  match compare a1 a2 with
  | Eq -> compare b1 b2
  | cmp -> cmp

let _compare_pairs_ex =
  assert (compare_pair (0, 0) (0, 1) = Lt);
  assert (compare_pair (0, 1) (1, 0) = Lt);
  assert (compare_pair (1, 0) (0, 2) = Gt);
  assert (compare_pair (1, 2) (1, 2) = Eq)


instance ordered_pair #a #b {| ordered a |} {| ordered b |} : ordered (a * b) = {
  compare = compare_pair
}
