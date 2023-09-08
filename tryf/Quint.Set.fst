module Quint.Set

open FStar.Order
open FStar.List.Tot
open Quint.Ordered

// let rec sorted_uniq #a {| ordered a |} : list a -> bool = function
//   | []  -> true
//   | [x] -> true
//   | x :: y :: xs ->
//   match compare x y with
//   | Lt -> sorted_uniq (y :: xs)
//   | _  -> false

let rec sorted
  #a {| ordered a |}
  : list a -> bool = function
  | []  -> true
  | [x] -> true
  | x :: y :: ls ->
  match compare x y with
  | Eq -> false
  | Gt -> false
  | Lt -> sorted (y :: ls)

let rec mem #a {| ordered a |} (e:a)
  : list a  -> bool = function
  | []      -> false
  | x :: xs ->
  match compare e x with
  | Eq -> true
  | _  -> mem e xs

// let rec cons_sorted
//   #a {| ordered a |}
//   : x:a -> l:list a{sorted l} ->
//   Lemma (requires (forall y. mem y l ==> compare x y = Lt))
//         (ensures sorted (x :: l))
//   = fun x -> function
//   | [] -> ()
//   | _ :: xs -> cons_sorted x xs

// let rec merge
//   #a {| ordered a |}
//   : l1:list a -> l2:list a -> list a
//   = fun xs ys ->
//   match xs, ys with
//   | [], ys -> ys
//   | xs, [] -> xs
//   | x :: xs', y :: ys' ->
//   match compare x y with
//   | Eq -> merge xs' ys
//   | Gt -> y :: merge xs ys'
//   | Lt -> x :: merge xs' ys

// TODO: I should be able to reuse the `rev_length` fact from List.Tot, but
// i'm not able to for some reason, so rev is reimplemented here.
// let rec rev_aux
//   #a (l:list a) (acc:list a)
//   : r:list a{length r == length l + length acc}
//   = match l with
//   | [] -> acc
//   | x :: xs -> rev_aux xs (x::acc)

// let rev
//   #a (l:list a)
//   : r:list a{length r == length l}
//   = rev_aux l []

// let rec take_aux
//   #a (c:nat) (n:nat{n >= c}) (l:list a) (acc:list a{length acc == c})
//   : Tot (o:list a{ length o <= n })
//         (decreases l)
//   =
//   if c = n then
//     acc
//   else match l with
//   | [] -> acc
//   | x :: xs -> take_aux (c + 1) n xs (x :: acc)

// let take
//   #a (n:nat) (l:list a)
//   : o:list a{length o <= n}
//   =
//   rev (take_aux 0 n l [])

// let rec drop
//   #a (n:nat) (l:list a{length l >= n})
//   : o:list a{length o == length l - n}
//   = if n = 0 then l else
//     drop (n - 1) (tail l)

// TODO: Prove that length is preserved
// Drops duplicates, the latest found duplicate is preserved
// let rec sort #a {| ordered a |} : l:list a -> Tot (list a) (decreases (length l)) = function
//   | []  -> []
//   | [x] -> [x]
//   | ls  ->
//     let n = length ls / 2 in
//     let xs = take n ls in
//     let ys = drop n ls in
//     let ls' = merge (sort xs) (sort ys) in
//     ls'

let order_to_int : order -> int = function
  | Eq -> 0
  | Lt -> -1
  | Gt -> 1

let rec remove_dups #a {|ordered a|}
  : l:list a
  -> l':list a{length l > 0 ==> length l' > 0} = function
  | [] -> []
  | [x] -> [x]
  | x::y::ls ->
  match compare x y with
  | Eq -> remove_dups (y :: ls)
  | _  -> x :: remove_dups (y :: ls)

let preserves_nonempty #a (l1 l2: list a) = length l1 > 0 ==> length l2 > 0

let sort #a {|ordered a|} : l:list a -> l':list a{preserves_nonempty l l'} =
  fun ls ->
  remove_dups (sortWith (fun a b -> order_to_int (compare a b)) ls)

type t a  = | Set: ls:list a -> t a // TODO {sorted l}
type non_empty a = s:t a{length s.ls > 0}

let compare_sets #a {| ordered a |} (Set s1 : t a) (Set s2 : t a) =
  compare_lists s1 s2

instance ordered_set #a {| ordered a |} : ordered (t a) = {
  compare = compare_sets
}

let set #a {| o:ordered a |} : l:list a -> s:t a{preserves_nonempty l s.ls} =
  fun ls ->
  let ls' = sort ls in
  Set ls'

let empty #a {| o:ordered a |} : t a = set []

let union #a {| ordered a |} (s1 s2: t a) =
  set (append s1.ls s2.ls)

let _sets_ex : t (t int) = set[set[0]; set[1]; set[1;2;3]; union (set[0]) (set[3])]

let add #a {| ordered a |} (x:a) (s:t a) : t a =
  union s (set[x])

let rec range_aux
  :  i:int -> j:int{i <= j}
  -> Tot (list int)
         (decreases j - i)
  = fun i j ->
    if i = j then
    [j]
    else
    i :: range_aux (i + 1) j

let range
  : i:int -> j:int{i <= j} -> t int
  = fun i j ->
  set (range_aux i j)

/// `product s1 s2` is the cartesian product of sets `s1` and `s2`
let product
  #a {| ordered a |}
  (s1 s2 : t a)
  : t (a * a)
  =
  let Set l1, Set l2 = s1, s2 in
  fold_left (fun sets_of_pairs x1 ->
     union
       (set (fold_left (fun pairs x2 -> (x1, x2) :: pairs) [] l2))
       sets_of_pairs
     )
     empty
     l1

let _product_ex =
  let actual = product (range 0 2) (range 2 4) in
  let expected = set [0, 2; 0, 3; 0, 4; 1, 2; 1, 3; 1, 4; 2, 2; 2, 3; 2, 4] in
  assert_norm (compare actual expected = Eq)

let for_all
  #a {| ordered a |}
  (f: a -> bool) (Set s:t a)
  : bool
  =
  for_all f s

let for_some
  #a {| ordered a |}
  (f: a -> bool) (Set s: t a)
  : bool
  = existsb f s

let size
  #a {| ordered a |}
  (Set s: t a)
  : nat
  = length s

let partition
  #a {| ordered a |}
  (f: a -> bool) (Set s: t a)
  : t a * t a
  = let has, has_not = partition f s in
    set has, set has_not
