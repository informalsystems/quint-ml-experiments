module Quint.Rng

open Quint.Rng.Internal

module List = FStar.List.Tot

open Quint.Rng.Ops

type t = t

let init (s:nat): rng_state = Rn (s % u64)

let incr_state = incr_state

// TODO: Prove boundary property
/// [rand_int n] is a random nat `i` `0 <= i < n`
let rand_nat (bound:nat{bound  > 0}): t (n:nat{n >= 0 /\ n < bound}) =
  fun rng_state ->
  let n, s = rand_aux rng_state bound 0 1 in
  // XXX Bounds property is unproven! (But we know it holds)
  assume (n >= 0 /\ n < bound);
  n, s

let rand_bool : t bool =
  let? n = rand_nat 2 in
  if n < 1 then true else false

let rand_choice #a (l : list a{List.length l > 0}) : t a =
  let len = List.length l in
  let? idx = rand_nat len in
  // XXX Bounds property is unproven! (But we know it holds)
  assume (idx >= 0 /\ idx < len);
  (List.index l idx)

let run #a (n:nat{n >= 0}) (f:t a): a =
  let r, _ = f (init n)  in
  r

let _ex_rand_nat =
  let cmp =
    let? w = rand_nat 2
    and? x = rand_nat 2
    and? y = rand_nat 10
    and? z = rand_nat 100
    in
    (w, x, y, z)
  in
  assert_norm (run 0 cmp = (0, 1, 4, 75));
  let cmp' =
    let? w = rand_nat 2
    and? x = rand_nat 2
    and? y = rand_nat 10
    and? z = rand_nat 100
    in
    (w, x, y, z)
  in
  // The same computation performed with the same seed is the same
  assert_norm (run 0 cmp = run 0 cmp');
  // The same computation performed with a different seed is different
  assert_norm (run 0 cmp =!= run 1 cmp')

let _ex_rand_bool =
  assert_norm (
    run 0 (
      let? b1 = rand_bool
      and? b2 = rand_bool
      and? b3 = rand_bool
      in
      (b1, b2, b3))
    =
    (true, false, true)
  )

let _ex_rand_choice =
  let l = [1;2;3;4;5] in
  assert_norm (
    run 0 (
      let? a = rand_choice l
      and? b = rand_choice l
      and? c = rand_choice l
      and? d = rand_choice l
      in
      (a, b, c, d))
    =
    (4, 5, 5, 1)
  )
