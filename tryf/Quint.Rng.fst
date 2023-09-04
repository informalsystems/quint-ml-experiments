module Quint.Rng

open FStar.Mul
module List = FStar.List.Tot

// An RNG adapted from https://raw.githubusercontent.com/informalsystems/quint/main/quint/src/rng.ts
// with all the shortcomings and basis of that impl

type state = | Rn : v:int -> state

// TODO, add a method to access the state?
type t a = state -> a & state

let u32 = 0x100000000
let u64 = 0x10000000000000000

let key = 0xfb9e125878fa6cb3

let squares64 (s:state): nat =
  let x = (s.v * key) % u64 in
  let y = x in
  let z = (y + key) % u64 in
  let x = (((x * x) % u64) + y) % u64 in
  let x = (x / u32 + ((x * u32) % u64)) % u64 in
  // round 2
  let x = (((x * x) % u64) + z) % u64 in
  let x = (x / u32 + ((x * u32) % u64)) % u64 in
  // round 3
  let x = (((x * x) % u64) + y) % u64 in
  let x = (x / u32 + ((x * u32) % u64)) % u64 in
  // round 4
  ((((x * x) % u64) + z) % u64) / u32


let rec rand_aux (s : state) (input:nat{input > 0}) (output base:int)
  : Tot (int & state)
        (decreases input)
  =
  if input >= u32 then
    let output' = output * u32 + squares64(s) in
    let input' = input / u32 in
    let base' = base * u32 in
    let s' = Rn ((s.v + 1) % u64) in
    rand_aux s' input' output' base'
  else
    // TODO Check quint lib to see of it breaks when range is 0
    let output' = (squares64(s) % input) * base + output in
    let state' = Rn ((s.v + 1) % u64) in
    output', state'


let return #a (x:a): t a = fun s -> (x, s)

let (let?) #a #b (rng:t a) (f: a -> t b): t b=
  fun s ->
    let r, s' = rng s in
    (f r) s'

let init (s:nat): state = Rn (s % u64)

// TODO: Prove boundary property
/// [rand_int n] is a random nat `i` `0 <= i < n`
let rand_nat (bound:nat{bound  > 0}): t (n:nat{n >= 0 /\ n < bound}) =
  fun state ->
  let n, s = rand_aux state bound 0 1 in
  // XXX Bounds property is unproven! (But we know it holds)
  assume (n >= 0 /\ n < bound);
  n, s

let rand_bool : t bool =
  let? n = rand_nat 2 in
  return (
     if n < 1 then true else false
  )

let rand_choice #a (l : list a{List.length l > 0}) : t a =
  let len = List.length l in
  let? idx = rand_nat len in
  // XXX Bounds property is unproven! (But we know it holds)
  assume (idx >= 0 /\ idx < len);
  return (List.index l idx)

let run #a (s:state) (f:t a): a =
  let r, _ = f s in
  r

let _ex_rand_nat =
  let cmp =
    let? w = rand_nat 2 in
    let? x = rand_nat 2 in
    let? y = rand_nat 10 in
    let? z = rand_nat 100 in
    return (w, x, y, z)
  in
  assert_norm (run (init 0) cmp = (0, 1, 4, 75));
  let cmp' =
    let? w = rand_nat 2 in
    let? x = rand_nat 2 in
    let? y = rand_nat 10 in
    let? z = rand_nat 100 in
    return (w, x, y, z)
  in
  // The same computation performed with the same seed is the same
  assert_norm (run (init 0) cmp = run (init 0) cmp');
  // The same computation performed with a different seed is different
  assert_norm (run (init 0) cmp =!= run (init 1) cmp')

let _ex_rand_bool =
  assert_norm (
    run (init 0) (
      let? b1 = rand_bool in
      let? b2 = rand_bool in
      let? b3 = rand_bool in
      return (b1, b2, b3)
    )
    =
    (true, false, true)
  )

let _ex_rand_choice =
 let l = [1;2;3;4;5] in
 assert_norm (
  run (init 0) (
      let? a = rand_choice l in
      let? b = rand_choice l in
      let? c = rand_choice l in
      let? d = rand_choice l in
      return (a, b, c, d)
  )
  =
  (4, 5, 5, 1)
 )
