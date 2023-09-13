module Quint.Rng.Internal

open FStar.Mul
module List = FStar.List.Tot

// An RNG adapted from https://raw.githubusercontent.com/informalsystems/quint/main/quint/src/rng.ts
// with all the shortcomings and basis of that impl

type rng_state = | Rn : v:int -> rng_state

// TODO, add a method to access the rng_state?
type t a = rng_state -> a & rng_state

let u32 = 0x100000000
let u64 = 0x10000000000000000

let key = 0xfb9e125878fa6cb3

let squares64 (s:rng_state): nat =
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


let incr_state (s : rng_state) : rng_state = Rn ((s.v + 1) % u64)

let rec rand_aux (s : rng_state) (input:nat{input > 0}) (output base:int)
  : Tot (int & rng_state)
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
    let rng_state' = incr_state s in
    output', rng_state'
