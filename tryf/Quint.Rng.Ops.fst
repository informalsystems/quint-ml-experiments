module Quint.Rng.Ops

open Quint.Rng.Internal

module List = FStar.List.Tot

let return #a (x:a): t a = fun s -> (x, s)

let (>>=) #a #b (rng:t a) (f: a -> t b): t b =
  fun s ->
    let r, s' = rng s in
    f r s'

let (let?) #a #b (rng:t a) (f: a -> b): t b=
  fun s ->
    let r, s' = rng s in
    return (f r) s'

let (and?) #a #b (r1:t a) (r2: t b): t (a & b) =
  fun s ->
    let x1, s' = r1 s in
    let x2, s'' = r2 s' in
    return (x1, x2) s''
