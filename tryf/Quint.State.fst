
module Quint.State

open Quint.Util

module DM = FStar.DependentMap

//// START dep map try
noeq
type sig =
  { vars: eqtype
  ; vals: vars -> Type
  }

let state (s:sig) = DM.t s.vars s.vals

type var =
  | V
  | X

let var_type : var -> Type = function
  | V -> int
  | X -> string

let optional : (var -> Type) -> var -> Type =
  fun f v -> option (f v)

let s = state {vars = var; vals = optional var_type}

let init_t : Type = v:var -> var_type v

let init : init_t = function
  | V -> 0
  | X -> "foo"

let init_opt: f:(v:var -> var_type v) -> v':var -> option (var_type v') =
  fun init variable -> Some (init variable)

let is_fresh (m:s) = forall k. None? (DM.sel m k)
let is_updated (m:s) = forall k. Some? (DM.sel m k)

let upd (v:var) (x:var_type v)
  : m:s{None? (DM.sel m v)} -> m':s{Some? (DM.sel m' v)} =
  fun m -> DM.upd m v (Some x)


let initial_state (f:init_t) : s = DM.create (init_opt f)
let empty_state : m:s{is_fresh m} =
  let clear _ = None in
  DM.create (clear)

// Trying to update the same variable twice fails
[@@expect_failure [54]]
let _ex_cannot_update_twice = (~(upd V 1 empty_state |> upd V 10))

let _ex_is_updated_empty = assert_norm (~(is_updated empty_state))
let _ex_is_updated_partial = assert_norm (~(is_updated (empty_state |> upd V 1)))
let _ex_is_updated = assert_norm (is_updated ( upd V 1  empty_state |> upd X "foo" ))

let m = initial_state init
let init_ex = assert (is_updated m)
let v_ex = assert_norm (DM.sel m V = Some 0)
let x_ex = assert_norm (DM.sel m X = Some "foo")
//// END dep map try

// TODO: Add a boolean to state, indicating whether the action was enabled,
// TODO: State is actual relating this state and next state, updates go to next state, reads from this state
type time a =
  { trace: list a
  ; t0 : a
  ; t1 : option a
  }

let st s c = time s -> c & time s

let now #s : st s s
  = fun time -> time.t0, time

let update #a (u:a -> a) : st a unit
  = fun t -> (), {t with t1 = Some (u t.t0)}

let bind
  #s #a #b
  (f: st s a) (g: a -> st s b)
  = fun s0 ->
    let x, s1 = f s0 in
    g x s1

let return #s #c (x:c)
  : st s c
  = fun t -> x, t

let (let!) = bind

type s = {a : int; b : string}

let _ex_computation : st s bool =
  let! t = now in
  let! () = update (fun s -> {s with a = s.a + 1}) in
  return true

let _ex_eval = _ex_computation {trace = []; t0 = {a = 0; b = "foo"}; t1 = None}
