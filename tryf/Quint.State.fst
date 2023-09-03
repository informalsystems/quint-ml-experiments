

module Quint.State

open Quint.Util

module DM = FStar.DependentMap
module List = FStar.List.Tot
open List

class sig = {
   /// `vars` is the set of "flexible variables"
   vars:eqtype;
   /// `types` maps each variable to the types of the values it can be assigned
   types: vars -> Type
}

let optional #k : (k -> Type) -> k -> Type =
  fun f v -> option (f v)


let state {| sig |} = DM.t vars (optional types)

let is_assigned {| sig |} (m:state) k = Some? (DM.sel m k)
let is_unassigned {| sig |} (m:state) k = None? (DM.sel m k)

let is_fresh {| sig |} (m:state) = forall k. is_unassigned m k

let is_updated {| sig |} (m:state) = forall k. is_assigned m k

let init_opt {| sig |}: f:(v:vars -> types v) -> v':vars -> option (types v') =
  fun init variable -> Some (init variable)

type init_t {| sig |} = v:vars -> types v

let init (s:sig) (f:init_t) : state = DM.create (init_opt f)

let empty_state {| sig |} : m:state{is_fresh m} =
  let clear _ = None in
  DM.create (clear)

let upd {| sig |} (v:vars) (x:types v)
  : m:state{is_unassigned m v} -> m':state{is_assigned m' v} =
  fun m -> DM.upd m v (Some x)

// let ( := ) {|sig|} = upd

let transition {| sig |} = s0:state{is_updated s0} -> s1:state{is_updated s1}

// START State Example
type ex_var = | V | X
instance ex_sig : sig = {
  vars = ex_var;
  types = function
    | V -> int
    | X -> string
}

// Trying to update the same variable twice fails
[@@expect_failure [54]]
let _ex_cannot_update_twice = (~(upd V 1 empty_state |> upd V 10))

let _ex_is_updated_empty = assert_norm (~(is_updated (empty_state)))
let _ex_is_updated_partial = assert_norm (~(is_updated (empty_state |> upd V 1)))
let _ex_is_updated = assert_norm (is_updated ( upd V 1  empty_state |> upd X "foo" ))

let _s = init ex_sig (function
  | V -> 0
  | X -> "foo")

let _ex_init = assert_norm (is_updated _s)
let _ex_v = assert_norm (DM.sel _s V = Some 0)
let _ex_x = assert_norm (DM.sel _s X = Some "foo")

// let _ex_acess_state = assert_norm (V@_s = 0 && X@_s = "foo")
// let _ex_set_state : state =
//     (V := 5) empty_state |> (X := "fee")
// END State Example

// TODO Use `DM.restrict` to limit map to just declared variables
// A computation of `a` that can read from `state #sig`

let state_has {|sig|} (s:state) (vs:list vars) =
    forall v. mem v vs ==> is_assigned s v

let state_not_has {|sig|} (s:state) (vs:list vars) =
    forall v. mem v vs ==> is_unassigned s v

// Copied from  https://github.com/shonfeder/FStar/tree/fd0f8db6e8e254a51f0c872067004cd83d3a1f5e/ulib/FStar.List.Tot.Properties.fst
// which has the SMTPat commented out
val append_mem: #t:eqtype ->  l1:list t
              -> l2:list t
              -> a:t
              -> Lemma (requires True)
                       (ensures (mem a (l1@l2) = (mem a l1 || mem a l2)))
                       [SMTPat (mem a (l1@l2))]
let rec append_mem #t l1 l2 a = match l1 with
  | [] -> ()
  | hd::tl -> append_mem tl l2 a

let state_concat_has_both {|sig|} (vs vs': list vars) (s:state{state_has s (vs @ vs')})
    : Lemma (state_has s vs /\ state_has s vs')
    = ()

let state_concat_is_concat_ls {|sig|} (vss vs vs': list vars) (s:state)
    : Lemma (vss == vs @ vs' ==> state_has s vss == state_has s (vs @ vs'))
    = ()

// let rec state_concat_has_both {|sig|}
//  (vs vs':list vars) (s:state)
//  : Lemma (state_has s (vs @ vs') ==> state_has s vs /\ state_has s vs')
//  = match vs with
//  | [] -> List.append_nil_l vs'; assert (state_has s vs')
//  | x :: xs -> assert (is_assigned s x); state_concat_has_both xs vs'

// let state_has_both {|sig|} (s:state) vs vs' =
//  state_has s vs && state_has s vs'

/// the type of computations that
///
/// - read from a state with signature `sig`
/// - read the variables in `vs` (so all `v` in `vs` must be assigned)
/// - produces a vlue of type `a`
type read {|sig|} (vs:list vars) (a:Type)
  = s:state{state_has s vs} -> a

let read_map {|sig|} #a #b #vs (f:a -> b) (x:read vs a) : read vs b
  = fun s -> f (x s)

let return {|sig|} #a (x:a) : read [] a = fun _ -> x

let (let@) {|sig|} #a #b #vs
  (x : read vs a) (f : a -> read vs b) : read vs b
  = fun s -> f (x s) s

let (and@) {|sig|} #a #b #vs #vs'
  (x : read vs a) (y : read vs' b) : read (vs @ vs') (a * b)
  = fun s -> (x s, y s)

let ( ! ) {| sig |} (v:vars) : read [v] (types v) // s:state{is_assigned s v} -> types v
    =
    fun state -> Some?.v (DM.sel state v)

let read_ex : read [X; V] (int * string) =
    let@ x = !V
    and@ v = !X
    in
    return (x, v)

type action_vars {|sig|} = {
  updated : list vars;
  updates : list vars;
  not_updated : list vars;
  }

/// A state predicate, i.e., an action
///
/// - `s0` is the current state
/// - `s` is the intermediate state to be updated (lets us ensure no state is updated twice)
/// - `s1` is the next state specified by by the action
type action_t {|sig|} (vs:list vars)
  = s0:state{is_updated s0}
    -> option (
      s:state{state_not_has s vs}
      -> s1:state{state_has s1 vs /\ (forall v. (not (mem v vs)) ==> DM.sel s1 v == DM.sel s v)}
    )

// /// A state predicate, i.e., an action
// ///
// /// - `s0` is the current state
// /// - `s` is the intermediate state to be updated (lets us ensure no state is updated twice)
// /// - `s1` is the next state specified by by the action
// type action_t {|sig|} (vs:action_vars)
//   = s0:state -> option (s:state{state_has s vs.updated /\ state_not_has s (vs.updates @ vs.not_updated)} -> s1:state{state_has s1 (vs.updated @ vs.updates) /\ state_not_has s1 vs.not_updated})

// let upd' {| sig |} (v:vars) (x:types v) updated not_updated
//   : s:state{state_has s updated /\ state_not_has s ([v] @ not_updated)} -> s':state{state_has s ([v] @ updated) /\ state_not_has s not_updated} =
//   fun m -> DM.upd m v (Some x)

let ( @= ) {|sig|} (v:vars) (x:types v) : action_t [v]
  = fun _ -> Some (fun s -> upd v x s)

/// Conjunction is the composition of actions
let ( &! ) {|sig|} #vs #vs'
  (a1:action_t vs)
  (a2:action_t vs'{forall v. mem v vs' ==> not (mem v vs)}) // a2 cannot update the same vars as a1
  : action_t (vs @ vs') // ther
  =
  fun s0 ->
  match a1 s0 with
  | None -> None
  | Some upd1 ->
  match a2 s0 with
  | None -> None
  | Some upd2 ->
  Some (fun (s:state{state_not_has s (vs @ vs')}) -> (upd2 (upd1 s)))

// TODO Add non-det
let ( |! ) {|sig|} #vs (a1:action_t vs) (a2:action_t vs) : action_t vs  =
  fun s0 ->
  match a1 s0 with
  | Some upd1 -> Some upd1
  | None ->
  a2 s0

// TODO: need to adjust precedence so don't need to use brackets
let _ex_conj : action_t [V; X] =
  (  V @= 1
  &! X @= "foo"
  )

let _ex_disj : action_t [V] =
  (  V @= 1
  |! V @= 2
  )

let _ex_comb : action_t [V; X] =
  (  V @= 1
  &! X @= "foo"
  )
  |!
  (  V @= 10
  &! X @= "fee"
  )



// let all {|sig|} : action j -> state -> option state =

// Like return, but we don't have values to return
let enact {|sig|} : action = fun s -> [], s

let (let!) {|sig|} #a
  (x: action) (f: action)
  : action
  = fun s ->
    let cs, s' = x s in
    let cs', s'' = f s' in
    (cs @ cs', s'')



// TODO: Add support for _next_ state
// TODO: A monad that will build up a series of constraints (requirements) and a state_update.
// A transition is enabled if all the constraints
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
