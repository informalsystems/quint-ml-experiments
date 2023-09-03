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
// END State Example

// TODO Use `DM.restrict` to limit map to just declared variables
// A computation of `a` that can read from `state #sig`

let state_has {|sig|} (s:state) (vs:list vars) =
    forall v. mem v vs ==> is_assigned s v

let state_not_has {|sig|} (s:state) (vs:list vars) =
    forall v. mem v vs ==> is_unassigned s v

// Copied from  https://github.com/shonfeder/FStar/tree/fd0f8db6e8e254a51f0c872067004cd83d3a1f5e/ulib/FStar.List.Tot.Properties.fst
// which has the SMTPat commented out
// This property is necessary to automate proofs of the equivalence
// `state_has s vs /\ state_has s vs' <==> state_has s (vs * vs')`
val append_mem: #t:eqtype ->  l1:list t
              -> l2:list t
              -> a:t
              -> Lemma (requires True)
                       (ensures (mem a (l1@l2) = (mem a l1 || mem a l2)))
                       [SMTPat (mem a (l1@l2))]
let rec append_mem #t l1 l2 a = match l1 with
  | [] -> ()
  | hd::tl -> append_mem tl l2 a

/// the type of computations that
///
/// - read from a state with signature `sig`
/// - read the variables in `vs` (so all `v` in `vs` must be assigned)
/// - produces a vlue of type `a`
type read {|sig|} (vs:list vars) (a:Type)
  = s:state{state_has s vs} -> a

let read_map {|sig|} #a #b #vs (f:a -> b) (x:read vs a) : read vs b
  = fun s -> f (x s)

let pure {|sig|} #a #vs (x:a) : read vs a = fun _ -> x

// This is what the monadic bindings would look like
// but the read effect is only applicative!
// let (let!) {|sig|} #a #b #vs
//   (x : read vs a) (f : a -> read vs b) : read vs b
//   = fun s -> f (x s) s

// let (and!) {|sig|} #a #b #vs #vs'
//   (x : read vs a) (y : read vs' b) : read (vs @ vs') (a * b)
//   = fun s -> (x s, y s)

let (let!) {|sig|} #a #b #vs
  (x : read vs a) (f : a -> b) : read vs b
  = fun s -> (pure #_ #_ #vs (f (x s))) s

let (and!) {|sig|} #a #b #vs #vs'
  (x : read vs a) (y : read vs' b) : read (vs @ vs') (a * b)
  = fun s -> (x s, y s)

let ( ! ) {| sig |} (v:vars) : read [v] (types v) // s:state{is_assigned s v} -> types v
    =
    fun state -> Some?.v (DM.sel state v)

let _read_ex : read [X; V] (int * string) =
    let! x = !V
    and! v = !X
    in
    (x, v)

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

let req {| sig |} #vs : read vs bool -> action_t [] =
  fun r s0 ->
  if r s0 then Some (fun x -> x) else None


let transition {| sig |} = s0:state{is_updated s0} -> s1:state{is_updated s1}
let update {|sig|} = s:state{is_fresh s} -> s1:state{is_updated s1}

// TODO: need to adjust precedence so don't need to use brackets
let _ex_conj_action : action_t [V; X] =
  (  V @= 1
  &! X @= "foo"
  )

let _ex_disj_action : action_t [V] =
  (  V @= 1
  |! V @= 2
  )

let _ex_comb_action : action_t [V; X] =
  (  V @= 1
  &! X @= "foo"
  )
  |!
  (  V @= 10
  &! X @= "fee"
  )


let _ex_req_action : action_t [V; X] =
  (  req (let! v = !V in v > 1)
  &! V @= 1
  &! X @= "foo"
  )
  |!
  (  req (
      let! v = !V
      and! x = !X
      in
      v < 1 && x = "foo"
     )
  &! V @= 10
  &! X @= "fee"
  )
