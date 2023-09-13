
module Quint.State

open FStar.Tactics.Typeclasses
open FStar.List.Tot

open Quint.Util
open Quint.Ordered
open Quint.Rng.Ops

module DM = FStar.DependentMap
module List = FStar.List.Tot
module Rng = Quint.Rng
module Set = Quint.Set

/// # State

/// State signature
///
/// Defines a state space
class sig = {
   /// `vars` is the set of "flexible variables"
   vars:eqtype;
   /// `types` maps each variable to the types of the values it can be assigned
   types: vars -> Type
}

let optional #k : (k -> Type) -> k -> Type =
  fun f v -> option (f v)

// TODO Find a way to abstract implementation of this so we don't have to expose the
// dep map impl.
/// A state defined by a signature `sig`
let state {| s:sig |} = DM.t vars (optional s.types)

/// Predicates over states
let is_assigned {| sig |} (m:state) k = Some? (DM.sel m k)
let is_unassigned {| sig |} (m:state) k = None? (DM.sel m k)
let is_fresh {| sig |} (m:state) = forall (v:vars). is_unassigned m v
let is_updated {| sig |} (m:state) = forall (v:vars). is_assigned m v

let init_opt {| sig |}: f:(v:vars -> types v) -> v':vars -> option (types v') =
  fun init variable -> Some (init variable)

/// A state initialization function
type init_t {|sig|} = v:vars -> types v

/// Construct a state from an initialization function
val init : sig -> init_t -> s:state{is_updated s}
let init (s:sig) (f:init_t) : state = DM.create (init_opt f)

let empty_state {| sig |} : m:state{is_fresh m} =
  let clear _ = None in
  DM.create (clear)

let upd {| sig |} (v:vars) (x:types v)
  : m:state{is_unassigned m v} -> m':state{is_assigned m' v} =
  fun m -> DM.upd m v (Some x)

// START State Example
type ex_var = | V | U
instance ex_sig : sig = {
  vars = ex_var;
  types = function
    | V -> int
    | U -> string
}

// Trying to update the same variable twice fails
[@@expect_failure [54]]
let _ex_cannot_update_twice = (~(upd V 1 empty_state |> upd V 10))

let _ex_is_updated_empty = assert_norm (~(is_updated (empty_state)))
let _ex_is_updated_partial = assert_norm (~(is_updated (empty_state |> upd V 1)))
let _ex_is_updated = assert_norm (is_updated ( upd V 1  empty_state |> upd U "foo" ))

let _s = init ex_sig (function
  | V -> 0
  | U -> "foo")

let _ex_init = assert_norm (is_updated _s)
let _ex_v = assert_norm (DM.sel _s V = Some 0)
let _ex_x = assert_norm (DM.sel _s U = Some "foo")
// END State Example

// TODO Use `DM.restrict` to limit map to just declared variables
// A computation of `a` that can read from `state #sig`

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

/// # State functions: the *read* effect

// TODO Use `DM.restrict` to limit map to just declared variables
// A computation of `a` that can read from `state #sig`
// TODO Figure out how to hide and abstract these
let state_has {|sig|} (s:state) (vs:list vars) =
    forall v. mem v vs ==> is_assigned s v

let state_not_has {|sig|} (s:state) (vs:list vars) =
    forall v. mem v vs ==> is_unassigned s v

let if_state_has_all_it_is_updated
    {|sig|}
    (s:state)
    (vs:list vars)
    : Lemma ((state_has s vs /\ (forall (v:vars). mem v vs)) ==> is_updated s)
    // [SMTPat (state_has s vs); SMTPat (is_updated s)]
    = ()

/// A computation of a value of type `a`,
/// over a state defined by `sig`
/// that can read from the variables in `list vars`
type read {|sig|} (vs:list vars) (a:Type)
  = s:state{state_has s vs} -> a

let read_map {|sig|} #a #b #vs (f:a -> b) (x:read vs a) : read vs b
  = fun s -> f (x s)

/// Puts a value of type `a` in a `read` context
val pure {|sig|} #a #vs (x:a) : read vs a
let pure {|sig|} #a #vs (x:a) : read vs a = fun _ -> x


// This is what the monadic bindings would look like
// but the read effect is only applicative!
// let (let!) {|sig|} #a #b #vs
//   (x : read vs a) (f : a -> read vs b) : read vs b
//   = fun s -> f (x s) s

// let (and!) {|sig|} #a #b #vs #vs'
//   (x : read vs a) (y : read vs' b) : read (vs @ vs') (a * b)
//   = fun s -> (x s, y s)

/// Read a value of type `types v`
val ( ! ) {| sig |} : v:vars -> read [v] (types v)
let ( ! ) {| sig |} (v:vars) : read [v] (types v) // s:state{is_assigned s v} -> types v
    =
    fun state -> Some?.v (DM.sel state v)

/// Bind a computation of `a` from a read context that computes a `b`
///
/// E.g., if `X` is a state variable
///
/// ```
/// let ex_1 : read [X] int =
///   let! x = !X in
///   x + 1
/// ```
val (let!) {|sig|} #a #b #vs : read vs a -> (a -> b) -> read vs b
let (let!) {|sig|} #a #b #vs
  (x : read vs a) (f : a -> b) : read vs b
  = fun s -> (pure #_ #_ #vs (f (x s))) s

/// Applicative binding of computationr within a read context
///
/// E.g.,
///
/// ```
/// let ex_2 : read [X; V] bool =
///   let! v = !V
///   and! x = !X
///   in
///   v < 1 && x = "foo"
/// ```
val (and!) {|sig|} #a #b #vs #vs' : read vs a -> read vs' b -> read (vs @ vs') (a * b)
let (and!) {|sig|} #a #b #vs #vs'
  (x : read vs a) (y : read vs' b) : read (vs @ vs') (a * b)
  = fun s -> (x s, y s)

let _read_ex : read [U; V] (int * string) =
    let! x = !V
    and! v = !U
    in
    (x, v)

/// # State predicates: the *action* effect

/// A state predicate, i.e., an action
///
/// An action over the state defined by `sig`
/// that updates the variables `vars`
///
/// - `s0` is the current state
/// - `s` is the intermediate state to be updated (lets us ensure no state is updated twice)
/// - `s1` is the next state specified by by the action
type action {|sig|} (vs:list vars)
  = s0:state{is_updated s0}
    -> option (
      s:state{state_not_has s vs}
      -> s1:state{state_has s1 vs /\ (forall v. (not (mem v vs)) ==> DM.sel s1 v == DM.sel s v)}
    )

// An action that fails
let fail {|sig|} #vs : action vs =
   fun _ -> None

/// Requirements
val req {| sig |} #vs : read vs bool -> action []
let req {| sig |} #vs : read vs bool -> action [] =
  fun r s0 ->
  if r s0 then Some (fun x -> x) else None

let chk {|sig|} (b:bool): action [] =
    fun s0 ->
    if b then
      Some (fun s -> s)
    else
      None

// Turn an action that depends on reading into an action
let ( !@ ) {|sig|} #rs #vs
    (ra : read rs (action vs))
    : action vs
    =
    fun s0 -> ra s0 s0

/// `v @= x` updates the state variable `v` to the value `x` in the next state
val ( @= ) {|sig|} : v:vars -> x:types v -> action [v]
let ( @= ) {|sig|} (v:vars) (x:types v) : action [v]
  = fun _ -> Some (fun s -> upd v x s)

// TODO: replace ! with @ for consistency
/// The composition of actions
val ( &@ ) {|sig|} #vs #vs'
  :  a1:action vs
  -> a2:action vs'{forall v. mem v vs' ==> not (mem v vs)}
  -> action (vs @ vs')
/// Conjunction is the composition of actions
let ( &@ ) {|sig|} #vs #vs'
  (a1:action vs)
  (a2:action vs'{forall v. mem v vs' ==> not (mem v vs)}) // a2 cannot update the same vars as a1
  : action (vs @ vs') // ther
  =
  fun s0 ->
  match a1 s0 with
  | None -> None
  | Some upd1 ->
  match a2 s0 with
  | None -> None
  | Some upd2 ->
  Some (fun (s:state{state_not_has s (vs @ vs')}) -> (upd2 (upd1 s)))

/// The alternation of actions
val ( |@ ) {|sig|} #vs : action vs -> action vs -> action vs
// TODO Add non-det
let ( |@ ) {|sig|} #vs (a1:action vs) (a2:action vs) : action vs  =
  fun s0 ->
  match a1 s0 with
  | Some upd1 -> Some upd1
  | None ->
  a2 s0


/// # Data nondetermism: the *nondet* effect

/// A computation of a value of type `a` in a nondet context
type nondet (a:Type) = Rng.t a

/// Nondeterministically select a value of type `a` from a non-empty set
val one_of #a {|ordered a|} : Set.non_empty a -> nondet a
let one_of #a {|ordered a|} (s:Set.non_empty a) : nondet a =
  Rng.rand_choice s.ls

let ( !? ) {|s:sig|} #rs #vs
    (rnda: read rs (nondet (action vs)))
    : nondet (action #s vs)
    =
    fun rng_st ->
    let a : action vs = fun s0 ->
      /// FIXME: We are not properly advancing the state here
      let a, _ = rnda s0 rng_st in
      a s0
    in
    (a, Rng.incr_state rng_st)

// (
//     // f)un rng s0 ->
//     let nda = rnda s0 in
//     nda rng

open Quint.Ordered

module Set = Quint.Set



/// # Transitions

// A transition is an action that updates all the variables
type transition {|sig|} #vs = a:action vs{(forall (v : vars). mem v vs)}

let apply_det {|s:sig|} #vs
  (t:transition #s #vs)
  (s0:state{is_updated s0})
  : option (s1:state{state_has s1 vs})
   =
  match t s0 with
  | None -> None
  | Some update ->
  Some (update empty_state)


/// Apply a transition to the state
let apply {|s:sig|} #vs
  (nt:nondet (transition #s #vs))
  (s0:state{is_updated s0})
  : nondet (option (s1:state{state_has s1 vs}))
  =
  let? t = nt in
  apply_det t s0

let rec run_aux {|s:sig|} #vs
  (nt:nondet (transition #s #vs))
  (s0:state{is_updated s0})
  : nat -> nondet (list state)
  = function
  | 0 -> return []
  | n ->
  apply nt s0 >>= (function
  | None    -> return []
  | Some s1 ->
  let? states = run_aux nt s0 (n - 1) in
  s0 :: states)

/// Run a transition for n_steps, or until it deadlocks
let run {|s:sig|} #vs
  (n_steps:nat)
  (i:init_t)
  (nt:nondet (transition #s #vs)) =
  let s0 = init s i in
  run_aux nt s0 n_steps

// TODO: need to adjust precedence so don't need to use brackets
let _ex_conj_action : transition =
  (  V @= 1
  &@ U @= "foo"
  )

let _ex_disj_action : action [V] =
  (  V @= 1
  |@ V @= 2
  )

let _ex_comb_action : transition =
  (  V @= 1
  &@ U @= "foo"
  )
  |@
  (  V @= 10
  &@ U @= "fee"
  )


let _ex_req_action : action [V; U] =
  (  req (let! v = !V in v > 1)
  &@ V @= 1
  &@ U @= "foo"
  ) |@ (  req (
      let! v = !V
      and! x = !U
      in
      v < 1 && x = "foo"
     )
  &@ V @= 10
  &@ U @= "fee"
  )

let _ex_nondet_action : nondet transition
  =
    let? vr : int = one_of (Set.set[1;2;3])
    and? xr : string = one_of (Set.set["a"; "b"; "c"])
    in
    (  req (
          let! v' = !V
          and! x' = !U
          in
          v' > vr && x' = xr
       )
    &@ V @= vr
    &@ U @= xr
    )
