
module Quint.State

open FStar.List.Tot
open Quint.Rng
open FStar.Tactics.Typeclasses
open Quint.State.Sig

module DM = FStar.DependentMap



/// # State

let optional #k : (k -> Type) -> k -> Type =
  fun f v -> option (f v)

// TODO Find a way to abstract implementation of this so we don't have to expose the
// dep map impl.
/// A state defined by a signature `sig`
let state {| s:sig |} = DM.t vars (optional s.types)

// /// A state defined by a signature `sig`
// val state {| sig |} : DM.t vars (optional types)

/// A state initialization function
type init_t {|sig|} = v:vars -> types v

/// Construct a state from an initialization function
val init : sig -> init_t -> state

/// Predicates over states
let is_assigned {| sig |} (m:state) k = Some? (DM.sel m k)
let is_unassigned {| sig |} (m:state) k = None? (DM.sel m k)
let is_fresh {| sig |} (m:state) = forall k. is_unassigned m k
let is_updated {| sig |} (m:state) = forall k. is_assigned m k

/// # State functions: the *read* effect

// TODO Use `DM.restrict` to limit map to just declared variables
// A computation of `a` that can read from `state #sig`
// TODO Figure out how to hide and abstract these
let state_has {|sig|} (s:state) (vs:list vars) =
    forall v. mem v vs ==> is_assigned s v

let state_not_has {|sig|} (s:state) (vs:list vars) =
    forall v. mem v vs ==> is_unassigned s v

/// A computation of a value of type `a`,
/// over a state defined by `sig`
/// that can read from the variables in `list vars`
type read {|sig|} (vs:list vars) (a:Type)
  = s:state{state_has s vs} -> a

/// Puts a value of type `a` in a `read` context
val pure {|sig|} #a #vs (x:a) : read vs a

/// Read a value of type `types v`
val ( ! ) {| sig |} : v:vars -> read [v] (types v)

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


/// Requirements
val req {| sig |} #vs : read vs bool -> action []

/// `v @= x` updates the state variable `v` to the value `x` in the next state
val ( @= ) {|sig|} : v:vars -> x:types v -> action [v]

/// The composition of actions
val ( &! ) {|sig|} #vs #vs'
  :  a1:action vs
  -> a2:action vs'{forall v. mem v vs' ==> not (mem v vs)}
  -> action (vs @ vs')

/// The alternation of actions
val ( |! ) {|sig|} #vs : action vs -> action vs -> action vs



/// # Data nondetermism: the *nondet* effect

/// A computation of a value of type `a` in a nondet context
type nondet (a:Type) = Rng.t a

open Quint.Ordered

module Set = Quint.Set

/// Run a nondet computatoin
let run = run

/// Nondeterministically select a value of type `a` from a non-empty set
val one_of #a {|ordered a|} : Set.non_empty a -> nondet a

open Quint.Rng

/// Bind values in nondet contexts
///
/// ```
/// let ex : nondet (action [V; X]) =
///   let? a = one_of (set[1;2;3])
///   and? b = one_of (set["a"; "b"; "c"])
///   in
///   (  req (
///        let! v = !V
///        and! x = !X
///        in
///        v > a && x = "a" )
///   &! V @= a
///   &! X @= b
///   )
/// ```
let (let?) = (let?)
let (and?) = (and?)



/// # Transitions