
module Quint.State

open FStar.List.Tot
open Quint.Rng



/// # State

/// State signature
class sig = {
   /// `vars` is the set of "flexible variables"
   vars:eqtype;
   /// `types` maps each variable to the types of the values it can be assigned
   types: vars -> Type
}

/// A state defined by a signature `sig`
val state {| sig |} : Type

/// A state initialization function
type init_t {|sig|} = v:vars -> types v

/// Construct a state from an initialization function
val init : sig -> init_t -> state



/// # State functions: the *read* effect

/// A computation of a value of type `a`,
/// over a state defined by `sig`
/// that can read from the variables in `list vars`
val read {|sig|} : list vars -> (a:Type) -> Type

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

/// An action over the state defined by `sig`
/// that updates the variables `vars`
val action {|sig|} : list vars -> Type

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
val nondet (a:Type) : Type

open Quint.Rng
open Quint.Ordered

module Set = Quint.Set

/// Run a nondet computatoin
let run = run

/// Nondeterministically select a value of type `a` from a non-empty set
val one_of #a {|ordered a|} : Set.non_empty a -> nondet a

/// Bind a value in a nondet context
let (let?) = (let?)
