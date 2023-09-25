
module Quint.State

open FStar.Tactics.Typeclasses
open FStar.List.Tot

open Quint.Util
open Quint.Ordered
open Quint.Rng.Ops
open Quint.Show

module DM = FStar.DependentMap
module List = FStar.List.Tot
module Rng = Quint.Rng
module Set = Quint.Set


/// # State

/// State signature
///
/// Defines a state space
class sig = {
   /// `var_t` is the set of "flexible variables"
   var_t:eqtype;
   /// Show a variable
   show_var: var_t -> string;
   /// `vars` is a list of all the variables
   vars: list var_t;
   /// `types` maps each variable to the types of the values it can be assigned
   types: var_t -> Type;
}

// TODO Contrib upstream
(** If an element can be [index]ed, then it is a [mem] of the list. *)
private
let rec lemma_index_mem (#t:eqtype) (l:list t) (i:nat{i < length l}) :
  Lemma
    (ensures (index l i `mem` l))
    [SMTPat (index l i `mem` l)]
    =
  match i with
  | 0 -> ()
  | _ -> lemma_index_mem (tl l) (i - 1)

private
let rec as_list_of_list_mems_aux (#a:eqtype) (l:list a) (i:nat{i < length l}) :
  Tot (list (x:a{mem x l}))
      (decreases length l - i)
  =
  if i = (length l - 1) then
    [index l i]
  else
    index l i :: as_list_of_list_mems_aux l (i + 1)

private
let as_list_of_list_mems (#a:eqtype) (l:list a): list (x:a{mem x l}) =
  match l with
  | []   -> []
  | _::_ -> as_list_of_list_mems_aux l 0

private
let _ex_as_list_of_list_mems =
   let ls = ["a"; "b"; "c"] in
   // let ls_t = x:string{List.mem x ls} in
   let _ : list (x:string{List.mem x ls}) = as_list_of_list_mems ls in
   ()

let state_signature (vars : list string{length vars > 0}) (typef:(s:string{mem s vars} -> Type)) : sig =
   let variables : list (x:string{List.mem x vars}) = as_list_of_list_mems #string vars in
   { var_t = (x:string{mem x vars})
   ; show_var = (fun s -> s)
   ; vars  = variables
   ; types = typef
   }

let optional #k : tf:(k -> Type) -> x:k -> t:Type{t == option (tf x)} =
  fun f v -> option (f v)


// TODO Find a way to abstract implementation of this so we don't have to expose the
// dep map impl.
/// A state defined by a signature `sig`
let state {| s:sig |} = DM.t var_t (optional s.types)

// type concrete {|sig|} = list (v:var_t & types v)

/// Predicates over states
let is_assigned {| sig |} (m:state) k = Some? (DM.sel m k)
let is_unassigned {| sig |} (m:state) k = None? (DM.sel m k)
let is_fresh {| sig |} (m:state) = forall (v:var_t). is_unassigned m v
let is_updated {| sig |} (m:state) = forall (v:var_t). is_assigned m v

let as_concrete {|sg:sig|}
  (s:(state #sg){is_updated #sg s})
  : list (dtuple2 var_t types) =
  List.map (fun v -> (| v, Some?.v (DM.sel s v) |)) sg.vars

let init_opt {| sig |}: f:(v:var_t -> types v) -> v':var_t -> option (types v') =
  fun init variable -> Some (init variable)

/// A state initialization function
type init_t {|sig|} = v:var_t -> types v

/// Construct a state from an initialization function
val init : sig -> init_t -> s:state{is_updated s}
let init (s:sig) (f:init_t) : state = DM.create (init_opt f)

let empty_state {| sig |} : m:state{is_fresh m} =
  let clear _  = None in
  DM.create (clear)

let upd {| sig |} (v:var_t) (x:types v)
  : m:state{is_unassigned m v} -> m':state{is_assigned m' v} =
  fun m -> DM.upd m v (Some x)



// START State Example
type ex_var = | V | U
instance ex_sig : sig = state_signature
  [ "v"; "u"]
  (function
  | "v" -> int
  | "u" -> string)


// Trying to update the same variable twice fails
[@@expect_failure [19]]
let _ex_cannot_update_twice = (upd "v" 10 (upd "v" 1 empty_state))

let _ex_is_updated = assert_norm (is_updated (upd "u" "foo" (upd "v" 1  empty_state)))

let _ex_is_updated_empty = assert_norm (is_unassigned (empty_state ) "v")

// let _ex_is_updated_partial = assert_norm (~(is_updated (upd "v" 1 empty_state )))




let _s = init ex_sig (function
  | "v" -> 0
  | "u" -> "foo")

let _ex_s_concrete = assert_norm (
  as_concrete _s
  =
  [ (| "v", 0     |)
  ; (| "u", "foo" |)
  ]
)

let _ex_init = assert_norm (is_updated _s)
let _ex_v = assert_norm (DM.sel _s "v" = Some 0)
let _ex_x = assert_norm (DM.sel _s "u" = Some "foo")
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
let state_has {|sig|} (s:state) (vs:list var_t) =
    forall v. mem v vs ==> is_assigned s v

let state_not_has {|sig|} (s:state) (vs:list var_t) =
    forall v. mem v vs ==> is_unassigned s v

let if_state_has_all_it_is_updated
    {|sig|}
    (s:state)
    (vs:list var_t)
    : Lemma ((state_has s vs /\ (forall (v:var_t). mem v vs)) ==> is_updated s)
    // [SMTPat (state_has s vs); SMTPat (is_updated s)]
    = ()

/// A computation of a value of type `a`,
/// over a state defined by `sig`
/// that can read from the variables in `list vars`
type read {|sig|} (vs:list var_t) (a:Type)
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
val ( ! ) {| sig |} : v:var_t -> read [v] (types v)
let ( ! ) {| sig |} (v:var_t) : read [v] (types v) // s:state{is_assigned s v} -> types v
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

let _read_ex : read #ex_sig ["u"; "v"] (int * string) =
    let! v = !"v"
    and! u = !"u"
    in
    (v, u)

/// # State predicates: the *action* effect

/// A state predicate, i.e., an action
///
/// An action over the state defined by `sig`
/// that updates the variables `vars`
///
/// - `s0` is the current state
/// - `s` is the intermediate state to be updated (lets us ensure no state is updated twice)
/// - `s1` is the next state specified by by the action
type action {|sig|} (vs:list var_t)
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
val ( @= ) {|sig|} : v:var_t -> x:types v -> action [v]
let ( @= ) {|sig|} (v:var_t) (x:types v) : action [v]
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
type transition {|sig|} #vs = a:action vs{(forall (v : var_t). mem v vs)}

let apply_det {|s:sig|}
  (t:transition #s #vars)
  (s0:state{is_updated s0})
  : option (s1:state{is_updated s1})
   =
  match t s0 with
  | None -> None
  | Some update ->
  Some (update empty_state)


/// Apply a transition to the state
let apply {|s:sig|}
  (nt:nondet (transition #s #vars))
  (s0:state{is_updated s0})
  : nondet (option (s1:state{is_updated s1}))
  =
  let? t = nt in
  apply_det t s0

module IO = FStar.IO

let rec run_aux {|s:sig|}
  (nt:nondet (transition #s #vars))
  (s0:state{is_updated s0})
  : c:nat
  -> Tot (nondet (list (s1:state{is_updated s1})))
         (decreases c)
  = function
  | 0 -> return [s0]
  | n ->
    let _ = IO.debug_print_string ("@ RUNNING STATE " ^ Prims.string_of_int n ^ "\n") in
    apply nt s0 >>= (function
  | None    ->
    let _ = IO.debug_print_string ("@ DEADLOCK\n") in
    // Report the last state run
    return [s0]
  | Some s1' ->
    let _ = IO.debug_print_string ("@ STATE SUCEEDED\n") in
    let? states = run_aux nt s1' (n - 1) in
    s0 :: states)

/// Run a transition for n_steps, or until it deadlocks
let run {|sg:sig|}
  (n_steps:nat)
  (i:init_t)
  (nt:nondet (transition #sg #vars))
  (seed: nat)
  : list (s:state{is_updated s})
  =
  let s0 = init sg i in
  run_aux nt s0 n_steps
  |> Rng.run seed

type trace_t {|sig|} = list (list (dtuple2 var_t types))

let trace
  {|sig|}
  (states:list (s:state{is_updated s}))
  : trace_t
  =
  List.map as_concrete states

open Quint.Show
open Quint.Map
open Quint.Set

let string_of_state_value
  #a #b {|Show.show a|} {|Show.show b|}
  (v:a) (u:b)
  : string
  =
  to_string v ^ " -> " ^ to_string u


// TODO: way to convert state values to string
// let rec state_to_string
//   {|sig|} (#v:var_t) {|show var_t|} {|show (types v)|}
//   : (list (dtuple2 var_t types)) -> string
//   = function
//   | [] -> ""
//   | (| a, b |) :: rest -> string_of_state_value a b ^ "\n" ^ state_to_string rest

// let rec trace_to_string {|sig|} : trace_t -> string
//   = function
//   | [] -> ""
//   | s :: ss -> state_to_string s ^ "\n---------\n" ^ trace_to_string ss

// let run_debug {|sg:sig|}
//   (n_steps:nat)
//   (i:init_t)
//   (nt:nondet (transition #sg #vars))
//   (seed: nat)
//   : string
//   =
//   trace_to_string (trace (run n_steps i nt seed))

// instance show_trace {|sig|} : show (trace_t) = {
//    to_string = trace_to_string
// }

let _ex_read_v : read ["v"] int =
  let! v = !"v" in
  v + 1

let _ex_read_u : read ["u"] string =
  let! u = !"u" in
  u ^ "!"

let _ex_composing_reads : read ["v"; "u"] (int * string) =
  let! v' = _ex_read_v
  and! u' = _ex_read_u
  in
  (v', u')

let _ex_action_updating_v : action ["v"] =
  "v" @= 1

let _ex_action_updating_u : action ["u"] =
 "u" @= "foo"

let _ex_composing_actions : action ["v"; "u"]  =
  _ex_action_updating_v
  &@
  _ex_action_updating_u

let _ex_disj_action : action ["v"] =
  (  "v" @= 1
  |@ "v" @= 2
  )

let _ex_comb_action : transition =
  (  "v" @= 1
  &@ "u" @= "foo"
  )
  |@
  (  "v" @= 10
  &@ "u" @= "fee"
  )


let _ex_req_action : action ["v"; "u"] =
  (  req (let! v = !"v" in v > 1)
  &@ "v" @= 1
  &@ "u" @= "foo"
  ) |@ (  req (
      let! v = !"v"
      and! x = !"u"
      in
      v < 1 && x = "foo"
     )
  &@ "v" @= 10
  &@ "u" @= "fee"
  )

let _ex_nondet_action : nondet transition
  =
    let? vr : int = one_of (Set.set[1;2;3])
    and? xr : string = one_of (Set.set["a"; "b"; "c"])
    in
    (  req (
          let! v' = !"v"
          and! x' = !"u"
          in
          v' > vr && x' = xr
       )
    &@ "v" @= vr
    &@ "u" @= xr
    )
