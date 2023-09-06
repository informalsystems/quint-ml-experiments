module Quint.State.Sig

open FStar.Tactics.Typeclasses

/// State signature
///
/// Defines a state space
class sig = {
   /// `vars` is the set of "flexible variables"
   vars:eqtype;
   /// `types` maps each variable to the types of the values it can be assigned
   types: vars -> Type
}
