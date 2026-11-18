import Dogwood.Spec.Validity

/-!
# Two lowerings in sequence

A policy set can be lowered against a schema that an earlier lowering augmented (the crate's
`lower_with_distincter`, "feeding an augmented schema forward"). The crate keeps the two sets'
hoisted attributes apart with a distincter; here, where leaf attributes are `leafAttr k`, a
distincter is an offset: the second set's leaves are numbered after the first's.

* `PolicySet.loweredFrom k`, `hoistedNamesFrom k`, `hoistedTypesFrom? k`, `augmentedSchemaFrom k`
  (action-selective, as `PolicySet.augmentedSchema` is), and `PolicySet.ValidFrom k`: lowering and
  validity with the leaves numbered from `k`
  (`ValidFrom 0` is `Valid`, `Dogwood.Thm.validFrom_zero_iff`).
* `A.next qs`, the second lowering's policy set, and `A.join qs`, the two together.
* What a rule reads of the request context, at the head of a `context.<path>`: in a temporal
  formula (`Formula.AvoidsContext`), a provider invocation (`Provider.Call.AvoidsContext`), and the
  event schema's pins (`PinsAvoid`).

The theorems are in `Dogwood.Thm.Composition`.
-/

namespace Dogwood.Spec

open Cedar.Spec (Attr)
open Cedar.Validation (Schema QualifiedType)

/-! ## Lowering from an offset -/


/-- The policy set's rules, lowered with their leaves numbered from `k`. -/
def PolicySet.loweredFrom (P : PolicySet) (k : Nat) : Cedar.Spec.Policies :=
  (Policies.lowerFrom k P.policies).1

/-- The attributes a lowering from `k` adds to the request context. -/
def PolicySet.hoistedNamesFrom (P : PolicySet) (k : Nat) : List Attr :=
  (List.range' k P.leafList.length).map leafAttr

/-- The attributes a lowering from `k` adds to the request context, with their types. -/
def PolicySet.hoistedTypesFrom? (P : PolicySet) (k : Nat) :
    Option (List (Attr × QualifiedType)) :=
  (P.leafList.zipIdx k).mapM fun (l, i) => (P.leafType? l).map fun ty => (leafAttr i, .required ty)

/-- The schema a lowering from `k` validates the lowered rules against: each leaf's attribute
added to the contexts of the actions its rule's action scope admits. -/
def PolicySet.augmentedSchemaFrom (P : PolicySet) (k : Nat) : Schema :=
  P.selectiveAugment ((P.hoistedTypesFrom? k).getD [])

/-- The schema with every attribute of a lowering from `k` added to every action's context. -/
def PolicySet.allAugmentedSchemaFrom (P : PolicySet) (k : Nat) : Schema :=
  Schema.augment P.actionSchema ((P.hoistedTypesFrom? k).getD [])

/-- **Validity of a lowering from `k`**: `PolicySet.Valid`, with the leaves numbered from `k`. -/
structure PolicySet.ValidFrom (P : PolicySet) (k : Nat) : Prop where
  leafTypes : (P.hoistedTypesFrom? k).isSome = true
  namesNodup : (P.hoistedNamesFrom k).Nodup
  namesFresh : ∀ act ∈ P.actionSchema.acts.toList, ∀ a ∈ P.hoistedNamesFrom k,
    act.2.context.find? a = none
  readsContext : P.leafList ≠ [] → ∀ p ∈ P.policies, p.toExpr.ReadsContext (P.hoistedNamesFrom k)
  wellFormed : (P.augmentedSchemaFrom k).validateWellFormed = .ok ()
  standardAncestors : (P.augmentedSchemaFrom k).standardAncestors = true
  complete : P.policies ≠ [] → P.externalTypes = [] ∧ P.externalActions = []
  cedar : Cedar.Validation.validate (P.loweredFrom k) (P.augmentedSchemaFrom k) = .ok ()
  temporal : ∀ p ∈ P.policies, ∀ φ F, (.inl φ, F) ∈ p.toExpr.leafFacts [] → P.LeafValid p F φ
  providers : ∀ p ∈ P.policies, ∀ c F, (.inr c, F) ∈ p.toExpr.leafFacts [] →
    c.Declared P.providerDecls ∧ ∀ env ∈ P.envsOf p, c.TypedIn (P.typingCtx env F) P.providerDecls
  horizon : ∀ H, P.maxHorizon = some H → ∀ φ ∈ P.temporalLeaves, φ.horizon .seconds ≤ H

/-! ## Two lowerings -/

/-- The policy set the second of two lowerings checks: the rules `qs`, against `A`'s augmented
schema. It shares `A`'s service schema (event schema, provider declarations, `max_window`, clock
rate, external names): the model covers feed-forward lowering under one service schema, while
the crate parses each set with a service schema of its own. -/
def PolicySet.next (A : PolicySet) (qs : Policies) : PolicySet :=
  { A with policies := qs, actionSchema := A.augmentedSchema }

/-- `A` with the rules `qs` added after its own. -/
def PolicySet.join (A : PolicySet) (qs : Policies) : PolicySet :=
  { A with policies := A.policies ++ qs }

/-! ## Context reads -/

namespace Temporal

/-- A path's head is outside `N`. -/
def headAvoids (N : List Attr) : Path → Prop
  | [] => True
  | a :: _ => a ∉ N

mutual

/-- A term reads no context attribute in `N` (at the head of a `context.<path>`). -/
def Term.AvoidsContext (N : List Attr) : Term → Prop
  | .context p => headAvoids N p
  | .agg a => a.AvoidsContext N
  | .arith _ l r => l.AvoidsContext N ∧ r.AvoidsContext N
  | _ => True

def Aggregate.AvoidsContext (N : List Attr) : Aggregate → Prop
  | .count _ body | .sum _ _ body => body.AvoidsContext N

/-- A formula reads no context attribute in `N`. -/
def Formula.AvoidsContext (N : List Attr) : Formula → Prop
  | .and φ ψ | .since φ _ ψ => φ.AvoidsContext N ∧ ψ.AvoidsContext N
  | .not φ | .formerly _ φ | .previous _ φ | .exist _ φ => φ.AvoidsContext N
  | .pred _ _ args => Formula.argsAvoidContext N args
  | .cmp _ l r => l.AvoidsContext N ∧ r.AvoidsContext N
  | .tp _ => True

def Formula.argsAvoidContext (N : List Attr) : List (Path × Term) → Prop
  | [] => True
  | (_, t) :: args => t.AvoidsContext N ∧ Formula.argsAvoidContext N args

end

/-- The pins of an event schema read no context attribute in `N`. -/
def PinsAvoid (N : List Attr) (S : EventSchema) : Prop :=
  ∀ sig ∈ S, ∀ pin ∈ sig.pins, ∀ p, pin.ref = .context p → headAvoids N p

end Temporal

open Temporal

mutual

/-- A provider argument reads no context attribute in `N`. -/
def Provider.Arg.AvoidsContext (N : List Attr) : Provider.Arg → Prop
  | .context p => headAvoids N p
  | .set items => Provider.Arg.allAvoidContext N items
  | _ => True

def Provider.Arg.allAvoidContext (N : List Attr) : List Provider.Arg → Prop
  | [] => True
  | x :: xs => x.AvoidsContext N ∧ Provider.Arg.allAvoidContext N xs

end

/-- A provider invocation reads no context attribute in `N`, in its arguments or its methods'. -/
def Provider.Call.AvoidsContext (N : List Attr) (c : Provider.Call) : Prop :=
  (∀ a ∈ c.args, a.AvoidsContext N) ∧ ∀ m ∈ c.methods, ∀ a ∈ m.args, a.AvoidsContext N

end Dogwood.Spec
