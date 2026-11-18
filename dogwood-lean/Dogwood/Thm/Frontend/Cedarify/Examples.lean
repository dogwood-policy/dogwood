import Dogwood.Thm.Frontend.Cedarify.Context
import Dogwood.Thm.Frontend.Cedarify.Names
import Dogwood.Thm.Frontend.Cedarify.Targets

/-!
# What cedarify does not check: three small sets

Lowering accepts each of these sets; each violates a clause of the specification's
`PolicySet.Valid`, the last two when the clause is read with the crate's names for the leaves.
The crate's validation must therefore check these clauses itself.

* `when { context == {} }` reads `context` as a whole: the rule in the specification's form does
  not satisfy `ReadsContext` (the `readsContext` clause), whatever the reserved names.
* `when { temporal { tp(t) } && context.policy_0__temporal_0 }` reads, as written, the context
  attribute that the crate gives its own leaf: the crate's rule reads the leaf's value twice where
  the specification's reads the leaf and the request's attribute. The rule satisfies
  `ReadsContext` with the specification's names, not with the crate's.
* With an action schema whose action `a` declares the context attribute `policy_0__temporal_0`,
  a rule on `a` with a temporal leaf hoists it to that very attribute (the `namesFresh` clause,
  for the crate's names); augmentation then replaces the declared attribute.
-/

namespace Dogwood.Thm.Frontend.Cedarify.Examples

open Dogwood.Spec
open Dogwood.Frontend
open Dogwood.Frontend.Cedarify

/-- A span, for the examples. -/
def sp : Span := ⟨0, 0⟩

/-- An expression of the examples. -/
def ex (k : Surface.ExprKind) : Surface.Expr := ⟨k, sp⟩

/-- `permit (principal, action, resource) when { body };`. -/
def rule (action : Surface.ActionConstraint) (body : Surface.Expr) : Surface.Policy :=
  { span := sp, annotations := [], effect := .permit,
    scope := { span := sp, principal := .any, action, resource := .any },
    conditions := [{ span := sp, keyword := .when, body }] }

/-! ## Reading the context as a whole -/

/-- `context == {}`. -/
def readsWholeContext : Surface.Policy :=
  rule .any (ex (.binaryApp .eq (ex (.var .context)) (ex (.record []))))

/-- The rule in the specification's form. -/
def readsWholeContextSpec : Policy :=
  { id := "policy_0", effect := .permit, principalScope := .principalScope .any,
    actionScope := .actionScope .any, resourceScope := .resourceScope .any,
    condition := [⟨.when, .binaryApp .eq (.var .context) (.record [])⟩] }

example : ∃ w, cedarifyFull ⟨[readsWholeContext], []⟩ [] none = .ok w ∧
    w.spec = [readsWholeContextSpec] ∧ ∀ R, ¬ readsWholeContextSpec.toExpr.ReadsContext R :=
  ⟨_, rfl, rfl, fun R => by
    simp [readsWholeContextSpec, Policy.toExpr, Expr.ReadsContext, Conditions.toExpr,
      Condition.toExpr]⟩

/-! ## Reading the crate's name for a leaf -/

/-- `temporal { tp(t) }`. -/
def leaf : Surface.Expr :=
  ex (.extension ⟨⟨sp, .tp (.name "t")⟩, sp⟩)

/-- `temporal { tp(t) } && context.policy_0__temporal_0`. -/
def readsLeafName : Surface.Policy :=
  rule .any (ex (.binaryApp .and leaf (ex (.getAttr (ex (.var .context)) "policy_0__temporal_0"))))

example : (cedarifyFull ⟨[readsLeafName], []⟩ [] none).map (fun w => (w.cedar.map (·.condition), w.refs)) =
    .ok ([[⟨.when, .and (.getAttr (.var .context) "policy_0__temporal_0")
              (.getAttr (.var .context) "policy_0__temporal_0")⟩]],
         [.getAttr (.var .context) "policy_0__temporal_0"]) := rfl

/-- The rule in the specification's form. -/
def readsLeafNameSpec : Policy :=
  { id := "policy_0", effect := .permit, principalScope := .principalScope .any,
    actionScope := .actionScope .any, resourceScope := .resourceScope .any,
    condition := [⟨.when, .and (.temporal (.tp "t"))
      (.getAttr (.var .context) "policy_0__temporal_0")⟩] }

example : ∃ w, cedarifyFull ⟨[readsLeafName], []⟩ [] none = .ok w ∧ w.spec = [readsLeafNameSpec] ∧
    readsLeafNameSpec.toExpr.ReadsContext [leafAttr 0] ∧
    ¬ readsLeafNameSpec.toExpr.ReadsContext ["policy_0__temporal_0"] :=
  ⟨_, rfl, rfl, by
    simp only [readsLeafNameSpec, Policy.toExpr, Expr.ReadsContext, Conditions.toExpr,
      Condition.toExpr, List.reverse_cons, List.reverse_nil, List.nil_append, List.foldl_nil]
    refine ⟨readsContext_ofCedar_scope .any .principal (by simp), readsContext_ofCedar_actionScope _,
      readsContext_ofCedar_scope .any .resource (by simp), trivial, ?_⟩
    simp only [Expr.isContext, ↓reduceIte]
    decide, by
    simp [readsLeafNameSpec, Policy.toExpr, Expr.ReadsContext, Conditions.toExpr, Condition.toExpr,
      Expr.isContext]⟩

/-! ## A declared attribute with the crate's name for a leaf -/

/-- `entity U; action a appliesTo { principal: U, resource: U, context: { policy_0__temporal_0:
String } };`. -/
def declaresLeafName : CedarSchema.Fragment :=
  let ctx : CedarSchema.SchemaType := .record [("policy_0__temporal_0", ⟨.string, true, []⟩)] false
  let a : CedarSchema.ActionDef := {
    attributes := none, memberOf := none, annotations := [],
    appliesTo := some { principalTypes := ["U"], resourceTypes := ["U"], context := ctx } }
  let u : CedarSchema.EntityTypeDef := { kind := .standard [] (.record [] false) none, annotations := [] }
  [(none, { commonTypes := [], entityTypes := [("U", u)], actions := [("a", a)], annotations := [] })]

/-- `permit (principal, action == Action::"a", resource) when { temporal { tp(t) } };`. -/
def onA : Surface.Policy := rule (.eq ⟨⟨"Action", []⟩, "a"⟩) leaf

example : ∃ w, cedarifyFull ⟨[onA], []⟩ declaresLeafName none = .ok w ∧
    w.cedarified.contextFields.map (·.fieldName) = ["policy_0__temporal_0"] ∧
    ∀ f ∈ w.cedarified.contextFields, ("", "a") ∈ f.targetActions := by
  have hw : cedarifyFull ⟨[onA], []⟩ declaresLeafName none = .ok _ := rfl
  refine ⟨_, hw, by decide, fun f hf => ?_⟩
  obtain ⟨p, hp, -, -, -, ht⟩ := (cedarify_targets hw).1 f hf
  simp only [List.mem_singleton] at hp
  subst hp
  rw [ht, mem_scopeTargetActions]
  exact ⟨rfl, .inr (by decide)⟩

end Dogwood.Thm.Frontend.Cedarify.Examples
