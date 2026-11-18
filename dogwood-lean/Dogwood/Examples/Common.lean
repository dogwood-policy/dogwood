import Dogwood.Thm.Decision
import Dogwood.Thm.Scale
import Dogwood.Thm.Leaves
import Dogwood.Thm.ValidityDecide
import Dogwood.Thm.CedarValidation
import Dogwood.Thm.ConformanceDecide
import Dogwood.Thm.SelectiveAugment

/-!
# Shared scaffolding for the worked examples

The guide's example bundles (`dogwood-docs/examples/<name>/`) share one
shape: a single rule `permit (principal, action == A, resource) when temporal
{ φ }`, the `Drupe` action schema, the default event schema (pinned or
unpinned), and a `.log` trace whose events log their `input` record and
their caller fields. This module builds those pieces and proves, once, how
such a policy set decides (`decision_temporalPermit`): an event every check of
which passes is allowed exactly when it is an `A` event and `φ` holds there.
-/

namespace Dogwood.Examples

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Thm
open Cedar.Spec (EntityUID EntityType Value Attr Entities)
open Cedar.Validation (CedarType)
open Cedar.Data (Map Set)

def drupe (ty id : String) : EntityUID := ⟨⟨ty, ["Drupe"]⟩, id⟩

def oauthUser (name : String) : EntityUID := drupe "OAuthUser" name
def gw1 : EntityUID := drupe "Gateway" "gw1"
def action (name : String) : EntityUID := drupe "Action" name

/-- The event of a `.log` line `@ts scope(principal: P, resource: gw1)
request_context(input: I) A::kind(input: I, callerPrincipal: P,
callerResource: gw1, requestId: R)`. -/
def logEvent (principal act : EntityUID) (kind requestId : String)
    (input : List (Attr × Value)) : Event where
  action := act
  kind := kind
  principal := some principal
  resource := some gw1
  logged := Map.make [
    ("input", .record (Map.make input)),
    ("callerPrincipal", .prim (.entityUID principal)),
    ("callerResource", .prim (.entityUID gw1)),
    ("requestId", .prim (.string requestId))]
  context := Map.make [("input", .record (Map.make input))]
  entities := Map.empty

/-- The default event schema's universal symmetric pin. -/
def callerPin : Pin := ⟨["callerPrincipal"], .scope .principal []⟩

def oauthUserType : EntityType := ⟨"OAuthUser", ["Drupe"]⟩
def gatewayType : EntityType := ⟨"Gateway", ["Drupe"]⟩

/-- An action of the examples, with the fields of its `context.input` record, all required. -/
abbrev ActionDecl := EntityUID × List (Attr × CedarType)

/-- The `Drupe` action schema of the examples' bundles: `OAuthUser` principals with a
required `id`, `Gateway` resources, and each action's `context.input` record. -/
def actionSchema (actions : List ActionDecl) : Cedar.Validation.Schema where
  ets := Map.make [
    (oauthUserType, .standard ⟨Set.empty, Map.make [("id", .required .string)], some .string⟩),
    (gatewayType, .standard ⟨Set.empty, Map.empty, none⟩)]
  acts := Map.make (actions.map fun (a, inputs) =>
    (a, { appliesToPrincipal := Set.make [oauthUserType], appliesToResource := Set.make [gatewayType],
          ancestors := Set.empty,
          context := Map.make [("input",
            .required (.record (Map.make (inputs.map fun (f, ty) => (f, .required ty)))))] }))

/-- The reserved fields the default event schema declares on every kind. -/
def reservedFields : List FieldDecl :=
  [⟨["callerPrincipal"], .entities [oauthUserType], true⟩,
   ⟨["callerResource"], .entities [gatewayType], false⟩,
   ⟨["requestId"], .cedar .string, false⟩,
   ⟨["sessionId"], .cedar .string, false⟩]

/-- The fields an event of an action logs: its `context.input` record, and the reserved
fields. -/
def actionFields (inputs : List (Attr × CedarType)) : List FieldDecl :=
  inputs.map (fun (f, ty) => ⟨["input", f], .cedar ty, true⟩) ++ reservedFields

/-- The default event schema (`pinned`) or the unpinned one, derived against `actions`: a
`request` decision kind and `response` / `error` history kinds. (It declares no outputs: an
example whose action has outputs builds its own schema.) -/
def defaultSchema (pinned : Bool) (actions : List ActionDecl) : EventSchema :=
  let pins := if pinned then [callerPin] else []
  actions.flatMap fun (a, inputs) =>
    [⟨a, "request", true, pins, actionFields inputs⟩,
     ⟨a, "response", false, pins, actionFields inputs⟩,
     ⟨a, "error", false, pins, actionFields inputs⟩]

/-- `permit (principal, action == a, resource) when temporal { φ }`, as the
first rule of a policy set. -/
def temporalPermit (a : EntityUID) (φ : Formula) : Policy where
  id := "policy_0"
  effect := .permit
  principalScope := .principalScope .any
  actionScope := .actionScope (.eq a)
  resourceScope := .resourceScope .any
  condition := [⟨.when, .temporal φ⟩]

/-- The one-rule policy set, over the given actions and event schema. Its clock counts one tick
per second, the unit the bundles record time in: a trace of the examples is the bundle's trace as
recorded. An authorizer that stamps in nanoseconds would stamp each event at its recorded time in
nanoseconds, and decide alike (`Dogwood.Thm.authorize_scale`; `ReadAfterLogin.outcome_at_10_nanos`
shows one). -/
def onePolicy (a : EntityUID) (φ : Formula) (schema : EventSchema) (actions : List ActionDecl) :
    PolicySet where
  policies := [temporalPermit a φ]
  schema := schema
  actionSchema := actionSchema actions
  tickRate := .seconds

/-! ## Validity of a one-rule temporal permit -/

theorem onePolicy_lowered (a : EntityUID) (φ : Formula) (schema : EventSchema)
    (actions : List ActionDecl) :
    (onePolicy a φ schema actions).lowered = [leafPermit "policy_0" a (leafAttr 0)] := rfl

theorem onePolicy_hoistedTypes (a : EntityUID) (φ : Formula) (schema : EventSchema)
    (actions : List ActionDecl) :
    (onePolicy a φ schema actions).hoistedTypes? = some [(leafAttr 0, .required (.bool .anyBool))] :=
  rfl

/-- How a one-rule temporal permit is valid: its leaf's attribute is fresh, the schema augmented
at every action is well-formed and has no enumerated ancestor, Cedar's validator accepts the lowered rule (`validate_leafPermit`), and its leaf is
valid. Each premise is a finite check. -/
theorem onePolicy_valid {a : EntityUID} {φ : Formula} {schema : EventSchema}
    {actions : List ActionDecl}
    (hfresh : (onePolicy a φ schema actions).namesFreshB = true)
    (hA : (Schema.augment (actionSchema actions)
        [(leafAttr 0, .required (.bool .anyBool))]).acts.contains a = true)
    (henvs : ∀ env ∈ (Schema.augment (actionSchema actions)
        [(leafAttr 0, .required (.bool .anyBool))]).environments,
      env.acts.contains env.reqty.action = true ∧ env.acts.contains a = true ∧
      env.reqty.context.find? (leafAttr 0) = some (.required (.bool .anyBool)))
    (hsome : ∃ env ∈ (Schema.augment (actionSchema actions)
        [(leafAttr 0, .required (.bool .anyBool))]).environments, env.reqty.action = a)
    (hwf : succeeds (onePolicy a φ schema actions).allAugmentedSchema.validateWellFormed = true)
    (hstd : (onePolicy a φ schema actions).allAugmentedSchema.standardAncestors = true)
    (hleaf : (onePolicy a φ schema actions).leafFindings (temporalPermit a φ) [] φ = []) :
    (onePolicy a φ schema actions).Valid := by
  have hnames : (onePolicy a φ schema actions).hoistedNames = [leafAttr 0] := rfl
  refine PolicySet.ValidAll.toValid ⟨by rw [onePolicy_hoistedTypes]; rfl, by rw [hnames]; simp,
    ?_, ?_, ?_, hstd, fun _ => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · simp only [PolicySet.namesFreshB, List.all_eq_true, Option.isNone_iff_eq_none] at hfresh
    exact fun act hact a' ha' => hfresh act hact a' ha'
  · intro _ p hp
    simp only [onePolicy, List.mem_singleton] at hp
    subst hp
    rw [hnames]
    simp [temporalPermit, Policy.toExpr, Expr.ofCedar, Cedar.Spec.PrincipalScope.toExpr,
      Cedar.Spec.ActionScope.toExpr, Cedar.Spec.ResourceScope.toExpr, Cedar.Spec.Scope.toExpr,
      Cedar.Spec.Var.eqEntityUID, Conditions.toExpr, Condition.toExpr, Expr.ReadsContext]
  · revert hwf
    cases (onePolicy a φ schema actions).allAugmentedSchema.validateWellFormed with
    | ok u => intro _; rfl
    | error _ => intro h; cases h
  · rw [onePolicy_lowered, PolicySet.allAugmentedSchema, onePolicy_hoistedTypes]
    exact validate_leafPermit _ _ _ _ hA henvs hsome
  · intro p hp φ' F hm
    simp only [onePolicy, List.mem_singleton] at hp
    subst hp
    have : (temporalPermit a φ).toExpr.leafFacts [] = [(.inl φ, [])] := by
      simp [temporalPermit, Policy.toExpr, Expr.ofCedar, Cedar.Spec.PrincipalScope.toExpr,
        Cedar.Spec.ActionScope.toExpr, Cedar.Spec.ResourceScope.toExpr, Cedar.Spec.Scope.toExpr,
        Cedar.Spec.Var.eqEntityUID, Conditions.toExpr, Condition.toExpr, Expr.leafFacts,
        Expr.facts]
    rw [this] at hm
    simp only [List.mem_singleton, Prod.mk.injEq, Sum.inl.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact (leafFindings_eq_nil_iff _ _ _ _).mp hleaf
  · intro p hp c F hm
    simp only [onePolicy, List.mem_singleton] at hp
    subst hp
    have : (temporalPermit a φ).toExpr.leafFacts [] = [(.inl φ, [])] := by
      simp [temporalPermit, Policy.toExpr, Expr.ofCedar, Cedar.Spec.PrincipalScope.toExpr,
        Cedar.Spec.ActionScope.toExpr, Cedar.Spec.ResourceScope.toExpr, Cedar.Spec.Scope.toExpr,
        Cedar.Spec.Var.eqEntityUID, Conditions.toExpr, Condition.toExpr, Expr.leafFacts,
        Expr.facts]
    rw [this] at hm
    simp at hm
  · intro H hH
    cases hH

/-- A computable leaf valuation giving every temporal leaf the value `b`. -/
def constLeaves (b : Bool) : Leaves := ⟨fun _ => b, fun _ => .prim (.bool false)⟩

theorem temporalPermit_leaves (a : EntityUID) (φ : Formula) :
    (temporalPermit a φ).toExpr.leaves = [.inl φ] := rfl

theorem isAuthorized_single_permit {θ : Leaves} {req : Cedar.Spec.Request} {es : Entities}
    {r : Policy} (hr : r.effect = .permit) :
    (isAuthorized θ req es [r]).decision = if satisfied θ r req es then .allow else .deny := by
  cases h : satisfied θ r req es <;>
    simp [isAuthorized, satisfiedPolicies, satisfiedWithEffect, hr, h, Cedar.Data.Set.make,
      Cedar.Data.Set.isEmpty, Cedar.Data.Set.empty, List.canonicalize, List.insertCanonical]

theorem satisfied_temporalPermit (b : Bool) (a : EntityUID) (φ : Formula) (e : Event)
    (pr rs : EntityUID) (es : Entities) :
    satisfied (constLeaves b) (temporalPermit a φ) (e.request pr rs) es = (e.action == a && b) := by
  by_cases ha : e.action = a
  · cases b <;>
    simp [satisfied, temporalPermit, Policy.toExpr, Conditions.toExpr, Condition.toExpr, evaluate,
      Expr.ofCedar, Cedar.Spec.PrincipalScope.toExpr, Cedar.Spec.ActionScope.toExpr,
      Cedar.Spec.ResourceScope.toExpr, Cedar.Spec.Scope.toExpr, Cedar.Spec.Var.eqEntityUID,
      Event.request, constLeaves, Cedar.Spec.apply₂, Cedar.Spec.Result.as, Coe.coe,
      Cedar.Spec.Value.asBool, ha]
  · simp [satisfied, temporalPermit, Policy.toExpr, Conditions.toExpr, Condition.toExpr, evaluate,
      Expr.ofCedar, Cedar.Spec.PrincipalScope.toExpr, Cedar.Spec.ActionScope.toExpr,
      Cedar.Spec.ResourceScope.toExpr, Cedar.Spec.Scope.toExpr, Cedar.Spec.Var.eqEntityUID,
      Event.request, constLeaves, Cedar.Spec.apply₂, Cedar.Spec.Result.as, Coe.coe,
      Cedar.Spec.Value.asBool, ha]

theorem onePolicy_providerCalls (a : EntityUID) (φ : Formula) (schema : EventSchema)
    (actions : List ActionDecl) : (onePolicy a φ schema actions).policies.providerCalls = [] := by
  simp [Policies.providerCalls, onePolicy, temporalPermit_leaves]

/-- A one-rule temporal permit whose leaf reads no attribute of a scope entity passes the check
of the scope entities. -/
theorem onePolicy_scopeEntitiesSupplied {a : EntityUID} {φ : Formula} {schema : EventSchema}
    {actions : List ActionDecl} (hφ : (φ.injectPins schema).scopeReads = []) (e : Event)
    (pr rs : EntityUID) :
    (onePolicy a φ schema actions).scopeEntitiesSupplied (onePolicy a φ schema actions).policies
      e pr rs = true := by
  refine scopeEntitiesSupplied_of_scopeReads_nil (fun q hq ψ hψ => ?_) e pr rs
  simp only [onePolicy, List.mem_singleton] at hq
  subst hq
  rw [temporalPermit_leaves, List.mem_singleton, Sum.inl.injEq] at hψ
  subst hψ
  exact hφ

/-- A one-rule temporal permit whose leaf reads no attribute of a scope entity admits a decision
event whose data conform: it invokes no provider. -/
theorem onePolicy_admits {a : EntityUID} {φ : Formula} {schema : EventSchema}
    {actions : List ActionDecl} {ω : Provider.Providers} {p : TimePoint} {pr rs : EntityUID}
    (hk : schema.isDecisionKind p.event.kind = true)
    (hpr : p.event.principal = some pr) (hrs : p.event.resource = some rs)
    (he : p.event.Conforms (actionSchema actions) schema)
    (hreq : succeeds (Cedar.Validation.validateRequest (actionSchema actions)
      (p.event.request pr rs)) = true)
    (hes : succeeds (Cedar.Validation.validateEntities (actionSchema actions)
      ((onePolicy a φ schema actions).decisionEntities p.event)) = true)
    (hφ : (φ.injectPins schema).scopeReads = []) :
    (onePolicy a φ schema actions).Admits (onePolicy a φ schema actions).policies ω p pr rs :=
  ⟨hk, hpr, hrs, he, hreq, hes, onePolicy_scopeEntitiesSupplied hφ _ _ _,
    providersFail_of_providerCalls_nil (onePolicy_providerCalls a φ schema actions) ω _,
    providerOutputsConform_of_providerCalls_nil (onePolicy_providerCalls a φ schema actions) _ ω _⟩

/-- A one-rule temporal permit admits a decision event whose data the executable checks
accept, when its leaf reads no attribute of a scope entity; each check is a finite computation
that the kernel evaluates (`decide +kernel`). -/
theorem onePolicy_admitsB {a : EntityUID} {φ : Formula} {schema : EventSchema}
    {actions : List ActionDecl} {ω : Provider.Providers} {p : TimePoint} {pr rs : EntityUID}
    (hk : schema.isDecisionKind p.event.kind = true)
    (hpr : p.event.principal = some pr) (hrs : p.event.resource = some rs)
    (he : p.event.conformsB (actionSchema actions) schema = true)
    (hreq : Eval.requestConformsB (actionSchema actions) (p.event.request pr rs) = true)
    (hes : succeeds (Cedar.Validation.validateEntities (actionSchema actions)
      ((onePolicy a φ schema actions).decisionEntities p.event)) = true)
    (hφ : (φ.injectPins schema).scopeReads = []) :
    (onePolicy a φ schema actions).Admits (onePolicy a φ schema actions).policies ω p pr rs :=
  onePolicy_admits hk hpr hrs ((conformsB_iff _ _ _).mp he)
    (requestConformsB_eq _ _ ▸ hreq) hes hφ

/-- A one-rule temporal permit responds to an event as its leaf's value at a leaf valuation
says: it allows exactly when the event is an `a` event and the leaf holds. -/
theorem response_temporalPermit {θ : Leaves} {a : EntityUID} {φ : Formula} {schema : EventSchema}
    {actions : List ActionDecl} (e : Event) (pr rs : EntityUID) (es : Entities) :
    (isAuthorized θ (e.request pr rs) es (onePolicy a φ schema actions).policies).decision =
      if e.action == a && θ.temporal φ then .allow else .deny := by
  have hagree : ∀ q ∈ (onePolicy a φ schema actions).policies,
      θ.AgreeOn (constLeaves (θ.temporal φ)) q.toExpr.leaves := by
    intro q hq
    simp only [onePolicy, List.mem_singleton] at hq
    subst hq
    rw [temporalPermit_leaves]
    intro l hl
    simp only [List.mem_singleton] at hl
    subst hl
    rfl
  rw [isAuthorized_congr hagree,
    show (onePolicy a φ schema actions).policies = [temporalPermit a φ] from rfl,
    isAuthorized_single_permit rfl, satisfied_temporalPermit]

/-- How a one-rule temporal permit decides an event every check of which passes: it allows
exactly when the event is an `a` event and the temporal leaf holds, under every completion of
the reading. -/
theorem decision_temporalPermit {ι : ImplChoices} {ω : Provider.Providers} {σ : Trace}
    {n : Nat} {p : TimePoint} {a : EntityUID} {φ : Formula} {schema : EventSchema}
    {actions : List ActionDecl} {pr rs : EntityUID} {b : Bool}
    (hσ : σ[n]? = some p)
    (h : (onePolicy a φ schema actions).Admits (onePolicy a φ schema actions).policies ω p pr rs)
    (hb : ∀ ι', ι'.Completes ι → ((onePolicy a φ schema actions).LeafHolds ι' σ n φ ↔ b = true)) :
    ((onePolicy a φ schema actions).authorize ι ω σ n).decision? =
      some (if p.event.action == a && b then .allow else .deny) := by
  have hagree : ∀ ι', ι'.Completes ι → ∀ q ∈ (onePolicy a φ schema actions).policies,
      ((onePolicy a φ schema actions).leaves ι' ω σ n p.event).AgreeOn (constLeaves b)
        q.toExpr.leaves := by
    intro ι' hc q hq
    simp only [onePolicy, List.mem_singleton] at hq
    subst hq
    rw [temporalPermit_leaves]
    intro l hl
    simp only [List.mem_singleton] at hl
    subst hl
    show @decide _ (Classical.propDecidable _) = b
    have := hb ι' hc
    cases b <;> simp_all
  have hresp : (onePolicy a φ schema actions).respond ι ω σ n p.event pr rs =
      some (isAuthorized (constLeaves b) (p.event.request pr rs)
        ((onePolicy a φ schema actions).decisionEntities p.event)
        (onePolicy a φ schema actions).policies) := by
    unfold PolicySet.respond
    rw [supervaluate_congr fun ι' hc => isAuthorized_congr (hagree ι' hc)]
    exact supervaluate_const _
  rw [authorize_of_admits hσ h, hresp]
  simp only [Outcome.decision?]
  rw [response_temporalPermit]
  rfl

/-- **A one-rule temporal permit denies where its leaf fails**, under every completion of the
reading, or where the event is of another action, whether or not the event's data conform. -/
theorem decision_temporalPermit_deny {ι : ImplChoices} {ω : Provider.Providers} {σ : Trace}
    {n : Nat} {p : TimePoint} {a : EntityUID} {φ : Formula} {schema : EventSchema}
    {actions : List ActionDecl}
    (hσ : σ[n]? = some p) (hk : schema.isDecisionKind p.event.kind = true)
    (hno : p.event.action ≠ a ∨
      ∀ ι', ι'.Completes ι → ¬ (onePolicy a φ schema actions).LeafHolds ι' σ n φ) :
    ((onePolicy a φ schema actions).authorize ι ω σ n).decision? = some .deny := by
  have hsome : ((onePolicy a φ schema actions).authorize ι ω σ n).decision?.isSome = true :=
    decideWith_decision?_isSome (P := onePolicy a φ schema actions) hσ hk
  cases hd : ((onePolicy a φ schema actions).authorize ι ω σ n).decision? with
  | none => simp [hd] at hsome
  | some d =>
    cases d with
    | deny => rfl
    | allow =>
      obtain ⟨p', pr, rs, r, hσ', _, hr, hdec⟩ := decideWith_decision?_allow hd
      rw [hσ] at hσ'
      cases hσ'
      obtain ⟨ι₀, h₀⟩ := exists_completes ι
      have hr₀ := supervaluate_eq_some_iff.mp hr ι₀ h₀
      rw [← hr₀, response_temporalPermit] at hdec
      rcases hno with hne | hnl
      · simp [hne] at hdec
      · have : ¬ (onePolicy a φ schema actions).LeafHolds ι₀ σ n φ := hnl ι₀ h₀
        simp [PolicySet.leaves, this] at hdec

/-- A one-rule temporal permit denies every decision event of another action,
whatever its temporal leaf. -/
theorem decision_temporalPermit_other {ι : ImplChoices} {ω : Provider.Providers} {σ : Trace}
    {n : Nat} {p : TimePoint} {a : EntityUID} {φ : Formula} {schema : EventSchema}
    {actions : List ActionDecl}
    (hσ : σ[n]? = some p) (hk : schema.isDecisionKind p.event.kind = true)
    (ha : p.event.action ≠ a) :
    ((onePolicy a φ schema actions).authorize ι ω σ n).decision? = some .deny :=
  decision_temporalPermit_deny hσ hk (.inl ha)

end Dogwood.Examples
