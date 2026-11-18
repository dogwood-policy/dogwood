import Dogwood.Thm.Decision
import Cedar.Thm.Data.List.Lemmas

/-!
# Dogwood conservatively extends Cedar

A Cedar expression, policy, or policy set, read as Dogwood (`Expr.ofCedar`,
`Policy.ofCedar`), means what it means in Cedar: Dogwood's evaluator and
authorizer agree with Cedar's whatever the leaf valuation. At the level of a
trace, a policy set without temporal conditions or providers decides every
decision event that passes the decision's checks (`PolicySet.Admits`) exactly as
Cedar decides that event's request.
-/

namespace Dogwood.Thm

open Dogwood.Spec
open Cedar.Spec (Request Entities Attr bindAttr)

theorem ofCedarList_eq_map (xs : List Cedar.Spec.Expr) :
    Expr.ofCedarList xs = xs.map Expr.ofCedar := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Expr.ofCedarList, ih]

theorem ofCedarRecord_eq_map (axs : List (Attr × Cedar.Spec.Expr)) :
    Expr.ofCedarRecord axs = axs.map (fun ax => (ax.1, Expr.ofCedar ax.2)) := by
  induction axs with
  | nil => rfl
  | cons ax axs ih => obtain ⟨a, x⟩ := ax; simp [Expr.ofCedarRecord, ih]

private theorem mapM_map_congr {α β γ ε : Type} (f : α → β) (g : β → Except ε γ)
    (h : α → Except ε γ) (xs : List α) (hfg : ∀ x ∈ xs, g (f x) = h x) :
    (xs.map f).mapM g = xs.mapM h := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.mapM_cons, hfg x (by simp)]
    rw [ih (fun y hy => hfg y (by simp [hy]))]

theorem evaluate_ofCedar (θ : Leaves) (x : Cedar.Spec.Expr) (req : Request) (es : Entities) :
    evaluate θ (Expr.ofCedar x) req es = Cedar.Spec.evaluate x req es := by
  match x with
  | .lit _ => simp [Expr.ofCedar, evaluate, Cedar.Spec.evaluate]
  | .var v => cases v <;> simp [Expr.ofCedar, evaluate, Cedar.Spec.evaluate]
  | .ite c t f =>
    simp only [Expr.ofCedar, evaluate, Cedar.Spec.evaluate,
      evaluate_ofCedar θ c, evaluate_ofCedar θ t, evaluate_ofCedar θ f]
  | .and a b =>
    simp only [Expr.ofCedar, evaluate, Cedar.Spec.evaluate,
      evaluate_ofCedar θ a, evaluate_ofCedar θ b]
  | .or a b =>
    simp only [Expr.ofCedar, evaluate, Cedar.Spec.evaluate,
      evaluate_ofCedar θ a, evaluate_ofCedar θ b]
  | .unaryApp _ a =>
    simp only [Expr.ofCedar, evaluate, Cedar.Spec.evaluate, evaluate_ofCedar θ a]
  | .binaryApp _ a b =>
    simp only [Expr.ofCedar, evaluate, Cedar.Spec.evaluate,
      evaluate_ofCedar θ a, evaluate_ofCedar θ b]
  | .getAttr a _ =>
    simp only [Expr.ofCedar, evaluate, Cedar.Spec.evaluate, evaluate_ofCedar θ a]
  | .extHasAttr a _ _ =>
    simp only [Expr.ofCedar, evaluate, Cedar.Spec.evaluate, evaluate_ofCedar θ a]
  | .hasAttr a _ =>
    simp only [Expr.ofCedar, evaluate, Cedar.Spec.evaluate, evaluate_ofCedar θ a]
  | .set xs =>
    simp only [Expr.ofCedar, evaluate, Cedar.Spec.evaluate]
    rw [List.mapM₁_eq_mapM (evaluate θ · req es), List.mapM₁_eq_mapM (Cedar.Spec.evaluate · req es),
      ofCedarList_eq_map,
      mapM_map_congr _ _ _ xs (fun x hx => evaluate_ofCedar θ x req es)]
  | .record axs =>
    simp only [Expr.ofCedar, evaluate, Cedar.Spec.evaluate]
    rw [List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => bindAttr ax.fst (evaluate θ ax.snd req es)),
      List.mapM₂_eq_mapM
        (fun (ax : Attr × Cedar.Spec.Expr) => bindAttr ax.fst (Cedar.Spec.evaluate ax.snd req es)),
      ofCedarRecord_eq_map,
      mapM_map_congr (fun ax => (ax.1, Expr.ofCedar ax.2))
        (fun ax => bindAttr ax.fst (evaluate θ ax.snd req es))
        (fun ax => bindAttr ax.fst (Cedar.Spec.evaluate ax.snd req es)) axs
        (fun ax hax => by simp only [evaluate_ofCedar θ ax.snd req es])]
  | .call _ xs =>
    simp only [Expr.ofCedar, evaluate, Cedar.Spec.evaluate]
    rw [List.mapM₁_eq_mapM (evaluate θ · req es), List.mapM₁_eq_mapM (Cedar.Spec.evaluate · req es),
      ofCedarList_eq_map,
      mapM_map_congr _ _ _ xs (fun x hx => evaluate_ofCedar θ x req es)]
termination_by sizeOf x
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem hx; omega)
    | (have := List.sizeOf_snd_lt_sizeOf_list hax; omega)

private def Condition.ofCedar (c : Cedar.Spec.Condition) : Condition := ⟨c.kind, Expr.ofCedar c.body⟩

private theorem Condition.toExpr_ofCedar (c : Cedar.Spec.Condition) :
    (Condition.ofCedar c).toExpr = Expr.ofCedar c.toExpr := by
  obtain ⟨kind, body⟩ := c
  cases kind <;> rfl

private theorem foldl_ofCedar (cs : List Cedar.Spec.Condition) (acc : Cedar.Spec.Expr) :
    (cs.map Condition.ofCedar).foldl (fun expr c => .and c.toExpr expr) (Expr.ofCedar acc) =
    Expr.ofCedar (cs.foldl (fun expr c => .and c.toExpr expr) acc) := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [← ih]
    simp [Condition.toExpr_ofCedar, Expr.ofCedar]

theorem Conditions.toExpr_ofCedar (cs : Cedar.Spec.Conditions) :
    Conditions.toExpr (cs.map fun c => ⟨c.kind, Expr.ofCedar c.body⟩) =
    Expr.ofCedar (Cedar.Spec.Conditions.toExpr cs) := by
  have h : (cs.map fun c => (⟨c.kind, Expr.ofCedar c.body⟩ : Condition)) = cs.map Condition.ofCedar := rfl
  rw [h]
  unfold Conditions.toExpr Cedar.Spec.Conditions.toExpr
  rw [← List.map_reverse]
  cases cs.reverse with
  | nil => rfl
  | cons c cs =>
    simp only [List.map_cons]
    rw [Condition.toExpr_ofCedar, foldl_ofCedar]

theorem Policy.toExpr_ofCedar (p : Cedar.Spec.Policy) :
    (Policy.ofCedar p).toExpr = Expr.ofCedar p.toExpr := by
  simp only [Policy.toExpr, Policy.ofCedar, Cedar.Spec.Policy.toExpr, Expr.ofCedar,
    Conditions.toExpr_ofCedar]

theorem satisfied_ofCedar (θ : Leaves) (p : Cedar.Spec.Policy) (req : Request) (es : Entities) :
    satisfied θ (Policy.ofCedar p) req es = Cedar.Spec.satisfied p req es := by
  simp only [satisfied, Cedar.Spec.satisfied, Policy.toExpr_ofCedar, evaluate_ofCedar]

theorem hasError_ofCedar (θ : Leaves) (p : Cedar.Spec.Policy) (req : Request) (es : Entities) :
    hasError θ (Policy.ofCedar p) req es = Cedar.Spec.hasError p req es := by
  simp only [hasError, Cedar.Spec.hasError, Policy.toExpr_ofCedar, evaluate_ofCedar]
  cases Cedar.Spec.evaluate p.toExpr req es <;> rfl

/-- The per-request authorizer, on Cedar policies, is Cedar's. -/
theorem isAuthorized_ofCedar (θ : Leaves) (req : Request) (es : Entities)
    (ps : Cedar.Spec.Policies) :
    isAuthorized θ req es (ps.map Policy.ofCedar) = Cedar.Spec.isAuthorized req es ps := by
  simp only [isAuthorized, Cedar.Spec.isAuthorized, satisfiedPolicies, Cedar.Spec.satisfiedPolicies,
    errorPolicies, Cedar.Spec.errorPolicies, List.filterMap_map, Function.comp_def,
    satisfiedWithEffect, Cedar.Spec.satisfiedWithEffect, errored, Cedar.Spec.errored,
    satisfied_ofCedar, hasError_ofCedar]
  rfl

mutual

/-- A Cedar expression read as Dogwood has no leaves. -/
theorem leaves_ofCedar : (x : Cedar.Spec.Expr) → (Expr.ofCedar x).leaves = []
  | .lit _ | .var _ => rfl
  | .ite c t f => by simp [Expr.ofCedar, Expr.leaves, leaves_ofCedar c, leaves_ofCedar t,
      leaves_ofCedar f]
  | .and a b | .or a b | .binaryApp _ a b => by
    simp [Expr.ofCedar, Expr.leaves, leaves_ofCedar a, leaves_ofCedar b]
  | .unaryApp _ a | .getAttr a _ | .hasAttr a _ | .extHasAttr a _ _ => by
    simp [Expr.ofCedar, Expr.leaves, leaves_ofCedar a]
  | .set xs | .call _ xs => by simp [Expr.ofCedar, Expr.leaves, leavesList_ofCedarList xs]
  | .record axs => by simp [Expr.ofCedar, Expr.leaves, leavesRecord_ofCedarRecord axs]

theorem leavesList_ofCedarList : (xs : List Cedar.Spec.Expr) →
    Expr.leavesList (Expr.ofCedarList xs) = []
  | [] => rfl
  | x :: xs => by
    simp [Expr.ofCedarList, Expr.leavesList, leaves_ofCedar x, leavesList_ofCedarList xs]

theorem leavesRecord_ofCedarRecord : (axs : List (Attr × Cedar.Spec.Expr)) →
    Expr.leavesRecord (Expr.ofCedarRecord axs) = []
  | [] => rfl
  | (_, x) :: axs => by
    simp [Expr.ofCedarRecord, Expr.leavesRecord, leaves_ofCedar x, leavesRecord_ofCedarRecord axs]

end

/-- Cedar policies invoke no information provider. -/
theorem providerCalls_ofCedar (ps : Cedar.Spec.Policies) :
    Policies.providerCalls (ps.map Policy.ofCedar) = [] := by
  simp [Policies.providerCalls, Policy.toExpr_ofCedar, leaves_ofCedar]

/-- **Conservative extension.** A Dogwood policy set whose rules are Cedar
policies — no temporal condition, no provider — decides each decision event
that passes the decision's checks (`PolicySet.Admits`) exactly as Cedar decides
the event's request, against the decision's entity store, under every reading. -/
theorem authorize_ofCedar (ι : Temporal.ImplChoices) (P : PolicySet) (ω : Provider.Providers)
    (σ : Trace) (n : Nat) (ps : Cedar.Spec.Policies) (hP : P.policies = ps.map Policy.ofCedar)
    (p : TimePoint) (hσ : σ[n]? = some p) (pr rs : Cedar.Spec.EntityUID)
    (h : P.Admits P.policies ω p pr rs) :
    P.authorize ι ω σ n =
      .decided (Cedar.Spec.isAuthorized (p.event.request pr rs)
        (P.decisionEntities p.event) ps) := by
  have hresp : P.respond ι ω σ n p.event pr rs =
      some (Cedar.Spec.isAuthorized (p.event.request pr rs) (P.decisionEntities p.event) ps) := by
    unfold PolicySet.respond
    simp only [hP, isAuthorized_ofCedar]
    exact supervaluate_const _
  rw [authorize_of_admits hσ h, hresp]

/-- Cedar policies pass the provider checks of a decision whatever the providers. -/
theorem providers_ofCedar (P : PolicySet) (ω : Provider.Providers) (ps : Cedar.Spec.Policies)
    (e : Event) :
    Policies.providersFail (ps.map Policy.ofCedar) ω e = false ∧
      P.providerOutputsConform (ps.map Policy.ofCedar) ω e = true :=
  ⟨providersFail_of_providerCalls_nil (providerCalls_ofCedar ps) ω e,
    providerOutputsConform_of_providerCalls_nil (providerCalls_ofCedar ps) P ω e⟩

end Dogwood.Thm
