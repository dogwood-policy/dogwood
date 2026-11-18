import Dogwood.Spec.Authorizer
import Cedar.Thm.Data.List.Lemmas

/-!
# Only the leaves a policy contains matter

Evaluation of an expression, and authorization against a list of rules,
depend on a leaf valuation only through the leaves those expressions
contain (`evaluate_congr`, `isAuthorized_congr`).
-/

namespace Dogwood.Thm

open Dogwood.Spec
open Cedar.Spec (Request Entities Attr bindAttr)

/-- Two leaf valuations agree on the leaves `ls`. -/
def _root_.Dogwood.Spec.Leaves.AgreeOn (θ₁ θ₂ : Leaves) (ls : List Leaf) : Prop :=
  ∀ l ∈ ls, match l with
    | .inl φ => θ₁.temporal φ = θ₂.temporal φ
    | .inr c => θ₁.provider c = θ₂.provider c

theorem _root_.Dogwood.Spec.Leaves.AgreeOn.mono {θ₁ θ₂ : Leaves} {ls ls' : List Leaf} (h : θ₁.AgreeOn θ₂ ls)
    (hsub : ∀ l ∈ ls', l ∈ ls) : θ₁.AgreeOn θ₂ ls' :=
  fun l hl => h l (hsub l hl)

theorem mem_leavesList {x : Expr} {xs : List Expr} (hx : x ∈ xs) :
    ∀ l ∈ x.leaves, l ∈ Expr.leavesList xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    intro l hl
    simp only [Expr.leavesList, List.mem_append]
    cases List.mem_cons.mp hx with
    | inl h => exact Or.inl (h ▸ hl)
    | inr h => exact Or.inr (ih h l hl)

theorem mem_leavesRecord {ax : Attr × Expr} {axs : List (Attr × Expr)} (hax : ax ∈ axs) :
    ∀ l ∈ ax.2.leaves, l ∈ Expr.leavesRecord axs := by
  induction axs with
  | nil => simp at hax
  | cons ay ays ih =>
    intro l hl
    obtain ⟨a, y⟩ := ay
    simp only [Expr.leavesRecord, List.mem_append]
    cases List.mem_cons.mp hax with
    | inl h => subst h; exact Or.inl hl
    | inr h => exact Or.inr (ih h l hl)

private theorem mapM_congr' {α β ε : Type} (f g : α → Except ε β) (xs : List α)
    (h : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, h x (by simp)]
    rw [ih (fun y hy => h y (by simp [hy]))]

theorem evaluate_congr (x : Expr) (θ₁ θ₂ : Leaves) (req : Request) (es : Entities)
    (h : θ₁.AgreeOn θ₂ x.leaves) : evaluate θ₁ x req es = evaluate θ₂ x req es := by
  match x with
  | .lit _ => simp only [evaluate]
  | .var v => cases v <;> simp only [evaluate]
  | .ite a b c =>
    have ha := evaluate_congr a θ₁ θ₂ req es (h.mono fun l hl => by simp [Expr.leaves, hl])
    have hb := evaluate_congr b θ₁ θ₂ req es (h.mono fun l hl => by simp [Expr.leaves, hl])
    have hc := evaluate_congr c θ₁ θ₂ req es (h.mono fun l hl => by simp [Expr.leaves, hl])
    simp only [evaluate, ha, hb, hc]
  | .and a b =>
    have ha := evaluate_congr a θ₁ θ₂ req es (h.mono fun l hl => by simp [Expr.leaves, hl])
    have hb := evaluate_congr b θ₁ θ₂ req es (h.mono fun l hl => by simp [Expr.leaves, hl])
    simp only [evaluate, ha, hb]
  | .or a b =>
    have ha := evaluate_congr a θ₁ θ₂ req es (h.mono fun l hl => by simp [Expr.leaves, hl])
    have hb := evaluate_congr b θ₁ θ₂ req es (h.mono fun l hl => by simp [Expr.leaves, hl])
    simp only [evaluate, ha, hb]
  | .unaryApp _ a =>
    have ha := evaluate_congr a θ₁ θ₂ req es (h.mono fun l hl => by simp [Expr.leaves, hl])
    simp only [evaluate, ha]
  | .binaryApp _ a b =>
    have ha := evaluate_congr a θ₁ θ₂ req es (h.mono fun l hl => by simp [Expr.leaves, hl])
    have hb := evaluate_congr b θ₁ θ₂ req es (h.mono fun l hl => by simp [Expr.leaves, hl])
    simp only [evaluate, ha, hb]
  | .getAttr a _ =>
    have ha := evaluate_congr a θ₁ θ₂ req es (h.mono fun l hl => by simp [Expr.leaves, hl])
    simp only [evaluate, ha]
  | .hasAttr a _ =>
    have ha := evaluate_congr a θ₁ θ₂ req es (h.mono fun l hl => by simp [Expr.leaves, hl])
    simp only [evaluate, ha]
  | .extHasAttr a _ _ =>
    have ha := evaluate_congr a θ₁ θ₂ req es (h.mono fun l hl => by simp [Expr.leaves, hl])
    simp only [evaluate, ha]
  | .set xs =>
    simp only [evaluate]
    rw [List.mapM₁_eq_mapM (evaluate θ₁ · req es), List.mapM₁_eq_mapM (evaluate θ₂ · req es),
      mapM_congr' _ _ xs fun x hx => evaluate_congr x θ₁ θ₂ req es
        (h.mono fun l hl => by simpa [Expr.leaves] using mem_leavesList hx l hl)]
  | .call _ xs =>
    simp only [evaluate]
    rw [List.mapM₁_eq_mapM (evaluate θ₁ · req es), List.mapM₁_eq_mapM (evaluate θ₂ · req es),
      mapM_congr' _ _ xs fun x hx => evaluate_congr x θ₁ θ₂ req es
        (h.mono fun l hl => by simpa [Expr.leaves] using mem_leavesList hx l hl)]
  | .record axs =>
    simp only [evaluate]
    rw [List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => bindAttr ax.fst (evaluate θ₁ ax.snd req es)),
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => bindAttr ax.fst (evaluate θ₂ ax.snd req es)),
      mapM_congr' (fun (ax : Attr × Expr) => bindAttr ax.fst (evaluate θ₁ ax.snd req es))
        (fun (ax : Attr × Expr) => bindAttr ax.fst (evaluate θ₂ ax.snd req es)) axs
        fun ax hax => by
          rw [evaluate_congr ax.snd θ₁ θ₂ req es
            (h.mono fun l hl => by simpa [Expr.leaves] using mem_leavesRecord hax l hl)]]
  | .temporal φ =>
    have hφ := h (.inl φ) (by simp [Expr.leaves])
    simp only at hφ
    simp only [evaluate, hφ]
  | .provider c =>
    have hc := h (.inr c) (by simp [Expr.leaves])
    simp only at hc
    simp only [evaluate, hc]
termination_by sizeOf x
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem hx; omega)
    | (have := List.sizeOf_snd_lt_sizeOf_list hax; omega)

theorem isAuthorized_congr {θ₁ θ₂ : Leaves} {req : Request} {es : Entities} {ps : Policies}
    (h : ∀ p ∈ ps, θ₁.AgreeOn θ₂ p.toExpr.leaves) :
    isAuthorized θ₁ req es ps = isAuthorized θ₂ req es ps := by
  have hsat : ∀ p ∈ ps, satisfied θ₁ p req es = satisfied θ₂ p req es := fun p hp => by
    simp only [satisfied, evaluate_congr p.toExpr θ₁ θ₂ req es (h p hp)]
  have herr : ∀ p ∈ ps, hasError θ₁ p req es = hasError θ₂ p req es := fun p hp => by
    simp only [hasError, evaluate_congr p.toExpr θ₁ θ₂ req es (h p hp)]
  have heff : ∀ eff, satisfiedPolicies θ₁ eff ps req es = satisfiedPolicies θ₂ eff ps req es :=
    fun eff => by
      simp only [satisfiedPolicies]
      congr 1
      exact Cedar.List.filterMap_congr fun p hp => by simp only [satisfiedWithEffect, hsat p hp]
  have herrs : errorPolicies θ₁ ps req es = errorPolicies θ₂ ps req es := by
    simp only [errorPolicies]
    congr 1
    exact Cedar.List.filterMap_congr fun p hp => by simp only [errored, herr p hp]
  simp only [isAuthorized, heff, herrs]

end Dogwood.Thm

/-! ## Rules with leaf valuations of their own -/

namespace Dogwood.Thm

open Dogwood.Spec
open Cedar.Spec (Request Entities)

/-- With one leaf valuation for every rule, `isAuthorizedEach` is `isAuthorized`. -/
theorem isAuthorizedEach_const (req : Request) (es : Entities) (θ : Leaves) (ps : Policies) :
    isAuthorizedEach req es (ps.map fun p => (p, θ)) = isAuthorized θ req es ps := by
  simp [isAuthorizedEach, isAuthorized, satisfiedPolicies, errorPolicies, List.filterMap_map,
    Function.comp_def]

/-- Rules each evaluated under their own valuation, as under `θ₀`, decide as under `θ₀`. -/
theorem isAuthorizedEach_eq {rules : List (Policy × Leaves)} {θ₀ : Leaves} {req : Request}
    {es : Entities}
    (h : ∀ r ∈ rules, evaluate r.2 r.1.toExpr req es = evaluate θ₀ r.1.toExpr req es) :
    isAuthorizedEach req es rules = isAuthorized θ₀ req es (rules.map (·.1)) := by
  have hsat : ∀ eff, rules.filterMap (fun r => satisfiedWithEffect r.2 eff r.1 req es) =
      (rules.map (·.1)).filterMap (fun p => satisfiedWithEffect θ₀ eff p req es) := fun eff => by
    rw [List.filterMap_map]
    exact Cedar.List.filterMap_congr fun r hr => by
      simp only [Function.comp, satisfiedWithEffect, satisfied, h r hr] <;> rfl
  have herr : rules.filterMap (fun r => errored r.2 r.1 req es) =
      (rules.map (·.1)).filterMap (fun p => errored θ₀ p req es) := by
    rw [List.filterMap_map]
    exact Cedar.List.filterMap_congr fun r hr => by
      simp only [Function.comp, errored, hasError, h r hr] <;> rfl
  simp only [isAuthorizedEach, isAuthorized, satisfiedPolicies, errorPolicies, hsat, herr] <;> rfl

end Dogwood.Thm
