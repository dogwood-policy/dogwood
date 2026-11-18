import Dogwood.Thm.Leaves
import Dogwood.Thm.Conservative
import Dogwood.Thm.ExtHasAttr

/-!
# A leaf matters only where its facts hold

The facts of a leaf's position (`Expr.leafFacts`) are the `has` tests Cedar has evaluated to
`true` before it reads the leaf. So the evaluation of an expression depends on a leaf's value only
where the leaf's facts hold (`evaluate_congr_facts`): two leaf valuations that agree on every leaf
whose facts hold, at a request and entity store, evaluate the expression alike there. A rule's
response therefore depends on a temporal leaf only where its facts hold
(`isAuthorized_congr_facts`), which is where the soundness of the temporal part
(`Dogwood.Thm.leaves_sound`) applies.

A fact holds (`Guard.HoldsIn`) when Cedar evaluates its `has` test to `true`
(`Guard.expr`).
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Value Attr Request Entities Var bindAttr)

/-! ## Facts as Cedar expressions -/

/-- The attribute chain `root.p₁.….pₙ`. -/
def attrChainExpr (root : Var) : Path → Cedar.Spec.Expr
  | [] => .var root
  | p => (p.foldl (fun x a => Cedar.Spec.Expr.getAttr x a) (.var root))

/-- The `has` test of a guard: `root.p₁.….pₙ₋₁ has pₙ`. -/
def _root_.Dogwood.Spec.Temporal.Guard.expr : Guard → Cedar.Spec.Expr
  | .context p => test .context p
  | .scope .principal p => test .principal p
  | .scope .resource p => test .resource p
where
  test (root : Var) (p : Path) : Cedar.Spec.Expr :=
    match p.getLast? with
    | some a => .hasAttr (attrChainExpr root p.dropLast) a
    | none => .lit (.bool true)

/-- **A fact holds** at a request and entity store when Cedar evaluates its `has` test to
`true`. -/
def _root_.Dogwood.Spec.Temporal.Guard.HoldsIn (req : Request) (es : Entities) (g : Guard) : Prop :=
  Cedar.Spec.evaluate g.expr req es = .ok (.prim (.bool true))

theorem attrChain_spec : {x : Expr} → {v : Var} → {p : Path} → Expr.attrChain? x = some (v, p) →
    x = Expr.ofCedar (attrChainExpr v p)
  | .var v', v, p, h => by
    simp only [Expr.attrChain?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .getAttr y a, v, p, h => by
    simp only [Expr.attrChain?, Option.map_eq_some_iff] at h
    obtain ⟨⟨v', q⟩, hq, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [attrChain_spec hq]
    cases q with
    | nil => rfl
    | cons b q => simp [attrChainExpr, List.foldl_append, Expr.ofCedar]
  | .lit _, _, _, h | .ite _ _ _, _, _, h | .and _ _, _, _, h | .or _ _, _, _, h
  | .unaryApp _ _, _, _, h | .binaryApp _ _ _, _, _, h | .hasAttr _ _, _, _, h
  | .extHasAttr _ _ _, _, _, h
  | .set _, _, _, h | .record _, _, _, h | .call _ _, _, _, h | .temporal _, _, _, h
  | .provider _, _, _, h => by simp [Expr.attrChain?] at h

theorem test_append (root : Var) (p : Path) (a : Attr) :
    Guard.expr.test root (p ++ [a]) = .hasAttr (attrChainExpr root p) a := by
  simp [Guard.expr.test]

/-- A `has` test that evaluates to `true` establishes its fact. -/
theorem hasFact_holds {θ : Leaves} {req : Request} {es : Entities} {x : Expr} {a : Attr}
    {g : Guard} (hg : Expr.hasFact? x a = some g)
    (h : evaluate θ (.hasAttr x a) req es = .ok (.prim (.bool true))) : g.HoldsIn req es := by
  unfold Expr.hasFact? at hg
  cases hc : Expr.attrChain? x with
  | none => rw [hc] at hg; cases hg
  | some vp =>
    obtain ⟨v, p⟩ := vp
    rw [hc] at hg
    have hx := attrChain_spec hc
    subst hx
    have heval : Cedar.Spec.evaluate (.hasAttr (attrChainExpr v p) a) req es =
        .ok (.prim (.bool true)) := by
      rw [← evaluate_ofCedar θ]
      exact h
    cases v with
    | context =>
      simp only [Option.some.injEq] at hg
      subst hg
      simp only [Guard.HoldsIn, Guard.expr, test_append]
      exact heval
    | principal =>
      simp only [Option.some.injEq] at hg
      subst hg
      simp only [Guard.HoldsIn, Guard.expr, test_append]
      exact heval
    | resource =>
      simp only [Option.some.injEq] at hg
      subst hg
      simp only [Guard.HoldsIn, Guard.expr, test_append]
      exact heval
    | action => simp at hg

theorem as_bool_true {r : Cedar.Spec.Result Value} (h : r.as Bool = .ok true) :
    r = .ok (.prim (.bool true)) := by
  cases r with
  | error e => cases h
  | ok v =>
    simp only [Cedar.Spec.Result.as] at h
    cases v with
    | prim p =>
      cases p with
      | bool b =>
        simp only [Coe.coe, Cedar.Spec.Value.asBool] at h
        cases h
        rfl
      | _ => cases h
    | _ => cases h

/-- An extended `has` that evaluates to `true` establishes the fact of each prefix of its path. -/
theorem extHasFacts_hold {θ : Leaves} {req : Request} {es : Entities} :
    ∀ (as : List Attr) (y : Expr) (a : Attr),
      evaluate θ (.extHasAttr y a as) req es = .ok (.prim (.bool true)) →
      ∀ g ∈ Expr.extHasFacts y a as, g.HoldsIn req es
  | [], y, a, h, g, hg => by
    simp only [Expr.extHasFacts, Option.mem_toList] at hg
    refine hasFact_holds (θ := θ) hg ?_
    simp only [evaluate, Cedar.Spec.hasAttrs] at h ⊢
    simp only [hasAttrs_loop_single] at h
    exact h
  | b :: bs, y, a, h, g, hg => by
    simp only [Expr.extHasFacts, List.mem_append, Option.mem_toList] at hg
    simp only [evaluate, Cedar.Spec.hasAttrs] at h
    cases hy : evaluate θ y req es with
    | error e => rw [hy] at h; cases h
    | ok v =>
      rw [hy] at h
      simp only [Except.bind_ok] at h
      obtain ⟨hhas, w, hget, hrest⟩ := hasAttrs_loop_cons_true h
      rcases hg with hg | hg
      · exact hasFact_holds (θ := θ) hg (by simp only [evaluate, hy, Except.bind_ok]; exact hhas)
      · refine extHasFacts_hold (θ := θ) bs (.getAttr y a) b ?_ g hg
        simp only [evaluate, hy, Except.bind_ok, hget, Cedar.Spec.hasAttrs]
        exact hrest

/-- **An expression that evaluates to `true` establishes its facts.** -/
theorem facts_hold {θ : Leaves} {req : Request} {es : Entities} :
    ∀ (x : Expr), evaluate θ x req es = .ok (.prim (.bool true)) → ∀ g ∈ x.facts, g.HoldsIn req es
  | .hasAttr y a, h, g, hg => by
    simp only [Expr.facts, Option.mem_toList] at hg
    exact hasFact_holds hg h
  | .extHasAttr y a as, h, g, hg => by
    simp only [Expr.facts] at hg
    exact extHasFacts_hold as y a h g hg
  | .and a b, h, g, hg => by
    simp only [Expr.facts, List.mem_append] at hg
    simp only [evaluate] at h
    cases ha : (evaluate θ a req es).as Bool with
    | error e => simp [ha] at h
    | ok b₁ =>
      cases b₁ with
      | false => simp [ha] at h
      | true =>
        cases hb : (evaluate θ b req es).as Bool with
        | error e => simp [ha, hb] at h
        | ok b₂ =>
          cases b₂ with
          | false => simp [ha, hb] at h
          | true =>
            rcases hg with hg | hg
            · exact facts_hold a (as_bool_true ha) g hg
            · exact facts_hold b (as_bool_true hb) g hg
  | .lit _, _, _, hg | .var _, _, _, hg | .ite _ _ _, _, _, hg | .or _ _, _, _, hg
  | .unaryApp _ _, _, _, hg | .binaryApp _ _ _, _, _, hg | .getAttr _ _, _, _, hg
  | .set _, _, _, hg | .record _, _, _, hg | .call _ _, _, _, hg | .temporal _, _, _, hg
  | .provider _, _, _, hg => by simp [Expr.facts] at hg

/-! ## Congruence -/

/-- Two leaf valuations agree on a leaf. -/
def LeafAgree (θ₁ θ₂ : Leaves) : Leaf → Prop
  | .inl φ => θ₁.temporal φ = θ₂.temporal φ
  | .inr c => θ₁.provider c = θ₂.provider c

private theorem mapM_congr'' {α β ε : Type} (f g : α → Except ε β) (xs : List α)
    (h : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, h x (by simp)]
    rw [ih (fun y hy => h y (by simp [hy]))]

theorem mem_leafFactsList {F : List Guard} {x : Expr} {xs : List Expr} (hx : x ∈ xs) :
    ∀ lf ∈ x.leafFacts F, lf ∈ Expr.leafFactsList F xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    intro lf hlf
    simp only [Expr.leafFactsList, List.mem_append]
    cases List.mem_cons.mp hx with
    | inl h => exact Or.inl (h ▸ hlf)
    | inr h => exact Or.inr (ih h lf hlf)

theorem mem_leafFactsRecord {F : List Guard} {ax : Attr × Expr} {axs : List (Attr × Expr)}
    (hax : ax ∈ axs) : ∀ lf ∈ ax.2.leafFacts F, lf ∈ Expr.leafFactsRecord F axs := by
  induction axs with
  | nil => simp at hax
  | cons ay ays ih =>
    intro lf hlf
    obtain ⟨a, y⟩ := ay
    simp only [Expr.leafFactsRecord, List.mem_append]
    cases List.mem_cons.mp hax with
    | inl h => subst h; exact Or.inl hlf
    | inr h => exact Or.inr (ih h lf hlf)

/-- **Evaluation depends on a leaf only where its facts hold.** Two leaf valuations that agree on
every leaf whose facts hold evaluate the expression alike, when the facts established before it
hold. -/
theorem evaluate_congr_facts (θ₁ θ₂ : Leaves) (req : Request) (es : Entities) (x : Expr)
    (F : List Guard) (hF : ∀ g ∈ F, g.HoldsIn req es)
    (h : ∀ l F', (l, F') ∈ x.leafFacts F → (∀ g ∈ F', g.HoldsIn req es) → LeafAgree θ₁ θ₂ l) :
    evaluate θ₁ x req es = evaluate θ₂ x req es := by
  match x with
  | .lit _ => simp only [evaluate]
  | .var v => cases v <;> simp only [evaluate]
  | .ite a b c =>
    have ha := evaluate_congr_facts θ₁ θ₂ req es a F hF
      (fun l F' hm => h l F' (by simp [Expr.leafFacts, hm]))
    have hc := evaluate_congr_facts θ₁ θ₂ req es c F hF
      (fun l F' hm => h l F' (by simp [Expr.leafFacts, hm]))
    simp only [evaluate]
    rw [← ha]
    cases hab : (evaluate θ₁ a req es).as Bool with
    | error e => rfl
    | ok b₁ =>
      cases b₁ with
      | false => simp [hc]
      | true =>
        have hfa := facts_hold a (as_bool_true hab)
        have hb := evaluate_congr_facts θ₁ θ₂ req es b (F ++ a.facts)
          (fun g hg => by
            rcases List.mem_append.mp hg with hg | hg
            · exact hF g hg
            · exact hfa g hg)
          (fun l F' hm => h l F' (by simp [Expr.leafFacts, hm]))
        simp [hb]
  | .and a b =>
    have ha := evaluate_congr_facts θ₁ θ₂ req es a F hF
      (fun l F' hm => h l F' (by simp [Expr.leafFacts, hm]))
    simp only [evaluate]
    rw [← ha]
    cases hab : (evaluate θ₁ a req es).as Bool with
    | error e => rfl
    | ok b₁ =>
      cases b₁ with
      | false => rfl
      | true =>
        have hfa := facts_hold a (as_bool_true hab)
        have hb := evaluate_congr_facts θ₁ θ₂ req es b (F ++ a.facts)
          (fun g hg => by
            rcases List.mem_append.mp hg with hg | hg
            · exact hF g hg
            · exact hfa g hg)
          (fun l F' hm => h l F' (by simp [Expr.leafFacts, hm]))
        simp [hb]
  | .or a b =>
    have ha := evaluate_congr_facts θ₁ θ₂ req es a F hF
      (fun l F' hm => h l F' (by simp [Expr.leafFacts, hm]))
    have hb := evaluate_congr_facts θ₁ θ₂ req es b F hF
      (fun l F' hm => h l F' (by simp [Expr.leafFacts, hm]))
    simp only [evaluate, ha, hb]
  | .unaryApp _ a =>
    have ha := evaluate_congr_facts θ₁ θ₂ req es a F hF
      (fun l F' hm => h l F' (by simp [Expr.leafFacts, hm]))
    simp only [evaluate, ha]
  | .binaryApp _ a b =>
    have ha := evaluate_congr_facts θ₁ θ₂ req es a F hF
      (fun l F' hm => h l F' (by simp [Expr.leafFacts, hm]))
    have hb := evaluate_congr_facts θ₁ θ₂ req es b F hF
      (fun l F' hm => h l F' (by simp [Expr.leafFacts, hm]))
    simp only [evaluate, ha, hb]
  | .getAttr a _ =>
    have ha := evaluate_congr_facts θ₁ θ₂ req es a F hF
      (fun l F' hm => h l F' (by simp [Expr.leafFacts, hm]))
    simp only [evaluate, ha]
  | .hasAttr a _ =>
    have ha := evaluate_congr_facts θ₁ θ₂ req es a F hF
      (fun l F' hm => h l F' (by simp [Expr.leafFacts, hm]))
    simp only [evaluate, ha]
  | .extHasAttr a _ _ =>
    have ha := evaluate_congr_facts θ₁ θ₂ req es a F hF
      (fun l F' hm => h l F' (by simp [Expr.leafFacts, hm]))
    simp only [evaluate, ha]
  | .set xs =>
    simp only [evaluate]
    rw [List.mapM₁_eq_mapM (evaluate θ₁ · req es), List.mapM₁_eq_mapM (evaluate θ₂ · req es),
      mapM_congr'' _ _ xs fun x hx => evaluate_congr_facts θ₁ θ₂ req es x F hF
        (fun l F' hm => h l F' (by simpa [Expr.leafFacts] using mem_leafFactsList hx _ hm))]
  | .call _ xs =>
    simp only [evaluate]
    rw [List.mapM₁_eq_mapM (evaluate θ₁ · req es), List.mapM₁_eq_mapM (evaluate θ₂ · req es),
      mapM_congr'' _ _ xs fun x hx => evaluate_congr_facts θ₁ θ₂ req es x F hF
        (fun l F' hm => h l F' (by simpa [Expr.leafFacts] using mem_leafFactsList hx _ hm))]
  | .record axs =>
    simp only [evaluate]
    rw [List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => bindAttr ax.fst (evaluate θ₁ ax.snd req es)),
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => bindAttr ax.fst (evaluate θ₂ ax.snd req es)),
      mapM_congr'' (fun (ax : Attr × Expr) => bindAttr ax.fst (evaluate θ₁ ax.snd req es))
        (fun (ax : Attr × Expr) => bindAttr ax.fst (evaluate θ₂ ax.snd req es)) axs
        fun ax hax => by
          rw [evaluate_congr_facts θ₁ θ₂ req es ax.snd F hF
            (fun l F' hm => h l F' (by simpa [Expr.leafFacts] using mem_leafFactsRecord hax _ hm))]]
  | .temporal φ =>
    have hφ := h (.inl φ) F (by simp [Expr.leafFacts]) hF
    simp only [LeafAgree] at hφ
    simp only [evaluate, hφ]
  | .provider c =>
    have hc := h (.inr c) F (by simp [Expr.leafFacts]) hF
    simp only [LeafAgree] at hc
    simp only [evaluate, hc]
termination_by sizeOf x
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem hx; omega)
    | (have := List.sizeOf_snd_lt_sizeOf_list hax; omega)

/-- **A response depends on a leaf only where its facts hold.** Two leaf valuations that agree,
on every rule, on every leaf whose facts hold at the request, give the same response. -/
theorem isAuthorized_congr_facts {θ₁ θ₂ : Leaves} {req : Request} {es : Entities} {ps : Policies}
    (h : ∀ p ∈ ps, ∀ l F, (l, F) ∈ p.toExpr.leafFacts [] → (∀ g ∈ F, g.HoldsIn req es) →
      LeafAgree θ₁ θ₂ l) :
    isAuthorized θ₁ req es ps = isAuthorized θ₂ req es ps := by
  have he : ∀ p ∈ ps, evaluate θ₁ p.toExpr req es = evaluate θ₂ p.toExpr req es := fun p hp =>
    evaluate_congr_facts θ₁ θ₂ req es p.toExpr [] (by simp) (h p hp)
  have hsat : ∀ p ∈ ps, satisfied θ₁ p req es = satisfied θ₂ p req es := fun p hp => by
    simp only [satisfied, he p hp]
  have herr : ∀ p ∈ ps, hasError θ₁ p req es = hasError θ₂ p req es := fun p hp => by
    simp only [hasError, he p hp]
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
