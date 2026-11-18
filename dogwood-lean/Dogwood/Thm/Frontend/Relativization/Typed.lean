import Dogwood.Thm.Frontend.Relativization.Mine

/-!
# Well-typed, safe leaves: the executable form, and the orderings of timepoints

Two facts about a temporal leaf that projects to a well-typed, safe formula of the specification:

* **The executable form is the leaf itself** (`unorderFree_of_typed`): typing orders only `Long`s
  and computes only with `Long`s, so `LeafPasses.unorderTimepoints` finds nothing to replace.
* **Ordering timepoints by position changes nothing** (`xsat_ord_iff`, in `Relativization.Ord`):
  the extended relation with `ord = true` means what it means with `ord = false`, for every
  domain of the binders.
  Typing makes the operands of an ordering `Long`s, and safety makes every variable an ordering
  reads one that is restricted by the condition, so it holds a value rather than a timepoint in
  every satisfying assignment (`restricts_coarse`).
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.LeafPasses Surface.Temporal
open Dogwood.Spec (Event Trace TickRate EventSchema)
open Dogwood.Spec.Temporal (Valuation ImplChoices CVal TVal ArgsMatch Formula Aggregate TypingCtx
  Bindings TType Binder BinderType domainNames eqRestricted? valueSide)

/-! ## The executable form of a well-typed leaf -/

/-- The unorder pass's scope and the typing's bindings agree on which names are timepoints. -/
def TpCorr (Γt : TpScope) (Γ : Bindings) : Prop :=
  ∀ x, isTimepoint Γt x = true → Γ.lookup x = some .timepoint

theorem isTimepointVar_of_cedar {C : TypingCtx} {Γt : TpScope} {Γ : Bindings} (hc : TpCorr Γt Γ)
    {t : Surface.Temporal.Term} {t' : Dogwood.Spec.Temporal.Term} (ht : t.toSpec = .ok t')
    {ty : Cedar.Validation.CedarType} (hty : Dogwood.Spec.Temporal.Term.Typed C Γ t' (.cedar ty)) :
    isTimepointVar Γt t = false := by
  cases t with
  | var x =>
    simp only [Surface.Temporal.Term.toSpec, pure_eq_ok] at ht
    subst ht
    cases hty with
    | var hl =>
      cases h : isTimepoint Γt x
      · simpa [isTimepointVar] using h
      · rw [hc x h] at hl; cases hl
  | _ => rfl

theorem computes_of_typed {C : TypingCtx} {Γt : TpScope} {Γ : Bindings} (hc : TpCorr Γt Γ) :
    (t : Surface.Temporal.Term) → {t' : Dogwood.Spec.Temporal.Term} → t.toSpec = .ok t' →
    {τ : TType} → Dogwood.Spec.Temporal.Term.Typed C Γ t' τ → computesWithTimepoint Γt t = false
  | .arith op l r, t', ht, τ, hty => by
    simp only [Surface.Temporal.Term.toSpec, bind_eq_ok, pure_eq_ok] at ht
    obtain ⟨l', hl, r', hr, rfl⟩ := ht
    cases hty with
    | arith h₁ h₂ =>
      simp only [computesWithTimepoint, isTimepointVar_of_cedar hc hl h₁,
        isTimepointVar_of_cedar hc hr h₂, computes_of_typed hc l hl h₁, computes_of_typed hc r hr h₂,
        Bool.or_self]
  | .agg _, _, _, _, _ | .entity _ _, _, _, _, _ | .integer _, _, _, _, _ | .decimal _, _, _, _, _
  | .string _, _, _, _, _ | .bool _, _, _, _, _ | .contextField _, _, _, _, _
  | .scopeField _, _, _, _, _ | .var _, _, _, _, _ | .wildcard, _, _, _, _ | .array _, _, _, _, _
  | .paramRef _, _, _, _, _ | .binderRef _, _, _, _, _ => rfl

theorem lookup_cons_of_ne {b : String × TType} {Γ : Bindings} {x : String} (h : b.1 ≠ x) :
    Bindings.lookup (b :: Γ) x = Γ.lookup x := by
  have : (b.1 == x) = false := by simpa using h
  simp [Bindings.lookup, this]

theorem isTimepoint_cons_of_ne {p : String × Bool} {Γt : TpScope} {x : String} (h : p.1 ≠ x) :
    isTimepoint (p :: Γt) x = isTimepoint Γt x := by
  have : (p.1 == x) = false := by simpa using h
  simp [isTimepoint, this]

theorem binder_sort_ty {ets : Cedar.Validation.EntitySchema} {x : Binder} {b : String × TType}
    (h : Binder.sort? ets x = some b) : b.1 = x.name ∧ (x.ty = .timepoint → b.2 = .timepoint) := by
  unfold Binder.sort? at h
  split at h
  · cases h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨τ, hτ, rfl⟩ := h
    refine ⟨rfl, fun hty => ?_⟩
    rw [hty] at hτ
    simp only [BinderType.sort?, Option.some.injEq] at hτ
    exact hτ.symm

theorem tpCorr_cons {Γt : TpScope} {Γ : Bindings} (hc : TpCorr Γt Γ) {ets : Cedar.Validation.EntitySchema}
    {x : String} {ty : BinderType} {b : String × TType} (hb : Binder.sort? ets ⟨x, ty⟩ = some b) :
    TpCorr (binding ⟨.name x, ty⟩ :: Γt) (b :: Γ) := by
  obtain ⟨hbn, hbt⟩ := binder_sort_ty hb
  intro y hy
  by_cases hyx : x = y
  · subst hyx
    simp only [binding, isTimepoint, List.find?_cons, beq_self_eq_true] at hy
    have hty : ty = .timepoint := by simpa using hy
    have : b = (b.1, b.2) := rfl
    rw [this, hbn, hbt hty]
    simp [Bindings.lookup]
  · rw [isTimepoint_cons_of_ne (by simpa [binding] using hyx)] at hy
    rw [lookup_cons_of_ne (by rw [hbn]; exact hyx)]
    exact hc y hy

theorem mem_mapM_some {α β : Type} {f : α → Option β} : {xs : List α} → {ys : List β} →
    xs.mapM f = some ys → ∀ x ∈ xs, ∃ y ∈ ys, f x = some y
  | [], ys, _, x, hx => by cases hx
  | x₀ :: xs, ys, h, x, hx => by
    simp only [List.mapM_cons] at h
    cases hx₀ : f x₀ with
    | none => rw [hx₀] at h; cases h
    | some y₀ =>
      cases hxs : xs.mapM f with
      | none => rw [hx₀, hxs] at h; cases h
      | some ys' =>
        rw [hx₀, hxs] at h
        have hys : ys = y₀ :: ys' := by simpa using h.symm
        subst hys
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨y₀, List.mem_cons_self .., hx₀⟩
        · obtain ⟨y, hy, hfy⟩ := mem_mapM_some hxs x hx
          exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

theorem find?_of_nodup {α : Type} {L : List (String × α)} (hnd : (L.map (·.1)).Nodup) {p : String × α}
    (hp : p ∈ L) : L.find? (·.1 == p.1) = some p := by
  induction L with
  | nil => cases hp
  | cons q L ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hp with rfl | hp
    · simp
    · have hne : q.1 ≠ p.1 := fun h => hnd.1 ⟨p, hp, h.symm⟩
      have : (q.1 == p.1) = false := by simpa using hne
      simp only [List.find?_cons, this]
      exact ih hnd.2 hp

theorem find?_none_of_not_mem {α : Type} {L : List (String × α)} {y : String} (h : y ∉ L.map (·.1)) :
    L.find? (·.1 == y) = none := by
  apply List.find?_eq_none.mpr
  intro p hp hpy
  exact h (List.mem_map.mpr ⟨p, hp, by simpa using hpy⟩)

theorem nodup_reverse' {α : Type} {l : List α} (h : l.Nodup) : l.reverse.Nodup :=
  List.pairwise_reverse.mpr (h.imp fun h' => fun e => h' e.symm)

theorem tpCorr_append {Γt : TpScope} {Γ : Bindings} (hc : TpCorr Γt Γ) {ets : Cedar.Validation.EntitySchema}
    {vs : List TypedBinder} {bs : List Binder} (hbs : vs.mapM TypedBinder.toSpec = .ok bs)
    {Δ : Bindings} (hΔ : Dogwood.Spec.Temporal.domainSorts? ets bs = some Δ) :
    TpCorr ((vs.map binding).reverse ++ Γt) (Δ ++ Γ) := by
  obtain ⟨hnd, hnames⟩ := Dogwood.Thm.domainSorts_spec hΔ
  have hmb := map_binding hbs
  have hsorts : bs.mapM (Binder.sort? ets) = some Δ := by
    unfold Dogwood.Spec.Temporal.domainSorts? at hΔ
    rw [if_pos hnd] at hΔ
    exact hΔ
  intro y hy
  rw [hmb] at hy
  obtain ⟨L, hL⟩ : ∃ L, L = bs.map fun b => (b.name, b.ty == BinderType.timepoint) := ⟨_, rfl⟩
  rw [← hL] at hy
  have hLn : L.reverse.map (·.1) = (bs.map (·.name)).reverse := by
    simp [hL, List.map_reverse, Function.comp_def]
  by_cases hyn : y ∈ bs.map (·.name)
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hyn
    have hpL : (b.name, b.ty == BinderType.timepoint) ∈ L.reverse := by
      simp only [List.mem_reverse, hL, List.mem_map]
      exact ⟨b, hb, rfl⟩
    have hfind := find?_of_nodup (by rw [hLn]; exact nodup_reverse' hnd) hpL
    simp only [isTimepoint, List.find?_append, hfind, Option.some_or] at hy
    have hbt : b.ty = .timepoint := by simpa using hy
    obtain ⟨q, hq, hqs⟩ := mem_mapM_some hsorts b hb
    obtain ⟨hqn, hqt⟩ := binder_sort_ty hqs
    have hfq := find?_of_nodup (by rw [hnames]; exact hnd) hq
    rw [hqn] at hfq
    simp only [Bindings.lookup, List.find?_append, hfq, Option.some_or, Option.map_some]
    rw [hqt hbt]
  · have hnone := find?_none_of_not_mem (L := L.reverse) (y := y) (by rw [hLn]; simpa using hyn)
    simp only [isTimepoint, List.find?_append, hnone, Option.none_or] at hy
    rw [Dogwood.Thm.lookup_append_not_mem (by rw [hnames]; exact hyn)]
    exact hc y hy

mutual

/-- **A well-typed leaf has no timepoint ordering for the unorder pass to replace.** -/
theorem unorderFree_of_typed {C : TypingCtx} : (c : Condition) → {φ : Formula} → c.toFormula = .ok φ →
    {Γ : Bindings} → Formula.WellTyped C Γ φ → {Γt : TpScope} → TpCorr Γt Γ → unorderFree Γt c = true
  | ⟨_, .and l r⟩, φ, h, Γ, hty, Γt, hc => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    cases hty with
    | and h₁ h₂ =>
      simp [unorderFree, unorderFreeKind, unorderFree_of_typed l ha h₁ hc, unorderFree_of_typed r hb h₂ hc]
  | ⟨_, .or _ _⟩, φ, h, _, _, _, _ => by simp [Condition.toFormula, ConditionKind.toFormula] at h
  | ⟨_, .not c⟩, φ, h, Γ, hty, Γt, hc => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    cases hty with
    | not h₁ => simp [unorderFree, unorderFreeKind, unorderFree_of_typed c ha h₁ hc]
  | ⟨_, .formerly w c⟩, φ, h, Γ, hty, Γt, hc => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨win, _, a, ha, rfl⟩ := h
    cases hty with
    | formerly _ h₁ => simp [unorderFree, unorderFreeKind, unorderFree_of_typed c ha h₁ hc]
  | ⟨_, .previous w c⟩, φ, h, Γ, hty, Γt, hc => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨win, _, a, ha, rfl⟩ := h
    cases hty with
    | previous _ h₁ => simp [unorderFree, unorderFreeKind, unorderFree_of_typed c ha h₁ hc]
  | ⟨_, .since l w r⟩, φ, h, Γ, hty, Γt, hc => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, win, _, b, hb, rfl⟩ := h
    cases hty with
    | since _ h₁ h₂ =>
      simp [unorderFree, unorderFreeKind, unorderFree_of_typed l ha h₁ hc, unorderFree_of_typed r hb h₂ hc]
  | ⟨_, .exists ⟨s, ty⟩ c⟩, φ, h, Γ, hty, Γt, hc => by
    simp only [Condition.toFormula, ConditionKind.toFormula, TypedBinder.toSpec, bind_eq_ok,
      pure_eq_ok] at h
    obtain ⟨x, ⟨n, hn, rfl⟩, a, ha, rfl⟩ := h
    obtain rfl := toName_eq_ok hn
    cases hty with
    | exist hb h₁ =>
      simp only [unorderFree, unorderFreeKind]
      exact unorderFree_of_typed c ha h₁ (tpCorr_cons hc hb)
  | ⟨_, .predicate _⟩, _, _, _, _, _, _ => rfl
  | ⟨_, .tp _⟩, _, _, _, _, _, _ => rfl
  | ⟨_, .call _⟩, _, _, _, _, _, _ => rfl
  | ⟨_, .sigilRef _ _⟩, _, _, _, _, _, _ => rfl
  | ⟨_, .refine _ _ _⟩, _, _, _, _, _, _ => rfl
  | ⟨_, .comparison op l r⟩, φ, h, Γ, hty, Γt, hc => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨l', hl, r', hr, rfl⟩ := h
    cases hty with
    | eq hno h₁ h₂ _ =>
      have hord : LeafPasses.CmpOp.orders op = false := by
        cases op <;> simp_all [LeafPasses.CmpOp.orders, Dogwood.Spec.Temporal.CmpOp.IsOrder]
      simp [unorderFree, unorderFreeKind, unordersComparison, hord, computes_of_typed hc l hl h₁,
        computes_of_typed hc r hr h₂, unorderFreeTerm_of_typed l hl h₁ hc,
        unorderFreeTerm_of_typed r hr h₂ hc]
    | ord _ h₁ h₂ =>
      simp [unorderFree, unorderFreeKind, unordersComparison, computes_of_typed hc l hl h₁,
        computes_of_typed hc r hr h₂, isTimepointVar_of_cedar hc hl h₁, isTimepointVar_of_cedar hc hr h₂,
        unorderFreeTerm_of_typed l hl h₁ hc, unorderFreeTerm_of_typed r hr h₂ hc]

theorem unorderFreeTerm_of_typed {C : TypingCtx} : (t : Surface.Temporal.Term) →
    {t' : Dogwood.Spec.Temporal.Term} → t.toSpec = .ok t' → {Γ : Bindings} → {τ : TType} →
    Dogwood.Spec.Temporal.Term.Typed C Γ t' τ → {Γt : TpScope} → TpCorr Γt Γ →
    unorderFreeTerm Γt t = true
  | .agg ⟨_, k⟩, t', h, Γ, τ, hty, Γt, hc => by
    simp only [Surface.Temporal.Term.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    cases hty with
    | agg h₁ => simp only [unorderFreeTerm]; exact unorderFreeAgg_of_typed k ha h₁ hc
  | .arith op l r, t', h, Γ, τ, hty, Γt, hc => by
    simp only [Surface.Temporal.Term.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨l', hl, r', hr, rfl⟩ := h
    cases hty with
    | arith h₁ h₂ =>
      simp [unorderFreeTerm, unorderFreeTerm_of_typed l hl h₁ hc, unorderFreeTerm_of_typed r hr h₂ hc]
  | .entity _ _, _, _, _, _, _, _, _ | .integer _, _, _, _, _, _, _, _ | .decimal _, _, _, _, _, _, _, _
  | .string _, _, _, _, _, _, _, _ | .bool _, _, _, _, _, _, _, _ | .contextField _, _, _, _, _, _, _, _
  | .scopeField _, _, _, _, _, _, _, _ | .var _, _, _, _, _, _, _, _ | .wildcard, _, _, _, _, _, _, _
  | .array _, _, _, _, _, _, _, _ | .paramRef _, _, _, _, _, _, _, _ | .binderRef _, _, _, _, _, _, _, _ =>
    rfl

theorem unorderFreeAgg_of_typed {C : TypingCtx} : (k : AggExprKind) → {a : Aggregate} →
    AggExprKind.toSpec k = .ok a → {Γ : Bindings} → Dogwood.Spec.Temporal.Aggregate.Typed C Γ a →
    {Γt : TpScope} → TpCorr Γt Γ → unorderFreeAgg Γt k = true
  | .count vs b, a, h, Γ, hty, Γt, hc => by
    simp only [AggExprKind.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨bs, hbs, body, hb, rfl⟩ := h
    cases hty with
    | count hΔ h₁ =>
      simp only [unorderFreeAgg]
      exact unorderFree_of_typed b hb h₁ (tpCorr_append hc hbs hΔ)
  | .sum s vs b, a, h, Γ, hty, Γt, hc => by
    simp only [AggExprKind.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨x, _, bs, hbs, body, hb, rfl⟩ := h
    cases hty with
    | sum hΔ _ h₁ =>
      simp only [unorderFreeAgg]
      exact unorderFree_of_typed b hb h₁ (tpCorr_append hc hbs hΔ)
  | .call _, a, h, _, _, _, _ => by simp [AggExprKind.toSpec] at h

end

end Dogwood.Thm.Frontend
