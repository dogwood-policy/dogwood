import Dogwood.Thm.Frontend.Relativization.Typed

/-!
# Ordering timepoints by position changes nothing on a well-typed, safe leaf

The relation the relativized leaves are read under (`RSat`) orders two timepoints by position,
which the relativization rewrite's encodings need. On the authored part of a leaf it changes
nothing (`xsat_ord_iff`): typing applies an ordering only to two `Long`s, and safety makes every
variable an ordering reads one that the condition restricts, which holds a value rather than a
timepoint in every satisfying assignment (`restricts_coarse`). The argument holds for every
domain of the binders, including the specification's, in which an `exists` ranges over every
value and every timepoint whatever its declared type.
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.LeafPasses Surface.Temporal
open Dogwood.Spec (Event Trace TickRate EventSchema)
open Dogwood.Spec.Temporal (Valuation ImplChoices CVal TVal ArgsMatch Formula Aggregate TypingCtx
  Bindings TType Binder BinderType domainNames eqRestricted? valueSide CmpOp)

/-- A variable the bindings give a Cedar type holds no timepoint under the valuation. -/
def CoarseVar (Γ : Bindings) (v : Valuation) (y : String) : Prop :=
  ∀ ty w, Γ.lookup y = some (.cedar ty) → v y = some w → ∀ k, w ≠ .tp k

theorem coarseVar_bind {Γ : Bindings} {v : Valuation} {b : String × TType} {x y : String}
    (hb : b.1 = x) (hyx : y ≠ x) {w : TVal} (h : CoarseVar Γ v y) : CoarseVar (b :: Γ) (v.bind x w) y := by
  intro ty w' hl hw
  rw [lookup_cons_of_ne (by rw [hb]; exact Ne.symm hyx)] at hl
  simp only [Valuation.bind, if_neg hyx] at hw
  exact h ty w' hl hw

theorem coarseVar_unbind {Γ : Bindings} {v : Valuation} {b : String × TType} {x y : String}
    (hb : b.1 = x) (hyx : y ≠ x) {w : TVal} (h : CoarseVar (b :: Γ) (v.bind x w) y) : CoarseVar Γ v y := by
  intro ty w' hl hw
  refine h ty w' ?_ ?_
  · rw [lookup_cons_of_ne (by rw [hb]; exact Ne.symm hyx)]; exact hl
  · simp only [Valuation.bind, if_neg hyx]; exact hw

theorem coarseVar_bindAll {Γ Δ : Bindings} {v : Valuation} {bs : List Binder}
    (hnames : Δ.map (·.1) = bs.map (·.name)) {y : String} (hy : y ∉ bs.map (·.name))
    {row : List TVal} (h : CoarseVar Γ v y) :
    CoarseVar (Δ ++ Γ) (v.bindAll (domainNames bs) row) y := by
  intro ty w hl hw
  rw [Dogwood.Thm.lookup_append_not_mem (by rw [hnames]; exact hy)] at hl
  rw [Dogwood.Thm.bindAll_not_mem (by simpa [domainNames, Dogwood.Thm.mem_dedup] using hy)] at hw
  exact h ty w hl hw

theorem xHolds_eq {o : Bool} {a b : CVal} : xHolds o .eq a b ↔ a = b := by
  simp [xHolds, CmpOp.Holds, tpOrders]

section
variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop} {C : TypingCtx}

/-- **Restricted variables hold values of their sort.** In a well-typed condition that holds,
under every reading, a variable the condition restricts holds no timepoint when the bindings give
it a Cedar type, provided the variables of `R` hold none either. -/
theorem restricts_coarse {o : Bool} {dom : Domain} : (c : Condition) → {φ : Formula} →
    c.toFormula = .ok φ → {Γ : Bindings} → Formula.WellTyped C Γ φ → {R : String → Prop} →
    {v : Valuation} → {j : Nat} → XSat ι rate σ e vis o dom v j c →
    (∀ y, R y → CoarseVar Γ v y) → ∀ x, φ.Restricts R x → CoarseVar Γ v x
  | ⟨_, .predicate ⟨_, ns, a, kd, args⟩⟩, φ, h, Γ, hty, R, v, j, hs, hR, x, hx => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨uid, hu, args', ha, rfl⟩ := h
    obtain ⟨p, hp⟩ := hx
    obtain ⟨uid', args'', _, ha', q, _, _, _, hm⟩ := hs
    rw [ha] at ha'; cases ha'
    obtain ⟨w, _, hmt⟩ := hm _ hp
    simp only [Dogwood.Spec.Temporal.Term.Matches, Dogwood.Spec.Temporal.Term.eval?] at hmt
    intro ty w' _ hw' k hk
    rw [hmt, hk] at hw'
    cases hw'
  | ⟨_, .tp s⟩, φ, h, Γ, hty, R, v, j, hs, hR, x, hx => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨y, _, rfl⟩ := h
    simp only [Formula.Restricts] at hx
    subst hx
    cases hty with
    | tp hlook =>
      intro ty w hl
      rw [hlook] at hl; cases hl
  | ⟨_, .comparison op l r⟩, φ, h, Γ, hty, R, v, j, hs, hR, x, hx => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨l', hl, r', hr, rfl⟩ := h
    cases op <;> simp only [Formula.Restricts] at hx
    obtain ⟨heq, _⟩ := hx
    obtain ⟨a, b, ha, hb, hab⟩ := hs
    rw [xHolds_eq] at hab
    subst hab
    rcases Dogwood.Thm.eqRestricted_cases heq with rfl | ⟨rfl, hnl⟩
    · obtain rfl := toSpec_eq_var hl
      have hnr : ∀ z, r' ≠ .var z := by
        rintro z rfl; simp [eqRestricted?] at heq
      obtain ⟨w, hw, rfl⟩ := xdenotes_var.mp ha
      intro ty w' _ hw' k hk
      rw [hw, hk, Option.some.injEq] at hw'
      subst hw'
      obtain ⟨z, rfl, _⟩ := xdenotes_tp (k := k) (by simpa [CVal.ofTVal] using hb)
      simp only [Surface.Temporal.Term.toSpec, pure_eq_ok] at hr
      exact hnr z hr.symm
    · obtain rfl := toSpec_eq_var hr
      obtain ⟨w, hw, hwb⟩ := xdenotes_var.mp hb
      intro ty w' _ hw' k hk
      rw [hw, hk, Option.some.injEq] at hw'
      subst hw'
      rw [hwb] at ha
      obtain ⟨z, rfl, _⟩ := xdenotes_tp (k := k) (by simpa [CVal.ofTVal] using ha)
      simp only [Surface.Temporal.Term.toSpec, pure_eq_ok] at hl
      exact hnl z hl.symm
  | ⟨_, .not _⟩, φ, h, _, _, _, _, _, _, _, x, hx => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, _, rfl⟩ := h
    exact hx.elim
  | ⟨_, .formerly w c⟩, φ, h, Γ, hty, R, v, j, hs, hR, x, hx => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨win, _, a, ha, rfl⟩ := h
    cases hty with
    | formerly _ h₁ =>
      obtain ⟨_, _, k, _, _, _, hs⟩ := hs
      exact restricts_coarse c ha h₁ hs hR x hx
  | ⟨_, .previous w c⟩, φ, h, Γ, hty, R, v, j, hs, hR, x, hx => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨win, _, a, ha, rfl⟩ := h
    cases hty with
    | previous _ h₁ =>
      obtain ⟨_, _, k, _, _, _, _, hs⟩ := hs
      exact restricts_coarse c ha h₁ hs hR x hx
  | ⟨_, .since l w r⟩, φ, h, Γ, hty, R, v, j, hs, hR, x, hx => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, _, win, _, b, hb, rfl⟩ := h
    cases hty with
    | since _ _ h₂ =>
      obtain ⟨_, _, k, _, _, _, hs, _⟩ := hs
      exact restricts_coarse r hb h₂ hs hR x hx
  | ⟨_, .exists ⟨s, ty⟩ c⟩, φ, h, Γ, hty, R, v, j, hs, hR, x, hx => by
    simp only [Condition.toFormula, ConditionKind.toFormula, TypedBinder.toSpec, bind_eq_ok,
      pure_eq_ok] at h
    obtain ⟨y, ⟨n, hn, rfl⟩, a, ha, rfl⟩ := h
    obtain rfl := toName_eq_ok hn
    obtain ⟨hxn, hx⟩ := hx
    cases hty with
    | exist hb h₁ =>
      rename_i b
      have hbn : b.1 = n := (binder_sort_ty hb).1
      obtain ⟨n', hn', w, _, hs⟩ := hs
      simp only [BinderSlot.toName, pure, Except.pure, Except.ok.injEq] at hn'
      subst hn'
      have := restricts_coarse c ha h₁ hs (R := fun z => z ≠ n ∧ R z)
        (fun z ⟨hzn, hz⟩ => coarseVar_bind hbn hzn (hR z hz)) x hx
      exact coarseVar_unbind hbn hxn this
  | ⟨_, .and l r⟩, φ, h, Γ, hty, R, v, j, hs, hR, x, hx => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    cases hty with
    | and h₁ h₂ =>
      exact hx (fun z => CoarseVar Γ v z) hR
        (fun z hz => restricts_coarse l ha h₁ hs.1 (fun y hy => hy) z hz)
        (fun z hz => restricts_coarse r hb h₂ hs.2 (fun y hy => hy) z hz)
  | ⟨_, .or _ _⟩, φ, h, _, _, _, _, _, _, _, _, _ => by
    simp [Condition.toFormula, ConditionKind.toFormula] at h
  | ⟨_, .call _⟩, φ, h, _, _, _, _, _, _, _, _, _ => by
    simp [Condition.toFormula, ConditionKind.toFormula] at h
  | ⟨_, .sigilRef _ _⟩, φ, h, _, _, _, _, _, _, _, _, _ => by
    simp [Condition.toFormula, ConditionKind.toFormula] at h
  | ⟨_, .refine _ _ _⟩, φ, h, _, _, _, _, _, _, _, _, _ => by
    simp [Condition.toFormula, ConditionKind.toFormula] at h

/-- An operand of a Cedar type, whose variables hold no timepoints, denotes no timepoint. -/
theorem xdenotes_not_tp {o : Bool} {dom : Domain} {Γ : Bindings} {v : Valuation} {j : Nat}
    {t : Surface.Temporal.Term} {t' : Dogwood.Spec.Temporal.Term} (ht : t.toSpec = .ok t')
    {ty : Cedar.Validation.CedarType} (hty : Dogwood.Spec.Temporal.Term.Typed C Γ t' (.cedar ty))
    (hv : ∀ y ∈ t'.fv, CoarseVar Γ v y) {a : CVal} (ha : XDenotes ι rate σ e vis o dom v j t a) :
    ∀ k, a ≠ .tp k := by
  rintro k rfl
  obtain ⟨x, rfl, hx⟩ := xdenotes_tp ha
  simp only [Surface.Temporal.Term.toSpec, pure_eq_ok] at ht
  subst ht
  cases hty with
  | var hl => exact hv x (by simp [Dogwood.Spec.Temporal.Term.fv]) ty _ hl hx k rfl

theorem tpOrders_not_tp {op : CmpOp} {a b : CVal} (ha : ∀ k, a ≠ .tp k) : ¬ tpOrders op a b := by
  intro h
  obtain ⟨_, ⟨m, rfl⟩, _⟩ := tpOrders_spec h
  exact ha m rfl

mutual

/-- **Ordering timepoints by position changes nothing on a well-typed, safe condition.** -/
theorem xsat_ord_iff {dom : Domain} : (c : Condition) → {φ : Formula} → c.toFormula = .ok φ →
    {Γ : Bindings} → Formula.WellTyped C Γ φ → {R : String → Prop} → φ.Safe R → {v : Valuation} →
    (∀ y, R y → CoarseVar Γ v y) → (j : Nat) →
    (XSat ι rate σ e vis true dom v j c ↔ XSat ι rate σ e vis false dom v j c)
  | ⟨sp, .and l r⟩, φ, h, Γ, hty, R, hs, v, hR, j => by
    have h0 := h
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    cases hty with
    | and h₁ h₂ =>
      have key : ∀ o, XSat ι rate σ e vis o dom v j ⟨sp, .and l r⟩ →
          ∀ y, (Formula.and a b).Restricts R y → CoarseVar Γ v y :=
        fun o hs' y hy => restricts_coarse _ h0 (.and h₁ h₂) hs' hR y hy
      simp only [XSat]
      constructor
      · intro hs'
        have hc := key true hs'
        exact ⟨(xsat_ord_iff l ha h₁ hs.1 hc j).mp hs'.1, (xsat_ord_iff r hb h₂ hs.2 hc j).mp hs'.2⟩
      · intro hs'
        have hc := key false hs'
        exact ⟨(xsat_ord_iff l ha h₁ hs.1 hc j).mpr hs'.1, (xsat_ord_iff r hb h₂ hs.2 hc j).mpr hs'.2⟩
  | ⟨_, .not c⟩, φ, h, Γ, hty, R, hs, v, hR, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    cases hty with
    | not h₁ => simp only [XSat]; exact not_congr (xsat_ord_iff c ha h₁ hs.2 hR j)
  | ⟨_, .formerly w c⟩, φ, h, Γ, hty, R, hs, v, hR, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨win, _, a, ha, rfl⟩ := h
    cases hty with
    | formerly _ h₁ =>
      simp only [XSat]
      exact exists_congr fun win => and_congr_right' (exists_congr fun k => and_congr_right'
        (and_congr_right' (and_congr_right' (xsat_ord_iff c ha h₁ hs hR k))))
  | ⟨_, .previous w c⟩, φ, h, Γ, hty, R, hs, v, hR, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨win, _, a, ha, rfl⟩ := h
    cases hty with
    | previous _ h₁ =>
      simp only [XSat]
      exact exists_congr fun win => and_congr_right' (exists_congr fun k => and_congr_right'
        (and_congr_right' (and_congr_right' (and_congr_right' (xsat_ord_iff c ha h₁ hs hR k)))))
  | ⟨_, .since l w r⟩, φ, h, Γ, hty, R, hs, v, hR, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, win, _, b, hb, rfl⟩ := h
    cases hty with
    | since _ h₁ h₂ =>
      obtain ⟨hsb, _, hsa⟩ := hs
      have key : ∀ o k, XSat ι rate σ e vis o dom v k r →
          ∀ y, Formula.Restricted R b y → CoarseVar Γ v y :=
        fun o k hr y hy => hy.elim (hR y) (restricts_coarse r hb h₂ hr hR y)
      simp only [XSat]
      constructor
      · rintro ⟨win, hw, k, hk, hvk, hiw, hr, hl⟩
        refine ⟨win, hw, k, hk, hvk, hiw, (xsat_ord_iff r hb h₂ hsb hR k).mp hr,
          fun k' h₁' h₂' h₃' => (xsat_ord_iff l ha h₁ hsa (key true k hr) k').mp (hl k' h₁' h₂' h₃')⟩
      · rintro ⟨win, hw, k, hk, hvk, hiw, hr, hl⟩
        refine ⟨win, hw, k, hk, hvk, hiw, (xsat_ord_iff r hb h₂ hsb hR k).mpr hr,
          fun k' h₁' h₂' h₃' => (xsat_ord_iff l ha h₁ hsa (key false k hr) k').mpr (hl k' h₁' h₂' h₃')⟩
  | ⟨_, .exists ⟨s, ty⟩ c⟩, φ, h, Γ, hty, R, hs, v, hR, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, TypedBinder.toSpec, bind_eq_ok,
      pure_eq_ok] at h
    obtain ⟨y, ⟨n, hn, rfl⟩, a, ha, rfl⟩ := h
    obtain rfl := toName_eq_ok hn
    cases hty with
    | exist hb h₁ =>
      rename_i b
      have hbn : b.1 = n := (binder_sort_ty hb).1
      simp only [XSat]
      refine exists_congr fun n' => and_congr_right fun hn' => ?_
      simp only [BinderSlot.toName, pure, Except.pure, Except.ok.injEq] at hn'
      subst hn'
      exact exists_congr fun w => and_congr_right' (xsat_ord_iff c ha h₁ hs.2
        (fun z ⟨hzn, hz⟩ => coarseVar_bind hbn hzn (hR z hz)) j)
  | ⟨_, .comparison op l r⟩, φ, h, Γ, hty, R, hs, v, hR, j => by
    simp only [Condition.toFormula, ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨l', hl, r', hr, rfl⟩ := h
    obtain ⟨hfv, hsl, hsr⟩ := hs
    simp only [XSat]
    cases hty with
    | eq hno h₁ h₂ _ =>
      refine exists_congr fun a => exists_congr fun b => ?_
      rw [xdenotes_ord_iff l hl h₁ hsl hR j a, xdenotes_ord_iff r hr h₂ hsr hR j b]
      refine and_congr_right' (and_congr_right' ?_)
      have : ∀ a b, ¬ tpOrders op a b := by
        intro a b; cases op <;> simp_all [tpOrders, Dogwood.Spec.Temporal.CmpOp.IsOrder]
      simp [xHolds, this]
    | ord ho h₁ h₂ =>
      have hRfv : ∀ y ∈ l'.fv ++ r'.fv, R y := fun y hy => (hfv y hy).elim id fun h' => by
        cases op <;> simp_all [Formula.Restricts, Dogwood.Spec.Temporal.CmpOp.IsOrder]
      refine exists_congr fun a => exists_congr fun b => ?_
      rw [xdenotes_ord_iff l hl h₁ hsl hR j a, xdenotes_ord_iff r hr h₂ hsr hR j b]
      refine and_congr_right fun ha => and_congr_right' ?_
      have hna := xdenotes_not_tp hl h₁ (fun y hy => hR y (hRfv y (List.mem_append_left _ hy))) ha
      simp [xHolds, tpOrders_not_tp (op := op) (b := b) hna]
  | ⟨_, .predicate ⟨_, _, _, _, _⟩⟩, _, _, _, _, _, _, _, _, _ => Iff.rfl
  | ⟨_, .tp _⟩, _, _, _, _, _, _, _, _, _ => Iff.rfl
  | ⟨_, .call _⟩, _, _, _, _, _, _, _, _, _ => Iff.rfl
  | ⟨_, .sigilRef _ _⟩, _, _, _, _, _, _, _, _, _ => Iff.rfl
  | ⟨_, .refine _ _ _⟩, _, _, _, _, _, _, _, _, _ => Iff.rfl
  | ⟨_, .or _ _⟩, φ, h, _, _, _, _, _, _, _ => by
    simp [Condition.toFormula, ConditionKind.toFormula] at h

theorem xdenotes_ord_iff {dom : Domain} : (t : Surface.Temporal.Term) →
    {t' : Dogwood.Spec.Temporal.Term} → t.toSpec = .ok t' → {Γ : Bindings} → {τ : TType} →
    Dogwood.Spec.Temporal.Term.Typed C Γ t' τ → {R : String → Prop} → t'.Safe R →
    {v : Valuation} → (∀ y, R y → CoarseVar Γ v y) → (j : Nat) → (c : CVal) →
    (XDenotes ι rate σ e vis true dom v j t c ↔ XDenotes ι rate σ e vis false dom v j t c)
  | .agg ⟨_, k⟩, t', h, Γ, τ, hty, R, hs, v, hR, j, c => by
    simp only [Surface.Temporal.Term.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    cases hty with
    | agg h₁ =>
      simp only [XDenotes]
      exact exists_congr fun n => and_congr_left' (xtotal_ord_iff k ha h₁ hs hR j n)
  | .arith op l r, t', h, Γ, τ, hty, R, hs, v, hR, j, c => by
    simp only [Surface.Temporal.Term.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨l', hl, r', hr, rfl⟩ := h
    cases hty with
    | arith h₁ h₂ =>
      simp only [XDenotes]
      exact exists_congr fun m => exists_congr fun n => and_congr
        (xdenotes_ord_iff l hl h₁ hs.1 hR j _) (and_congr_left' (xdenotes_ord_iff r hr h₂ hs.2 hR j _))
  | .entity _ _, _, _, _, _, _, _, _, _, _, _, _ | .integer _, _, _, _, _, _, _, _, _, _, _, _
  | .decimal _, _, _, _, _, _, _, _, _, _, _, _ | .string _, _, _, _, _, _, _, _, _, _, _, _
  | .bool _, _, _, _, _, _, _, _, _, _, _, _ | .contextField _, _, _, _, _, _, _, _, _, _, _, _
  | .scopeField _, _, _, _, _, _, _, _, _, _, _, _ | .var _, _, _, _, _, _, _, _, _, _, _, _
  | .wildcard, _, _, _, _, _, _, _, _, _, _, _ | .array _, _, _, _, _, _, _, _, _, _, _, _
  | .paramRef _, _, _, _, _, _, _, _, _, _, _, _ | .binderRef _, _, _, _, _, _, _, _, _, _, _, _ => Iff.rfl

theorem xtotal_ord_iff {dom : Domain} : (k : AggExprKind) → {a : Aggregate} →
    AggExprKind.toSpec k = .ok a → {Γ : Bindings} → Dogwood.Spec.Temporal.Aggregate.Typed C Γ a →
    {R : String → Prop} → a.Safe R → {v : Valuation} → (∀ y, R y → CoarseVar Γ v y) → (j : Nat) →
    (n : Int) → (XTotal ι rate σ e vis true dom v j k n ↔ XTotal ι rate σ e vis false dom v j k n)
  | .count vs b, a, h, Γ, hty, R, hs, v, hR, j, n => by
    simp only [AggExprKind.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨bs, hbs, body, hb, rfl⟩ := h
    cases hty with
    | count hΔ h₁ =>
      obtain ⟨_, hnames⟩ := Dogwood.Thm.domainSorts_spec hΔ
      simp only [XTotal]
      refine exists_congr fun bs' => and_congr_right fun hbs' => ?_
      rw [hbs] at hbs'; cases hbs'
      refine exists_congr fun rows => and_congr_right' (and_congr_left' (forall_congr' fun row =>
        iff_congr Iff.rfl (and_congr_right' (and_congr_right' ?_))))
      exact xsat_ord_iff b hb h₁ hs.2 (fun y ⟨hy, hRy⟩ => coarseVar_bindAll hnames hy (hR y hRy)) j
  | .sum s vs b, a, h, Γ, hty, R, hs, v, hR, j, n => by
    simp only [AggExprKind.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨x, hx, bs, hbs, body, hb, rfl⟩ := h
    cases hty with
    | sum hΔ _ h₁ =>
      obtain ⟨_, hnames⟩ := Dogwood.Thm.domainSorts_spec hΔ
      simp only [XTotal]
      refine exists_congr fun x' => exists_congr fun bs' => and_congr_right' (and_congr_right fun hbs' => ?_)
      rw [hbs] at hbs'; cases hbs'
      refine exists_congr fun rows => and_congr_right' (and_congr_left' (forall_congr' fun row =>
        iff_congr Iff.rfl (and_congr_right' (and_congr_right' ?_))))
      exact xsat_ord_iff b hb h₁ hs.2 (fun y ⟨hy, hRy⟩ => coarseVar_bindAll hnames hy (hR y hRy)) j
  | .call _, a, h, _, _, _, _, _, _, _, _ => by simp [AggExprKind.toSpec] at h

end

end

end Dogwood.Thm.Frontend
