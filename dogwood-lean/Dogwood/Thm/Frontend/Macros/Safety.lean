import Dogwood.Thm.Frontend.Macros.Transport

/-!
# The temporal static checks decide `SafeLR`

`Dogwood.Frontend.Macros.checkLeaf`, the crate's `check_condition`, `check_leaf_closed` and
`check_demands`, accepts an authored leaf exactly when its formula is closed, is well formed
(`WF`: no binder or `tp` variable named after a Cedar request variable, every summand one of
its `for` variables, no aggregate or arithmetic as a predicate argument) and is safe with each
`&&` chain read left to right (`SafeLR`): `checkLeaf_iff`. Since `SafeLR` implies the
specification's safety, every leaf the check accepts is safe (`checkLeaf_isSafe`).

The converse fails, and not only because of the order of the conjuncts: `Formula.Safe` closes
each chain under what its conjuncts restrict, so a conjunct may restrict one variable before the
others and another after, which no order of the conjuncts reproduces. `Macros.Examples` gives a
safe leaf that the check rejects in all eight orders of its three chains.
-/

namespace Dogwood.Thm.Frontend.Macros

open Dogwood.Frontend Dogwood.Frontend.Macros Dogwood.Frontend.Surface.Temporal
open Dogwood.Spec.Temporal (Formula Binder)
open Dogwood.Thm (pred_ext mem_predVars)

/-! ## Messages naming the least element of a set -/

theorem least_eq_none {xs : List String} : least xs = none ↔ xs = [] := by
  cases xs with
  | nil => simp [least]
  | cons x xs =>
    simp only [least, reduceCtorEq, iff_false]
    split <;> simp

theorem least_mem : {xs : List String} → {v : String} → least xs = some v → v ∈ xs
  | [], _, h => by simp [least] at h
  | x :: xs, v, h => by
    simp only [least] at h
    split at h
    · simp only [Option.some.injEq] at h
      exact h ▸ List.mem_cons_self
    · rename_i y hy
      simp only [Option.some.injEq] at h
      split at h
      · exact h ▸ List.mem_cons_self
      · exact h ▸ List.mem_cons_of_mem _ (least_mem hy)

theorem filter_nil_iff {xs : List String} {p : String → Bool} :
    xs.filter p = [] ↔ ∀ x ∈ xs, p x = false := by
  simp [List.filter_eq_nil_iff]

/-- A check that fails naming the least element of a set passes iff the set is empty. -/
macro "least_split" : tactic => `(tactic| (
  split <;> rename_i h <;>
    first
    | (simp only [pure_eq_ok, true_iff]; exact least_eq_none.mp h)
    | (simp only [throw_ne_ok, false_iff]; intro he; rw [he] at h; simp [least] at h)))

theorem rejectUnmetFilter_ok {fv ρ : List String} :
    rejectUnmetFilter fv ρ = .ok () ↔ ∀ y ∈ fv, y ∈ ρ := by
  have key : (fv.filter fun v => !ρ.contains v) = [] ↔ ∀ y ∈ fv, y ∈ ρ := by
    rw [filter_nil_iff]; simp
  rw [← key]
  unfold rejectUnmetFilter
  least_split

theorem bindingDemands_ok {b : String} {l r : Term} {ρ : List String} :
    bindingDemands b l r ρ = .ok () ↔ ∀ y ∈ termVars (valueSide b l r), y ∈ ρ := by
  have key : ((termVars (valueSide b l r)).filter fun v => !ρ.contains v) = [] ↔
      ∀ y ∈ termVars (valueSide b l r), y ∈ ρ := by
    rw [filter_nil_iff]; simp
  rw [← key]
  unfold bindingDemands
  least_split

theorem sinceDemands_ok {l r : Condition} {ρ : List String} :
    sinceDemands l r ρ = .ok () ↔ ∀ y ∈ condFree l, y ∈ condRR r ∨ y ∈ ρ := by
  have key : ((condFree l).filter fun v => !(condRR r).contains v && !ρ.contains v) = [] ↔
      ∀ y ∈ condFree l, y ∈ condRR r ∨ y ∈ ρ := by
    rw [filter_nil_iff]
    simp only [Bool.and_eq_false_iff, Bool.not_eq_false', List.contains_iff_mem]
  rw [← key]
  unfold sinceDemands
  dsimp only
  least_split

/-! ## The order check -/

theorem chain_leaf {ρ : List String} {sp : Span} {k : ConditionKind}
    (hk : ∀ l r, k ≠ .and l r) :
    chain ρ ⟨sp, k⟩ = (conjDemands ρ k >>= fun _ => descend ρ k) := by
  cases k <;> first | rfl | exact absurd rfl (hk _ _)

theorem chainF_leaf {ρ : List String} {φ : SFormula} (hφ : ∀ a b, φ ≠ .and a b) :
    ChainF ρ φ ↔ ConjF ρ φ ∧ DescF ρ φ := by
  cases φ <;> first | exact absurd rfl (hφ _ _) | exact Iff.rfl

theorem toFormula_ne_and {k : ConditionKind} {φ : SFormula} (h : ConditionKind.toFormula k = .ok φ)
    (hk : ∀ l r, k ≠ .and l r) : ∀ a b, φ ≠ .and a b := by
  intro a b he
  subst he
  cases k with
  | and l r => exact hk l r rfl
  | or => exact inv_or h
  | not => obtain ⟨_, _, h⟩ := inv_not h; cases h
  | formerly => obtain ⟨_, _, _, _, h⟩ := inv_formerly h; cases h
  | previous => obtain ⟨_, _, _, _, h⟩ := inv_previous h; cases h
  | since => obtain ⟨_, _, _, _, _, _, h⟩ := inv_since h; cases h
  | predicate p => obtain ⟨_, _, _, _, _⟩ := p; obtain ⟨_, _, _, h⟩ := inv_pred h; cases h
  | comparison => obtain ⟨_, _, _, _, h⟩ := inv_cmp h; cases h
  | «exists» => obtain ⟨_, _, _, _, h⟩ := inv_exists h; cases h
  | tp => obtain ⟨_, _, h⟩ := inv_tp h; cases h
  | call => exact inv_call h
  | sigilRef => exact inv_sigil h
  | refine => exact inv_refine h

theorem leaf_iff {ρ : List String} {sp : Span} {k : ConditionKind} {φ : SFormula}
    (h : ConditionKind.toFormula k = .ok φ) (hk : ∀ l r, k ≠ .and l r)
    (hc : conjDemands ρ k = .ok () ↔ ConjF ρ φ) (hd : descend ρ k = .ok () ↔ DescF ρ φ) :
    chain ρ ⟨sp, k⟩ = .ok () ↔ ChainF ρ φ := by
  rw [chain_leaf hk, seq_eq_ok, hc, hd, chainF_leaf (toFormula_ne_and h hk)]

theorem conjDemands_formerly {ρ : List String} {w : WithinSpec} {sp : Span} {k : ConditionKind} :
    conjDemands ρ (.formerly w ⟨sp, k⟩) = conjDemands ρ k := by
  cases k <;> rfl

theorem conjDemands_previous {ρ : List String} {w : WithinSpec} {sp : Span} {k : ConditionKind} :
    conjDemands ρ (.previous w ⟨sp, k⟩) = conjDemands ρ k := by
  cases k <;> rfl

theorem conjDemands_exists {ρ : List String} {v : TypedBinder} {sp : Span} {k : ConditionKind} :
    conjDemands ρ (.exists v ⟨sp, k⟩) = conjDemands (match v.slot with
      | .name n => without ρ n
      | _ => ρ) k := by
  cases k <;> rfl

theorem withoutAll_eq {ρ : List String} {vs : List TypedBinder} {dom : List Binder}
    (h : vs.mapM TypedBinder.toSpec = .ok dom) : withoutAll ρ vs = withoutDom ρ dom := by
  simp only [withoutAll, withoutDom, toSpec_binders h]

mutual

theorem chain_iff : (c : Condition) → {φ : SFormula} → c.toFormula = .ok φ → (ρ : List String) →
    (chain ρ c = .ok () ↔ ChainF ρ φ)
  | ⟨_, .and l r⟩, _, h, ρ => by
    obtain ⟨a, b, ha, hb, rfl⟩ := inv_and h
    simp only [chain, seq_eq_ok, chain_iff l ha, chain_iff r hb, condRR_eq l ha, ChainF]
  | ⟨_, .or l r⟩, _, h, _ => absurd h (@inv_or _ l r)
  | ⟨_, .call c⟩, _, h, _ => absurd h (@inv_call _ c)
  | ⟨_, .sigilRef s n⟩, _, h, _ => absurd h (@inv_sigil _ s n)
  | ⟨_, .refine b fs sp⟩, _, h, _ => absurd h (@inv_refine _ b fs sp)
  | ⟨_, .not c⟩, _, h, ρ =>
    leaf_iff h (fun _ _ e => by cases e) (conjDemands_iff _ h ρ) (descend_iff _ h ρ)
  | ⟨_, .formerly w c⟩, _, h, ρ =>
    leaf_iff h (fun _ _ e => by cases e) (conjDemands_iff _ h ρ) (descend_iff _ h ρ)
  | ⟨_, .previous w c⟩, _, h, ρ =>
    leaf_iff h (fun _ _ e => by cases e) (conjDemands_iff _ h ρ) (descend_iff _ h ρ)
  | ⟨_, .since l w r⟩, _, h, ρ =>
    leaf_iff h (fun _ _ e => by cases e) (conjDemands_iff _ h ρ) (descend_iff _ h ρ)
  | ⟨_, .predicate p⟩, _, h, ρ =>
    leaf_iff h (fun _ _ e => by cases e) (conjDemands_iff _ h ρ) (descend_iff _ h ρ)
  | ⟨_, .comparison op l r⟩, _, h, ρ =>
    leaf_iff h (fun _ _ e => by cases e) (conjDemands_iff _ h ρ) (descend_iff _ h ρ)
  | ⟨_, .exists v c⟩, _, h, ρ =>
    leaf_iff h (fun _ _ e => by cases e) (conjDemands_iff _ h ρ) (descend_iff _ h ρ)
  | ⟨_, .tp v⟩, _, h, ρ =>
    leaf_iff h (fun _ _ e => by cases e) (conjDemands_iff _ h ρ) (descend_iff _ h ρ)

theorem conjDemands_iff : (k : ConditionKind) → {φ : SFormula} → ConditionKind.toFormula k = .ok φ →
    (ρ : List String) → (conjDemands ρ k = .ok () ↔ ConjF ρ φ)
  | .comparison op l r, _, h, ρ => by
    obtain ⟨l', r', hl, hr, rfl⟩ := inv_cmp h
    simp only [conjDemands, ConjF, CmpDemands, eqRestrictedVar_eq hl hr]
    cases op <;> cases hx : Dogwood.Spec.Temporal.eqRestricted? l' r' <;>
      simp only [rejectUnmetFilter_ok, termVars_eq l hl, termVars_eq r hr]
    rename_i x
    rw [bindingDemands_ok, termVars_eq _ (valueSide_toSpec hl hr)]
  | .not c, _, h, ρ => by
    obtain ⟨a, ha, rfl⟩ := inv_not h
    simp only [conjDemands, ConjF, rejectUnmetFilter_ok, condFree_eq c ha]
  | .since l w r, _, h, ρ => by
    obtain ⟨a, _, b, ha, _, hb, rfl⟩ := inv_since h
    simp only [conjDemands, ConjF, sinceDemands_ok, condFree_eq l ha, condRR_eq r hb]
  | .formerly w ⟨_, k⟩, _, h, ρ => by
    obtain ⟨_, a, _, ha, rfl⟩ := inv_formerly h
    rw [conjDemands_formerly]
    exact conjDemands_iff k ha ρ
  | .previous w ⟨_, k⟩, _, h, ρ => by
    obtain ⟨_, a, _, ha, rfl⟩ := inv_previous h
    rw [conjDemands_previous]
    exact conjDemands_iff k ha ρ
  | .exists v ⟨_, k⟩, _, h, ρ => by
    obtain ⟨x, a, hv, ha, rfl⟩ := inv_exists h
    rw [conjDemands_exists, hv]
    exact conjDemands_iff k ha _
  | .and l r, _, h, _ => by
    obtain ⟨a, b, _, _, rfl⟩ := inv_and h
    simp only [conjDemands, ConjF, pure_eq_ok]
  | .predicate p, _, h, _ => by
    obtain ⟨_, _, _, _, _⟩ := p
    obtain ⟨_, _, _, rfl⟩ := inv_pred h
    simp only [conjDemands, ConjF, pure_eq_ok]
  | .tp v, _, h, _ => by
    obtain ⟨_, _, rfl⟩ := inv_tp h
    simp only [conjDemands, ConjF, pure_eq_ok]
  | .or _ _, _, h, _ => absurd h inv_or
  | .call _, _, h, _ => absurd h inv_call
  | .sigilRef _ _, _, h, _ => absurd h inv_sigil
  | .refine _ _ _, _, h, _ => absurd h inv_refine

theorem descend_iff : (k : ConditionKind) → {φ : SFormula} → ConditionKind.toFormula k = .ok φ →
    (ρ : List String) → (descend ρ k = .ok () ↔ DescF ρ φ)
  | .and l r, _, h, ρ => by
    obtain ⟨a, b, ha, hb, rfl⟩ := inv_and h
    simp only [descend, condHasSigil_eq l ha, condHasSigil_eq r hb, Bool.or_false,
      Bool.false_eq_true, if_false, seq_eq_ok, chain_iff l ha, chain_iff r hb, condRR_eq l ha,
      DescF]
  | .not ⟨_, k⟩, _, h, ρ => by
    obtain ⟨a, ha, rfl⟩ := inv_not h
    simp only [descend, DescF]
    exact descend_iff k ha ρ
  | .formerly w c, _, h, ρ => by
    obtain ⟨_, a, _, ha, rfl⟩ := inv_formerly h
    simp only [descend, condHasSigil_eq c ha, Bool.false_eq_true, if_false, chain_iff c ha, DescF]
  | .previous w c, _, h, ρ => by
    obtain ⟨_, a, _, ha, rfl⟩ := inv_previous h
    simp only [descend, condHasSigil_eq c ha, Bool.false_eq_true, if_false, chain_iff c ha, DescF]
  | .since l w r, _, h, ρ => by
    obtain ⟨a, _, b, ha, _, hb, rfl⟩ := inv_since h
    simp only [descend, condHasSigil_eq l ha, condHasSigil_eq r hb, Bool.false_eq_true, if_false,
      seq_eq_ok, chain_iff l ha, chain_iff r hb, condRR_eq r hb, DescF]
  | .exists v c, _, h, ρ => by
    obtain ⟨x, a, hv, ha, rfl⟩ := inv_exists h
    simp only [descend, condHasSigil_eq c ha, Bool.false_eq_true, if_false, hv, chain_iff c ha,
      DescF, without]
  | .comparison op l r, _, h, ρ => by
    obtain ⟨l', r', hl, hr, rfl⟩ := inv_cmp h
    simp only [descend, seq_eq_ok, descendTerm_iff l hl, descendTerm_iff r hr, DescF]
  | .predicate p, _, h, _ => by
    obtain ⟨_, _, _, _, _⟩ := p
    obtain ⟨_, _, _, rfl⟩ := inv_pred h
    simp only [descend, DescF, pure_eq_ok]
  | .tp v, _, h, _ => by
    obtain ⟨_, _, rfl⟩ := inv_tp h
    simp only [descend, DescF, pure_eq_ok]
  | .or _ _, _, h, _ => absurd h inv_or
  | .call _, _, h, _ => absurd h inv_call
  | .sigilRef _ _, _, h, _ => absurd h inv_sigil
  | .refine _ _ _, _, h, _ => absurd h inv_refine

theorem descendTerm_iff : (t : Term) → {t' : STerm} → t.toSpec = .ok t' → (ρ : List String) →
    (descendTerm ρ t = .ok () ↔ DescTerm ρ t')
  | .agg ⟨_, .count vs b⟩, _, h, ρ => by
    obtain ⟨a, ha, rfl⟩ := inv_agg h
    obtain ⟨dom, body, hd, hb, rfl⟩ := inv_count ha
    simp only [descendTerm, condHasSigil_eq b hb, Bool.false_eq_true, if_false, withoutAll_eq hd,
      chain_iff b hb, DescTerm]
  | .agg ⟨_, .sum s vs b⟩, _, h, ρ => by
    obtain ⟨a, ha, rfl⟩ := inv_agg h
    obtain ⟨_, dom, body, _, hd, hb, rfl⟩ := inv_sum ha
    simp only [descendTerm, condHasSigil_eq b hb, Bool.false_eq_true, if_false, withoutAll_eq hd,
      chain_iff b hb, DescTerm]
  | .agg ⟨_, .call _⟩, _, h, _ => by
    obtain ⟨a, ha, rfl⟩ := inv_agg h
    exact absurd ha inv_aggCall
  | .arith op l r, _, h, ρ => by
    obtain ⟨l', r', hl, hr, rfl⟩ := inv_arith h
    simp only [descendTerm, seq_eq_ok, descendTerm_iff l hl, descendTerm_iff r hr, DescTerm]
  | .var _, _, h, _ | .integer _, _, h, _ | .decimal _, _, h, _ | .string _, _, h, _
  | .bool _, _, h, _ | .contextField _, _, h, _ | .wildcard, _, h, _ => by
    simp only [Term.toSpec, pure_eq_ok] at h
    subst h
    simp [descendTerm, DescTerm, pure_eq_ok]
  | .entity _ _, _, h, _ => by
    simp only [Term.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, rfl⟩ := h
    simp [descendTerm, DescTerm, pure_eq_ok]
  | .scopeField p, _, h, _ => by
    unfold Term.toSpec at h
    split at h <;> simp_all [pure_eq_ok, throw_ne_ok] <;> subst h <;>
      simp [descendTerm, DescTerm, pure_eq_ok]
  | .array _, _, h, _ => absurd h throw_ne_ok
  | .paramRef _, _, h, _ => absurd h throw_ne_ok
  | .binderRef _, _, h, _ => absurd h throw_ne_ok

end

/-! ## The scoping pass -/

theorem rr_sub_fv : (φ : SFormula) → ∀ x ∈ rr φ, x ∈ φ.fv
  | .pred _ _ args, x, hx => by
    have := mem_predVars.mp hx
    obtain ⟨p, hp⟩ := this
    exact Dogwood.Thm.mem_argsFv_of_mem hp x (by simp [Dogwood.Spec.Temporal.Term.fv])
  | .tp _, x, hx => by simpa [rr, Formula.fv] using hx
  | .cmp op l r, x, hx => by
    cases op <;> simp only [rr, List.not_mem_nil] at hx
    simp only [Option.mem_toList] at hx
    exact Dogwood.Thm.eqRestricted_mem_fv hx
  | .not _, _, hx => by simp [rr] at hx
  | .formerly _ φ, x, hx => rr_sub_fv φ x hx
  | .previous _ φ, x, hx => rr_sub_fv φ x hx
  | .since _ _ ψ, x, hx => by
    simp only [Formula.fv, List.mem_append]
    exact .inr (rr_sub_fv ψ x hx)
  | .exist y φ, x, hx => by
    simp only [rr, List.mem_filter] at hx
    simp only [Formula.fv, List.mem_filter]
    exact ⟨rr_sub_fv φ x hx.1, hx.2⟩
  | .and φ ψ, x, hx => by
    simp only [rr, List.mem_append] at hx
    simp only [Formula.fv, List.mem_append]
    exact hx.imp (rr_sub_fv φ x) (rr_sub_fv ψ x)

theorem and_and_and_comm' {a b c d : Prop} : ((a ∧ b) ∧ (c ∧ d)) ↔ ((a ∧ c) ∧ (b ∧ d)) :=
  ⟨fun ⟨⟨ha, hb⟩, hc, hd⟩ => ⟨⟨ha, hc⟩, hb, hd⟩, fun ⟨⟨ha, hc⟩, hb, hd⟩ => ⟨⟨ha, hb⟩, hc, hd⟩⟩

theorem rejectReservedBinder_name {n : String} :
    rejectReservedBinder (.name n) = .ok () ↔ n ∉ reserved := by
  simp only [rejectReservedBinder]
  by_cases h : n ∈ reservedBinderNames <;> simp [h, throw_ne_ok, pure_eq_ok, reserved]

theorem reservedAll_ok : {vs : List TypedBinder} → {dom : List Binder} →
    vs.mapM TypedBinder.toSpec = .ok dom →
    ((vs.forM fun v => rejectReservedBinder v.slot) = .ok () ↔ ∀ v ∈ dom, v.name ∉ reserved)
  | [], dom, h => by
    simp only [List.mapM_nil, pure_eq_ok] at h
    subst h
    simp [List.forM, pure, Except.pure]
  | v :: vs, dom, h => by
    simp only [List.mapM_cons, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    have ih := reservedAll_ok hxs
    rw [forM_eq_ok] at ih ⊢
    simp only [List.mem_cons, forall_eq_or_imp, (toSpec_binder hx).1, rejectReservedBinder_name, ih]

theorem binders_noSigil : {vs : List TypedBinder} → {dom : List Binder} →
    vs.mapM TypedBinder.toSpec = .ok dom → vs.any (slotIsSigil ·.slot) = false
  | [], _, _ => rfl
  | v :: vs, dom, h => by
    simp only [List.mapM_cons, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    show (slotIsSigil v.slot || vs.any (slotIsSigil ·.slot)) = false
    rw [(toSpec_binder hx).1, binders_noSigil hxs]
    rfl

theorem checkSummand_name {s : String} {vs : List TypedBinder} :
    checkSummand (some (.name s)) vs = .ok () ↔ s ∈ slotNames vs := by
  simp only [checkSummand]
  by_cases h : s ∈ slotNames vs <;> simp [h, throw_ne_ok, pure_eq_ok]

theorem checkAggBound_ok {inner : List String} {vs : List TypedBinder} {body : Condition} :
    checkAggBound inner vs body = .ok () ↔ ∀ y ∈ condFree body, y ∈ inner := by
  have key : ((condFree body).filter fun y => !inner.contains y) = [] ↔
      ∀ y ∈ condFree body, y ∈ inner := by
    rw [filter_nil_iff]; simp
  rw [← key]
  unfold checkAggBound
  least_split

theorem checkForOccur_ok {vs : List TypedBinder} {body : Condition} :
    checkForOccur vs body = .ok () ↔ ∀ n ∈ slotNames vs, n ∈ condFree body := by
  unfold checkForOccur
  rw [forM_eq_ok]
  refine forall_congr' fun n => imp_congr_right fun _ => ?_
  split <;> rename_i h <;> simp_all [throw_ne_ok, pure_eq_ok]

theorem checkForRestricted_ok {vs : List TypedBinder} {body : Condition} :
    checkForRestricted vs body = .ok () ↔ ∀ n ∈ slotNames vs, n ∈ condRR body := by
  unfold checkForRestricted
  rw [forM_eq_ok]
  refine forall_congr' fun n => imp_congr_right fun _ => ?_
  split <;> rename_i h <;> simp_all [throw_ne_ok, pure_eq_ok]

theorem checkAggregation_ok {bound : List String} {summand : Option BinderSlot}
    {vs : List TypedBinder} {dom : List Binder} {b : Condition} {r : Option (List String)}
    (hd : vs.mapM TypedBinder.toSpec = .ok dom) (hs : (summand.map slotIsSigil).getD false = false) :
    checkAggregation bound summand vs b = .ok r ↔
      r = some (bound ++ slotNames vs) ∧ (vs.forM fun v => rejectReservedBinder v.slot) = .ok () ∧
      checkSummand summand vs = .ok () ∧ checkAggBound (bound ++ slotNames vs) vs b = .ok () ∧
      checkForOccur vs b = .ok () ∧ checkForRestricted vs b = .ok () := by
  unfold checkAggregation
  rw [hs, binders_noSigil hd]
  simp only [Bool.or_false, Bool.false_eq_true, if_false, seq_eq_ok, pure_eq_ok]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, rfl⟩; exact ⟨rfl, h₁, h₂, h₃, h₄, h₅⟩
  · rintro ⟨rfl, h₁, h₂, h₃, h₄, h₅⟩; exact ⟨h₁, h₂, h₃, h₄, h₅, rfl⟩

theorem checkExistsSafe_ok {v : TypedBinder} {c : Condition} {x : Binder} {a : SFormula}
    (hv : v.slot = .name x.name) (ha : c.toFormula = .ok a) :
    checkExistsSafe v c = .ok () ↔ x.name ∈ rr a := by
  simp only [checkExistsSafe, hv, condHasSigil_eq c ha, condRR_eq c ha, Bool.false_eq_true,
    if_false]
  by_cases h : x.name ∈ rr a <;> simp [h, pure_eq_ok, throw_ne_ok]

theorem rejectNestedAgg_iff {t : Term} {t' : STerm} (h : t.toSpec = .ok t') :
    rejectNestedAgg t = .ok () ↔ IsPlain t' := by
  cases t with
  | agg a =>
    obtain ⟨sp, k⟩ := a
    obtain ⟨a', _, rfl⟩ := inv_agg h
    simp [rejectNestedAgg, IsPlain, throw_ne_ok]
  | arith op l r =>
    obtain ⟨l', r', _, _, rfl⟩ := inv_arith h
    simp [rejectNestedAgg, IsPlain, throw_ne_ok]
  | array _ => exact absurd h throw_ne_ok
  | paramRef _ => exact absurd h throw_ne_ok
  | binderRef _ => exact absurd h throw_ne_ok
  | entity _ _ =>
    simp only [Term.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, rfl⟩ := h
    simp [rejectNestedAgg, IsPlain, pure_eq_ok]
  | scopeField p =>
    unfold Term.toSpec at h
    split at h <;> simp_all [pure_eq_ok, throw_ne_ok] <;> subst h <;>
      simp [rejectNestedAgg, IsPlain, pure_eq_ok]
  | _ =>
    simp only [Term.toSpec, pure_eq_ok] at h
    subst h
    simp [rejectNestedAgg, IsPlain, pure_eq_ok]

theorem predArgs_ok : {args : List NamedArg} → {args' : List (Dogwood.Spec.Path × STerm)} →
    NamedArg.toSpecList args = .ok args' →
    ((args.forM fun a => rejectNestedAgg a.value) = .ok () ↔ ∀ a ∈ args', IsPlain a.2)
  | [], _, h => by
    rw [inv_args_nil h]
    simp [List.forM, pure, Except.pure]
  | ⟨n, t⟩ :: rest, _, h => by
    obtain ⟨t', rest', ht, hr, rfl⟩ := inv_args_cons h
    have ih := predArgs_ok hr
    rw [forM_eq_ok] at ih ⊢
    simp only [List.mem_cons, forall_eq_or_imp, rejectNestedAgg_iff ht, ih]

mutual

theorem checkCondition_iff : (c : Condition) → {φ : SFormula} → c.toFormula = .ok φ →
    (bound : List String) → (∀ y ∈ φ.fv, y ∈ bound) →
    (checkCondition bound c = .ok () ↔ FactsF φ ∧ WF φ)
  | ⟨_, k⟩, _, h, bound, hb => checkKind_iff k h bound hb

theorem checkKind_iff : (k : ConditionKind) → {φ : SFormula} → ConditionKind.toFormula k = .ok φ →
    (bound : List String) → (∀ y ∈ φ.fv, y ∈ bound) →
    (checkKind bound k = .ok () ↔ FactsF φ ∧ WF φ)
  | .and l r, _, h, bound, hb => by
    obtain ⟨a, b, ha, hb', rfl⟩ := inv_and h
    simp only [Formula.fv, List.mem_append] at hb
    rw [checkKind, seq_eq_ok, checkCondition_iff l ha bound (fun y hy => hb y (.inl hy)),
      checkCondition_iff r hb' bound (fun y hy => hb y (.inr hy))]
    exact and_and_and_comm'
  | .since l _ r, _, h, bound, hb => by
    obtain ⟨a, _, b, ha, _, hb', rfl⟩ := inv_since h
    simp only [Formula.fv, List.mem_append] at hb
    rw [checkKind, seq_eq_ok, checkCondition_iff l ha bound (fun y hy => hb y (.inl hy)),
      checkCondition_iff r hb' bound (fun y hy => hb y (.inr hy))]
    exact and_and_and_comm'
  | .not c, _, h, bound, hb => by
    obtain ⟨a, ha, rfl⟩ := inv_not h
    exact checkCondition_iff c ha bound hb
  | .formerly _ c, _, h, bound, hb => by
    obtain ⟨_, a, _, ha, rfl⟩ := inv_formerly h
    exact checkCondition_iff c ha bound hb
  | .previous _ c, _, h, bound, hb => by
    obtain ⟨_, a, _, ha, rfl⟩ := inv_previous h
    exact checkCondition_iff c ha bound hb
  | .exists v c, _, h, bound, hb => by
    obtain ⟨x, a, hv, ha, rfl⟩ := inv_exists h
    have hb' : ∀ y ∈ a.fv, y ∈ bound ++ [x.name] := by
      intro y hy
      by_cases hyx : y = x.name
      · simp [hyx]
      · exact List.mem_append_left _ (hb y (by simp [Formula.fv, hy, hyx]))
    simp only [checkKind, seq_eq_ok, hv]
    rw [rejectReservedBinder_name, checkExistsSafe_ok hv ha, checkCondition_iff c ha _ hb']
    simp only [FactsF, WF]
    constructor
    · rintro ⟨h₁, h₂, h₃, h₄⟩
      exact ⟨⟨h₂, h₃⟩, h₁, h₄⟩
    · rintro ⟨⟨h₂, h₃⟩, h₁, h₄⟩
      exact ⟨h₁, h₂, h₃, h₄⟩
  | .comparison _ l r, _, h, bound, hb => by
    obtain ⟨l', r', hl, hr, rfl⟩ := inv_cmp h
    simp only [Formula.fv, List.mem_append] at hb
    rw [checkKind, seq_eq_ok, checkOperand_iff l hl bound (fun y hy => hb y (.inl hy)),
      checkOperand_iff r hr bound (fun y hy => hb y (.inr hy))]
    exact and_and_and_comm'
  | .predicate p, _, h, _, _ => by
    obtain ⟨_, _, _, _, args⟩ := p
    obtain ⟨_, args', ha, rfl⟩ := inv_pred h
    simp only [checkKind, predArgs_ok ha, FactsF, WF, true_and]
  | .tp v, _, h, _, _ => by
    obtain ⟨n, rfl, rfl⟩ := inv_tp h
    simp only [checkKind, rejectReservedBinder_name, FactsF, WF, true_and]
  | .or _ _, _, h, _, _ => absurd h inv_or
  | .call _, _, h, _, _ => absurd h inv_call
  | .sigilRef _ _, _, h, _, _ => absurd h inv_sigil
  | .refine _ _ _, _, h, _, _ => absurd h inv_refine

theorem checkOperand_iff : (t : Term) → {t' : STerm} → t.toSpec = .ok t' → (bound : List String) →
    (∀ y ∈ t'.fv, y ∈ bound) → (checkOperand bound t = .ok () ↔ TermFacts t' ∧ TermWF t')
  | .agg ⟨_, k⟩, _, h, bound, hb => by
    obtain ⟨a, ha, rfl⟩ := inv_agg h
    exact checkAgg_iff k ha bound hb
  | .arith _ l r, _, h, bound, hb => by
    obtain ⟨l', r', hl, hr, rfl⟩ := inv_arith h
    simp only [Dogwood.Spec.Temporal.Term.fv, List.mem_append] at hb
    rw [checkOperand, seq_eq_ok, checkOperand_iff l hl bound (fun y hy => hb y (.inl hy)),
      checkOperand_iff r hr bound (fun y hy => hb y (.inr hy))]
    exact and_and_and_comm'
  | .array _, _, h, _, _ => absurd h throw_ne_ok
  | .paramRef _, _, h, _, _ => absurd h throw_ne_ok
  | .binderRef _, _, h, _, _ => absurd h throw_ne_ok
  | .entity _ _, _, h, _, _ => by
    simp only [Term.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, rfl⟩ := h
    simp [checkOperand, rejectNestedAgg, TermFacts, TermWF, pure_eq_ok]
  | .scopeField p, _, h, _, _ => by
    unfold Term.toSpec at h
    split at h <;> simp_all [pure_eq_ok, throw_ne_ok] <;> subst h <;>
      simp [checkOperand, rejectNestedAgg, TermFacts, TermWF, pure_eq_ok]
  | .var _, _, h, _, _ | .integer _, _, h, _, _ | .decimal _, _, h, _, _ | .string _, _, h, _, _
  | .bool _, _, h, _, _ | .contextField _, _, h, _, _ | .wildcard, _, h, _, _ => by
    simp only [Term.toSpec, pure_eq_ok] at h
    subst h
    simp [checkOperand, rejectNestedAgg, TermFacts, TermWF, pure_eq_ok]

theorem checkAgg_iff : (k : AggExprKind) → {a : SAggregate} → AggExprKind.toSpec k = .ok a →
    (bound : List String) → (∀ y ∈ a.fv, y ∈ bound) →
    (checkAgg bound k = .ok () ↔ TermFacts (.agg a) ∧ TermWF (.agg a))
  | .count vs b, _, h, bound, hb => by
    obtain ⟨dom, body, hd, hbody, rfl⟩ := inv_count h
    have hn := toSpec_binders hd
    have hb' : ∀ y ∈ body.fv, y ∈ bound ++ slotNames vs := by
      intro y hy
      by_cases hyd : y ∈ dom.map (·.name)
      · exact List.mem_append_right _ (hn ▸ hyd)
      · have hyd' : ∀ x ∈ dom, ¬x.name = y := fun x hx he => hyd (he ▸ List.mem_map_of_mem hx)
        exact List.mem_append_left _
          (hb y (by simp only [Dogwood.Spec.Temporal.Aggregate.fv, List.mem_filter, hy,
            true_and]; simpa using hyd'))
    simp only [checkAgg, bind_eq_ok]
    constructor
    · rintro ⟨r, hr, hm⟩
      obtain ⟨rfl, h₁, -, -, -, h₅⟩ := (checkAggregation_ok hd rfl).mp hr
      rw [reservedAll_ok hd] at h₁
      rw [checkForRestricted_ok, condRR_eq b hbody, hn] at h₅
      obtain ⟨f, w⟩ := (checkCondition_iff b hbody _ hb').mp hm
      exact ⟨⟨fun v hv => h₅ v.name (List.mem_map_of_mem hv), f⟩, h₁, w⟩
    · rintro ⟨⟨h₅, f⟩, h₁, w⟩
      refine ⟨_, (checkAggregation_ok hd rfl).mpr ⟨rfl, (reservedAll_ok hd).mpr h₁, rfl,
        checkAggBound_ok.mpr (by rwa [condFree_eq b hbody]), ?_, ?_⟩,
        (checkCondition_iff b hbody _ hb').mpr ⟨f, w⟩⟩
      · rw [checkForOccur_ok, condFree_eq b hbody, hn]
        intro n hn'
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hn'
        exact rr_sub_fv body _ (h₅ v hv)
      · rw [checkForRestricted_ok, condRR_eq b hbody, hn]
        intro n hn'
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hn'
        exact h₅ v hv
  | .sum s vs b, _, h, bound, hb => by
    obtain ⟨n, dom, body, rfl, hd, hbody, rfl⟩ := inv_sum h
    have hn := toSpec_binders hd
    have hb' : ∀ y ∈ body.fv, y ∈ bound ++ slotNames vs := by
      intro y hy
      by_cases hyd : y ∈ dom.map (·.name)
      · exact List.mem_append_right _ (hn ▸ hyd)
      · have hyd' : ∀ x ∈ dom, ¬x.name = y := fun x hx he => hyd (he ▸ List.mem_map_of_mem hx)
        exact List.mem_append_left _
          (hb y (by simp only [Dogwood.Spec.Temporal.Aggregate.fv, List.mem_filter, hy,
            true_and]; simpa using hyd'))
    simp only [checkAgg, bind_eq_ok]
    constructor
    · rintro ⟨r, hr, hm⟩
      obtain ⟨rfl, h₁, h₂, -, -, h₅⟩ := (checkAggregation_ok hd rfl).mp hr
      rw [reservedAll_ok hd] at h₁
      rw [checkSummand_name, hn] at h₂
      rw [checkForRestricted_ok, condRR_eq b hbody, hn] at h₅
      obtain ⟨f, w⟩ := (checkCondition_iff b hbody _ hb').mp hm
      exact ⟨⟨fun v hv => h₅ v.name (List.mem_map_of_mem hv), f⟩, h₁, h₂, w⟩
    · rintro ⟨⟨h₅, f⟩, h₁, h₂, w⟩
      refine ⟨_, (checkAggregation_ok hd rfl).mpr ⟨rfl, (reservedAll_ok hd).mpr h₁,
        checkSummand_name.mpr (hn ▸ h₂),
        checkAggBound_ok.mpr (by rwa [condFree_eq b hbody]), ?_, ?_⟩,
        (checkCondition_iff b hbody _ hb').mpr ⟨f, w⟩⟩
      · rw [checkForOccur_ok, condFree_eq b hbody, hn]
        intro n hn'
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hn'
        exact rr_sub_fv body _ (h₅ v hv)
      · rw [checkForRestricted_ok, condRR_eq b hbody, hn]
        intro n hn'
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hn'
        exact h₅ v hv
  | .call _, _, h, _, _ => absurd h inv_aggCall

end

/-! ## The checks of a leaf -/

theorem checkLeafClosed_ok {c : Condition} {φ : SFormula} (h : c.toFormula = .ok φ) :
    checkLeafClosed c = .ok () ↔ φ.fv = [] := by
  rw [← condFree_eq c h]
  unfold checkLeafClosed
  least_split

/-- **The temporal static checks decide closed, well-formed, left-to-right safety.** A leaf
that projects to the formula `φ` passes `checkLeaf` iff `φ` is safe with each `&&` chain read
left to right, has no free variable, and is well formed (`WF`). -/
theorem checkLeaf_iff {c : Condition} {φ : SFormula} (h : c.toFormula = .ok φ) :
    checkLeaf c = .ok () ↔ SafeLR (fun _ => False) φ ∧ φ.fv = [] ∧ WF φ := by
  have hR : (fun _ : String => False) = (· ∈ ([] : List String)) := pred_ext fun _ => by simp
  rw [hR, ← chainF_factsF_iff]
  simp only [checkLeaf, seq_eq_ok, checkLeafClosed_ok h, checkDemands, condHasSigil_eq c h,
    Bool.false_eq_true, if_false, chain_iff c h]
  constructor
  · rintro ⟨hc, hfv, hch⟩
    obtain ⟨f, w⟩ := (checkCondition_iff c h [] (by simp [hfv])).mp hc
    exact ⟨⟨hch, f⟩, hfv, w⟩
  · rintro ⟨⟨hch, f⟩, hfv, w⟩
    exact ⟨(checkCondition_iff c h [] (by simp [hfv])).mpr ⟨f, w⟩, hfv, hch⟩

/-- **Soundness of the temporal static checks.** A leaf that `checkLeaf` accepts is safe in the
specification's sense. -/
theorem checkLeaf_isSafe {c : Condition} {φ : SFormula} (hc : checkLeaf c = .ok ())
    (h : c.toFormula = .ok φ) : φ.IsSafe :=
  safeLR_isSafe ((checkLeaf_iff h).mp hc).1

/-- The executable form: `safeB` accepts every leaf `checkLeaf` accepts. -/
theorem checkLeaf_safeB {c : Condition} {φ : SFormula} (hc : checkLeaf c = .ok ())
    (h : c.toFormula = .ok φ) : Dogwood.Eval.isSafeB φ = true :=
  (Dogwood.Thm.isSafeB_iff φ).mpr (checkLeaf_isSafe hc h)

end Dogwood.Thm.Frontend.Macros
