import Dogwood.Eval.Typing

/-!
# The typing check decides typing

`Term.check?_ok_iff`: `Term.check?` computes exactly the sort of a well-typed term.
`Formula.check_eq_nil_iff`: `Formula.check` finds no problem exactly when the condition is
well-typed.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Eval

theorem acceptsB_iff (ft : FieldTy) (τ : TType) : acceptsB ft τ = true ↔ ft.Accepts τ := by
  cases ft <;> simp [acceptsB, FieldTy.Accepts]

theorem withinB_iff (ft : FieldTy) (τ : TType) : withinB ft τ = true ↔ ft.Within τ := by
  cases ft with
  | cedar ty => simp [withinB, FieldTy.Within]
  | entities etys =>
    simp only [withinB, FieldTy.Within, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true, beq_iff_eq, ne_eq]

theorem eqCompatibleB_iff (l r : Term) (τ₁ τ₂ : TType) :
    eqCompatibleB l r τ₁ τ₂ = true ↔ EqCompatible l r τ₁ τ₂ := by
  unfold eqCompatibleB EqCompatible
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
  refine or_congr_right (and_congr_right fun _ => ?_)
  constructor
  · intro h
    split at h
    · rename_i e₁ e₂; exact ⟨e₁, e₂, rfl, rfl⟩
    · cases h
  · rintro ⟨e₁, e₂, rfl, rfl⟩; rfl

theorem isOrder_iff (op : CmpOp) : op.isOrder = true ↔ op.IsOrder := by
  cases op <;> simp [CmpOp.isOrder, CmpOp.IsOrder]

theorem simple_iff (t : Term) : t.simple = true ↔ t.Simple := by
  cases t <;> simp [Term.simple, Term.Simple]

theorem pinsTypedB_iff (C : TypingCtx) (sig : EventSignature) :
    pinsTypedB C sig = true ↔ sig.PinsTyped C := by
  simp only [pinsTypedB, EventSignature.PinsTyped, List.all_eq_true]
  refine forall_congr' fun pin => imp_congr_right fun _ => ?_
  cases h₁ : sig.field? pin.field <;> cases h₂ : pin.ref.sort? { C with facts := [] } <;>
    simp [acceptsB_iff]

theorem Term.checkSimple?_ok_iff (C : TypingCtx) (Γ : Bindings) : (t : Term) → t.Simple →
    (τ : TType) → (t.checkSimple? C Γ = .ok τ ↔ Term.Typed C Γ t τ)
  | .entity uid, _, τ => by
    simp only [Term.checkSimple?]
    split
    · rename_i h
      constructor
      · intro h'; cases h'; exact .entity h
      · intro h'; cases h'; rfl
    · rename_i h
      constructor
      · intro h'; cases h'
      · intro h'; cases h'; rename_i h''; exact absurd h'' h
  | .long _, _, τ => by
    simp only [Term.checkSimple?, Except.ok.injEq]
    constructor
    · rintro rfl; exact .long
    · intro h; cases h; rfl
  | .decimal s, _, τ => by
    simp only [Term.checkSimple?]
    split
    · rename_i h
      constructor
      · intro h'; cases h'; exact .decimal h
      · intro h'; cases h'; rfl
    · rename_i h
      constructor
      · intro h'; cases h'
      · intro h'; cases h'; rename_i h''; exact absurd h'' h
  | .string _, _, τ => by
    simp only [Term.checkSimple?, Except.ok.injEq]
    constructor
    · rintro rfl; exact .string
    · intro h; cases h; rfl
  | .bool _, _, τ => by
    simp only [Term.checkSimple?, Except.ok.injEq]
    constructor
    · rintro rfl; exact .bool
    · intro h; cases h; rfl
  | .context p, _, τ => by
    simp only [Term.checkSimple?]
    split
    · rename_i ty h
      by_cases hs : ty.temporalSupported = true
      · simp only [hs, if_true, Except.ok.injEq]
        constructor
        · intro h'; subst h'; exact .context h hs
        · intro h'; cases h' with
          | context h'' _ => rw [h] at h''; cases h''; rfl
      · simp only [hs, Bool.false_eq_true, if_false, reduceCtorEq, false_iff]
        intro h'; cases h' with
        | context h'' hs' => rw [h] at h''; cases h''; exact hs hs'
    · rename_i h
      constructor
      · intro h'; cases h'
      · intro h'; cases h'; rename_i h''; rw [h] at h''; cases h''
  | .scope r [], _, τ => by
    simp only [Term.checkSimple?, Except.ok.injEq]
    constructor
    · rintro rfl; exact .scopeRoot
    · intro h
      cases h with
      | scopeRoot => rfl
      | scopeAttr h _ _ => exact absurd rfl h
  | .scope r (a :: p), _, τ => by
    simp only [Term.checkSimple?]
    split
    · rename_i ty h
      by_cases hs : ty.temporalSupported = true
      · simp only [hs, if_true, Except.ok.injEq]
        constructor
        · intro h'; subst h'; exact .scopeAttr (by simp) h hs
        · intro h'
          cases h' with
          | scopeAttr _ h'' _ => rw [h] at h''; cases h''; rfl
      · simp only [hs, Bool.false_eq_true, if_false, reduceCtorEq, false_iff]
        intro h'
        cases h' with
        | scopeAttr _ h'' hs' => rw [h] at h''; cases h''; exact hs hs'
    · rename_i h
      constructor
      · intro h'; cases h'
      · intro h'
        cases h' with
        | scopeAttr _ h'' _ => rw [h] at h''; cases h''
  | .var x, _, τ => by
    simp only [Term.checkSimple?]
    split
    · rename_i τ' h
      simp only [Except.ok.injEq]
      constructor
      · rintro rfl; exact .var h
      · intro h'; cases h'; rename_i h''; rw [h] at h''; cases h''; rfl
    · rename_i h
      constructor
      · intro h'; cases h'
      · intro h'; cases h'; rename_i h''; rw [h] at h''; cases h''
  | .wildcard, _, τ => by
    simp only [Term.checkSimple?]
    constructor
    · intro h; cases h
    · intro h; cases h
  | .agg _, h, _ => h.elim
  | .arith _ _ _, h, _ => h.elim

/-- One predicate argument is checked exactly when it is well-typed. -/
theorem argCheck1_iff {C : TypingCtx} {Γ : Bindings} {sig : EventSignature} {p : Path}
    {t : Term} : Formula.argCheck C Γ sig (p, t) = [] ↔ Formula.ArgTyped C Γ sig (p, t) := by
  dsimp only [Formula.argCheck]
  split
  · rename_i hfd
    simp only [List.cons_ne_nil, false_iff]
    intro h
    cases h with
    | wildcard h' => rw [hfd] at h'; cases h'
    | var h' _ _ => rw [hfd] at h'; cases h'
    | term h' _ _ _ _ _ => rw [hfd] at h'; cases h'
  · rename_i fd hfd
    have generic : t ≠ .wildcard → (∀ x, t ≠ .var x) →
        ((match t.checkSimple? C Γ with
          | .error f => [f]
          | .ok τ => if acceptsB fd.ty τ then [] else [Finding.argument]) = [] ↔
          Formula.ArgTyped C Γ sig (p, t)) := by
      intro hnw hnv
      split
      · rename_i f h
        simp only [reduceCtorEq, false_iff]
        intro h'
        cases h' with
        | wildcard _ => exact hnw rfl
        | var _ _ _ => exact hnv _ rfl
        | term _ hs _ _ ht _ =>
          rw [(Term.checkSimple?_ok_iff C Γ t hs _).mpr ht] at h; cases h
      · rename_i τ h
        have hs : t.Simple := by
          cases t <;> simp_all [Term.checkSimple?, Term.Simple]
        split
        · rename_i ha
          simp only [true_iff]
          exact .term hfd hs hnv hnw ((Term.checkSimple?_ok_iff C Γ t hs _).mp h)
            ((acceptsB_iff _ _).mp ha)
        · rename_i ha
          simp only [reduceCtorEq, false_iff]
          intro h'
          cases h' with
          | wildcard _ => exact hnw rfl
          | var _ _ _ => exact hnv _ rfl
          | term hfd' _ _ _ ht ha' =>
            rw [hfd] at hfd'; cases hfd'
            rw [(Term.checkSimple?_ok_iff C Γ t hs _).mpr ht] at h; cases h
            exact ha ((acceptsB_iff _ _).mpr ha')
    split
    · simp only [true_iff]; exact .wildcard hfd
    · rename_i x
      split
      · rename_i h
        simp only [reduceCtorEq, false_iff]
        intro h'
        cases h' with
        | var _ h'' _ => rw [h] at h''; cases h''
        | term _ _ hv _ _ _ => exact hv x rfl
      · rename_i τ h
        split
        · rename_i hw
          simp only [true_iff]; exact .var hfd h ((withinB_iff _ _).mp hw)
        · rename_i hw
          simp only [reduceCtorEq, false_iff]
          intro h'
          cases h' with
          | var hfd' h'' hw' =>
            rw [hfd] at hfd'; cases hfd'
            rw [h] at h''; cases h''
            exact hw ((withinB_iff _ _).mpr hw')
          | term _ _ hv _ _ _ => exact hv x rfl
    · rename_i hnw hnv
      exact generic hnw (fun x h => hnv x h)

theorem Formula.argsCheck_eq_nil_iff (C : TypingCtx) (Γ : Bindings) (sig : EventSignature) :
    (args : List (Path × Term)) →
      (Formula.argsCheck C Γ sig args = [] ↔ ∀ arg ∈ args, Formula.ArgTyped C Γ sig arg)
  | [] => by simp [Formula.argsCheck]
  | (p, t) :: args => by
    rw [Formula.argsCheck, List.append_eq_nil_iff, Formula.argsCheck_eq_nil_iff C Γ sig args,
      List.forall_mem_cons, argCheck1_iff]

/-- A comparison operand has no problem exactly when it has a sort. -/
theorem Term.problems_eq_nil_iff (C : TypingCtx) (Γ : Bindings) : (t : Term) →
    (Term.problems C Γ t = [] ↔ ∃ τ, Term.check? C Γ t = .ok τ)
  | .agg a => by
    simp only [Term.problems, Term.check?]
    split <;> simp_all
  | .arith op l r => by
    have ihl := Term.problems_eq_nil_iff C Γ l
    have ihr := Term.problems_eq_nil_iff C Γ r
    simp only [Term.problems, Term.check?]
    cases hl : Term.check? C Γ l <;> cases hr : Term.check? C Γ r
    · simp_all
    · simp_all
    · simp_all
    · simp only
      split
      · simp
      · split <;> simp
  | .wildcard => by simp [Term.problems, Term.check?]
  | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _ | .scope _ _ | .var _ => by
    simp only [Term.problems, Term.check?]
    split <;> simp_all

mutual

theorem Term.check?_ok_iff (C : TypingCtx) (Γ : Bindings) : (t : Term) → (τ : TType) →
    (t.check? C Γ = .ok τ ↔ Term.Typed C Γ t τ)
  | .agg a, τ => by
    have ih := Aggregate.check_eq_nil_iff C Γ a
    simp only [Term.check?]
    split
    · rename_i h
      simp only [Except.ok.injEq]
      constructor
      · rintro rfl; exact .agg (ih.mp h)
      · intro h'; cases h'; rfl
    · rename_i f fs h
      constructor
      · intro h'; cases h'
      · intro h'; cases h'; rename_i h''; rw [ih.mpr h''] at h; cases h
  | .arith op l r, τ => by
    have ihl := Term.check?_ok_iff C Γ l
    have ihr := Term.check?_ok_iff C Γ r
    simp only [Term.check?]
    split
    · rename_i f h
      constructor
      · intro h'; cases h'
      · intro h'
        cases h'; rename_i hl _
        rw [(ihl _).mpr hl] at h; cases h
    · rename_i f h _
      constructor
      · intro h'; cases h'
      · intro h'
        cases h'; rename_i _ hr
        rw [(ihr _).mpr hr] at h; cases h
    · rename_i τ₁ τ₂ hl hr
      split
      · rename_i hint
        simp only [Bool.and_eq_true, beq_iff_eq] at hint
        obtain ⟨rfl, rfl⟩ := hint
        simp only [Except.ok.injEq]
        constructor
        · rintro rfl; exact .arith ((ihl _).mp hl) ((ihr _).mp hr)
        · intro h'; cases h'; rfl
      · rename_i hint
        have no : ¬ Term.Typed C Γ (.arith op l r) τ := by
          intro h'
          cases h'; rename_i hl' hr'
          rw [(ihl _).mpr hl'] at hl; rw [(ihr _).mpr hr'] at hr
          cases hl; cases hr
          simp at hint
        split <;> simp only [reduceCtorEq, false_iff] <;> exact no

  | .wildcard, τ => by
    simp only [Term.check?]
    constructor
    · intro h; cases h
    · intro h; cases h
  | .entity _, τ | .long _, τ | .decimal _, τ | .string _, τ | .bool _, τ | .context _, τ
  | .scope _ _, τ | .var _, τ => Term.checkSimple?_ok_iff C Γ _ (by simp [Term.Simple]) τ

theorem Aggregate.check_eq_nil_iff (C : TypingCtx) (Γ : Bindings) : (a : Aggregate) →
    (a.check C Γ = [] ↔ Aggregate.Typed C Γ a)
  | .count dom body => by
    simp only [Aggregate.check]
    split
    · rename_i h
      constructor
      · intro h'; cases h'
      · intro h'; cases h'; rename_i h'' _; rw [h] at h''; cases h''
    · rename_i Δ h
      rw [Formula.check_eq_nil_iff C (Δ ++ Γ) body]
      constructor
      · intro h'; exact .count h h'
      · intro h'; cases h'; rename_i Δ' h'' hb; rw [h] at h''; cases h''; exact hb
  | .sum s dom body => by
    simp only [Aggregate.check]
    split
    · rename_i h
      constructor
      · intro h'; cases h'
      · intro h'
        cases h' with
        | sum hd _ _ => rw [h] at hd; cases hd
    · rename_i Δ h
      rw [List.append_eq_nil_iff, Formula.check_eq_nil_iff C (Δ ++ Γ) body]
      constructor
      · rintro ⟨hs, hb⟩
        refine .sum h ?_ hb
        split at hs
        · rename_i hc; exact List.contains_iff_mem.mp hc
        · cases hs
      · intro h'
        cases h' with
        | sum hd hs hb =>
          rw [h] at hd; cases hd
          refine ⟨?_, hb⟩
          rw [if_pos (List.contains_iff_mem.mpr hs)]

theorem Formula.check_eq_nil_iff (C : TypingCtx) (Γ : Bindings) : (φ : Formula) →
    (φ.check C Γ = [] ↔ Formula.WellTyped C Γ φ)
  | .and φ ψ => by
    simp only [Formula.check, List.append_eq_nil_iff, Formula.check_eq_nil_iff C Γ φ,
      Formula.check_eq_nil_iff C Γ ψ]
    constructor
    · rintro ⟨h₁, h₂⟩; exact .and h₁ h₂
    · intro h; cases h; rename_i h₁ h₂; exact ⟨h₁, h₂⟩
  | .not φ => by
    simp only [Formula.check, Formula.check_eq_nil_iff C Γ φ]
    constructor
    · intro h; exact .not h
    · intro h; cases h; assumption
  | .formerly w φ => by
    simp only [Formula.check, List.append_eq_nil_iff, Formula.check_eq_nil_iff C Γ φ]
    constructor
    · rintro ⟨hw, h⟩
      split at hw
      · rename_i hc; exact .formerly hc h
      · cases hw
    · intro h; cases h; rename_i hw h; exact ⟨by rw [if_pos hw], h⟩
  | .previous w φ => by
    simp only [Formula.check, List.append_eq_nil_iff, Formula.check_eq_nil_iff C Γ φ]
    constructor
    · rintro ⟨hw, h⟩
      split at hw
      · rename_i hc; exact .previous hc h
      · cases hw
    · intro h; cases h; rename_i hw h; exact ⟨by rw [if_pos hw], h⟩
  | .since φ w ψ => by
    simp only [Formula.check, List.append_eq_nil_iff, Formula.check_eq_nil_iff C Γ φ,
      Formula.check_eq_nil_iff C Γ ψ]
    constructor
    · rintro ⟨⟨hw, h₁⟩, h₂⟩
      split at hw
      · rename_i hc; exact .since hc h₁ h₂
      · cases hw
    · intro h
      cases h with
      | since hw h₁ h₂ => exact ⟨⟨by rw [if_pos hw], h₁⟩, h₂⟩
  | .pred a k args => by
    simp only [Formula.check]
    split
    · rename_i h
      constructor
      · intro h'; cases h'
      · intro h'
        cases h' with
        | pred hs _ _ => rw [h] at hs; cases hs
    · rename_i sig h
      rw [List.append_eq_nil_iff, Formula.argsCheck_eq_nil_iff C Γ sig args]
      constructor
      · rintro ⟨hargs, hpins⟩
        refine .pred h hargs ((pinsTypedB_iff C sig).mp ?_)
        split at hpins
        · assumption
        · cases hpins
      · intro h'
        cases h' with
        | pred hs hargs hpins =>
          rw [h] at hs; cases hs
          exact ⟨hargs, by rw [if_pos ((pinsTypedB_iff C sig).mpr hpins)]⟩
  | .cmp op l r => by
    have ihl := Term.check?_ok_iff C Γ l
    have ihr := Term.check?_ok_iff C Γ r
    simp only [Formula.check]
    split
    · rename_i τ₁ τ₂ hl hr
      have hl' := (ihl _).mp hl
      have hr' := (ihr _).mp hr
      have back : ∀ {σ₁ σ₂}, Term.Typed C Γ l σ₁ → Term.Typed C Γ r σ₂ → σ₁ = τ₁ ∧ σ₂ = τ₂ :=
        fun h₁ h₂ => by
          have e₁ := (ihl _).mpr h₁; rw [hl] at e₁; cases e₁
          have e₂ := (ihr _).mpr h₂; rw [hr] at e₂; cases e₂
          exact ⟨rfl, rfl⟩
      split
      · rename_i hord
        have hord' := (isOrder_iff op).mp hord
        split
        · rename_i hint
          simp only [Bool.and_eq_true, beq_iff_eq] at hint
          obtain ⟨rfl, rfl⟩ := hint
          simp only [true_iff]
          exact .ord hord' hl' hr'
        · rename_i hint
          have no : ¬ Formula.WellTyped C Γ (.cmp op l r) := by
            intro h'
            cases h' with
            | eq hno _ _ _ => exact hno hord'
            | ord _ h₁ h₂ =>
              obtain ⟨rfl, rfl⟩ := back h₁ h₂
              simp at hint
          split <;> simp only [reduceCtorEq, false_iff] <;> exact no
      · rename_i hord
        have hord' : ¬ op.IsOrder := fun h => hord ((isOrder_iff op).mpr h)
        split
        · rename_i hc
          simp only [true_iff]
          exact .eq hord' hl' hr' ((eqCompatibleB_iff l r τ₁ τ₂).mp hc)
        · rename_i hc
          have no : ¬ Formula.WellTyped C Γ (.cmp op l r) := by
            intro h'
            cases h' with
            | eq _ h₁ h₂ hc' =>
              obtain ⟨rfl, rfl⟩ := back h₁ h₂
              exact hc ((eqCompatibleB_iff l r _ _).mpr hc')
            | ord h _ _ => exact hord' h
          split <;> simp only [reduceCtorEq, false_iff] <;> exact no
    · rename_i hne
      have hpl := Term.problems_eq_nil_iff C Γ l
      have hpr := Term.problems_eq_nil_iff C Γ r
      constructor
      · intro h
        obtain ⟨h₁, h₂⟩ := List.append_eq_nil_iff.mp h
        obtain ⟨τ₁, e₁⟩ := hpl.mp h₁
        obtain ⟨τ₂, e₂⟩ := hpr.mp h₂
        exact (hne τ₁ τ₂ e₁ e₂).elim
      · intro h'
        cases h' with
        | eq _ hl hr _ => exact (hne _ _ ((ihl _).mpr hl) ((ihr _).mpr hr)).elim
        | ord _ hl hr => exact (hne _ _ ((ihl _).mpr hl) ((ihr _).mpr hr)).elim
  | .exist x φ => by
    simp only [Formula.check]
    split
    · rename_i h
      constructor
      · intro h'; cases h'
      · intro h'; cases h'; rename_i b h'' _; rw [h] at h''; cases h''
    · rename_i b h
      rw [Formula.check_eq_nil_iff C (b :: Γ) φ]
      constructor
      · intro h'; exact .exist h h'
      · intro h'; cases h'; rename_i b' h'' hb; rw [h] at h''; cases h''; exact hb
  | .tp x => by
    simp only [Formula.check]
    cases h : Γ.lookup x with
    | none =>
      simp only [reduceCtorEq, false_iff]
      intro h'
      cases h' with
      | tp h'' => rw [h] at h''; cases h''
    | some τ =>
      cases τ with
      | timepoint => simp only [true_iff]; exact .tp h
      | cedar ty =>
        simp only [reduceCtorEq, false_iff]
        intro h'
        cases h' with
        | tp h'' => rw [h] at h''; cases h''

end

end Dogwood.Thm
