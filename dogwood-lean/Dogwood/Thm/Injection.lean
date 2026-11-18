import Dogwood.Thm.Restriction
import Dogwood.Spec.Temporal.Typing
import Dogwood.Spec.Temporal.Scopes

/-!
# Pin injection keeps validity

Validation checks a leaf as authored; an authorizer evaluates it after pin injection
(`Formula.injectPins`). A pin adds a predicate argument whose term is a request-side reference:
it uses no variable and restricts none. So pin injection changes no free variable and no range
restriction, keeps safety (`Formula.safe_injectPins`) and time dependence
(`Formula.monitorsTime_injectPins`), and keeps a well-typed leaf well-typed
(`Formula.wellTyped_injectPins`), because typing checks every pin of every predicate's
signature.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

section

variable (S : EventSchema)

theorem PinRef.fv_toTerm (r : PinRef) : r.toTerm.fv = [] := by cases r <;> rfl

theorem argsFv_append (a b : List (Path × Term)) :
    Formula.argsFv (a ++ b) = Formula.argsFv a ++ Formula.argsFv b := by
  induction a with
  | nil => rfl
  | cons x a ih => obtain ⟨_, t⟩ := x; simp [Formula.argsFv, ih]

theorem argsFv_pins (ps : List Pin) :
    Formula.argsFv (ps.map fun p => (p.field, p.ref.toTerm)) = [] := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [Formula.argsFv, PinRef.fv_toTerm, ih]

theorem predVars_append (a b : List (Path × Term)) : predVars (a ++ b) = predVars a ++ predVars b := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    obtain ⟨_, t⟩ := x
    cases t <;> simp [predVars, ih]

theorem predVars_pins (ps : List Pin) : predVars (ps.map fun p => (p.field, p.ref.toTerm)) = [] := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases h : p.ref <;> simp_all [predVars, PinRef.toTerm]

mutual

theorem Formula.fv_injectPins : (φ : Formula) → (φ.injectPins S).fv = φ.fv
  | .and φ ψ => by simp [Formula.injectPins, Formula.fv, Formula.fv_injectPins φ, Formula.fv_injectPins ψ]
  | .not φ => by simp [Formula.injectPins, Formula.fv, Formula.fv_injectPins φ]
  | .formerly _ φ => by simp [Formula.injectPins, Formula.fv, Formula.fv_injectPins φ]
  | .previous _ φ => by simp [Formula.injectPins, Formula.fv, Formula.fv_injectPins φ]
  | .since φ _ ψ => by
    simp [Formula.injectPins, Formula.fv, Formula.fv_injectPins φ, Formula.fv_injectPins ψ]
  | .pred _ _ _ => by simp [Formula.injectPins, Formula.fv, argsFv_append, argsFv_pins]
  | .cmp _ l r => by simp [Formula.injectPins, Formula.fv, Term.fv_injectPins l, Term.fv_injectPins r]
  | .exist _ φ => by simp [Formula.injectPins, Formula.fv, Formula.fv_injectPins φ]
  | .tp _ => rfl

theorem Term.fv_injectPins : (t : Term) → (t.injectPins S).fv = t.fv
  | .agg a => by simp [Term.injectPins, Term.fv, Aggregate.fv_injectPins a]
  | .arith _ l r => by simp [Term.injectPins, Term.fv, Term.fv_injectPins l, Term.fv_injectPins r]
  | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _ | .scope _ _ | .var _
  | .wildcard => rfl

theorem Aggregate.fv_injectPins : (a : Aggregate) → (a.injectPins S).fv = a.fv
  | .count _ body => by simp [Aggregate.injectPins, Aggregate.fv, Formula.fv_injectPins body]
  | .sum _ _ body => by simp [Aggregate.injectPins, Aggregate.fv, Formula.fv_injectPins body]

end

theorem Term.hasWildcard_injectPins : (t : Term) → (t.injectPins S).hasWildcard = t.hasWildcard
  | .arith _ l r => by
    simp [Term.injectPins, Term.hasWildcard, Term.hasWildcard_injectPins l,
      Term.hasWildcard_injectPins r]
  | .agg _ | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _ | .scope _ _
  | .var _ | .wildcard => rfl

theorem eqRestricted_injectPins (l r : Term) :
    eqRestricted? (l.injectPins S) (r.injectPins S) = eqRestricted? l r := by
  cases l <;> cases r <;>
    simp [eqRestricted?, Term.injectPins, Term.hasWildcard, Term.hasWildcard_injectPins]

theorem valueSide_injectPins (x : VarName) (l r : Term) :
    valueSide x (l.injectPins S) (r.injectPins S) = (valueSide x l r).injectPins S := by
  cases l <;> simp only [valueSide, Term.injectPins]
  split <;> rfl

/-- Pin injection restricts the same variables. -/
theorem Formula.restricts_injectPins : (φ : Formula) → (R : VarName → Prop) → (x : VarName) →
    ((φ.injectPins S).Restricts R x ↔ φ.Restricts R x)
  | .pred _ _ args, R, x => by
    simp only [Formula.injectPins, Formula.Restricts, List.mem_append, List.mem_map]
    constructor
    · rintro ⟨p, hp | ⟨pin, _, hpin⟩⟩
      · exact ⟨p, hp⟩
      · cases h : pin.ref <;> simp [h, PinRef.toTerm] at hpin
    · rintro ⟨p, hp⟩; exact ⟨p, .inl hp⟩
  | .tp _, _, _ => Iff.rfl
  | .cmp op l r, R, x => by
    cases op <;> simp only [Formula.injectPins, Formula.Restricts]
    rw [eqRestricted_injectPins, valueSide_injectPins, Term.fv_injectPins]
  | .not _, _, _ => Iff.rfl
  | .formerly _ φ, R, x => Formula.restricts_injectPins φ R x
  | .previous _ φ, R, x => Formula.restricts_injectPins φ R x
  | .since _ _ ψ, R, x => Formula.restricts_injectPins ψ R x
  | .exist y φ, R, x => by
    simp only [Formula.injectPins, Formula.Restricts]
    rw [Formula.restricts_injectPins φ]
  | .and φ ψ, R, x => by
    simp only [Formula.injectPins, Formula.Restricts]
    have hφ : ∀ T z, (φ.injectPins S).Restricts T z ↔ φ.Restricts T z :=
      fun T z => Formula.restricts_injectPins φ T z
    have hψ : ∀ T z, (ψ.injectPins S).Restricts T z ↔ ψ.Restricts T z :=
      fun T z => Formula.restricts_injectPins ψ T z
    simp only [hφ, hψ]

theorem Formula.restricted_injectPins (φ : Formula) (R : VarName → Prop) (x : VarName) :
    (φ.injectPins S).Restricted R x ↔ φ.Restricted R x := by
  simp [Formula.Restricted, Formula.restricts_injectPins]

theorem Formula.restricts_injectPins_eq (φ : Formula) (R : VarName → Prop) :
    (φ.injectPins S).Restricts R = φ.Restricts R :=
  funext fun x => propext (Formula.restricts_injectPins S φ R x)

mutual

/-- **Pin injection keeps safety.** -/
theorem Formula.safe_injectPins : (φ : Formula) → (R : VarName → Prop) →
    ((φ.injectPins S).Safe R ↔ φ.Safe R)
  | .and φ ψ, R => by
    have h : (Formula.and (φ.injectPins S) (ψ.injectPins S)).Restricts R =
        (Formula.and φ ψ).Restricts R := Formula.restricts_injectPins_eq S (.and φ ψ) R
    simp only [Formula.injectPins, Formula.Safe]
    rw [h, Formula.safe_injectPins φ, Formula.safe_injectPins ψ]
  | .not φ, R => by
    simp only [Formula.injectPins, Formula.Safe, Formula.fv_injectPins, Formula.safe_injectPins φ]
  | .formerly _ φ, R => Formula.safe_injectPins φ R
  | .previous _ φ, R => Formula.safe_injectPins φ R
  | .since φ _ ψ, R => by
    have h : (ψ.injectPins S).Restricted R = ψ.Restricted R :=
      funext fun x => propext (Formula.restricted_injectPins S ψ R x)
    simp only [Formula.injectPins, Formula.Safe, Formula.fv_injectPins, h,
      Formula.safe_injectPins φ, Formula.safe_injectPins ψ]
  | .pred _ _ _, _ => Iff.rfl
  | .tp _, _ => Iff.rfl
  | .cmp op l r, R => by
    have h : (Formula.cmp op (l.injectPins S) (r.injectPins S)).Restricted R =
        (Formula.cmp op l r).Restricted R :=
      funext fun x => propext (Formula.restricted_injectPins S (.cmp op l r) R x)
    simp only [Formula.injectPins, Formula.Safe, Term.fv_injectPins, h, Term.safe_injectPins l,
      Term.safe_injectPins r]
  | .exist x φ, R => by
    simp only [Formula.injectPins, Formula.Safe, Formula.restricts_injectPins,
      Formula.safe_injectPins φ]

theorem Term.safe_injectPins : (t : Term) → (R : VarName → Prop) →
    ((t.injectPins S).Safe R ↔ t.Safe R)
  | .agg a, R => Aggregate.safe_injectPins a R
  | .arith _ l r, R => by
    simp only [Term.injectPins, Term.Safe, Term.safe_injectPins l, Term.safe_injectPins r]
  | .entity _, _ | .long _, _ | .decimal _, _ | .string _, _ | .bool _, _ | .context _, _
  | .scope _ _, _ | .var _, _ | .wildcard, _ => Iff.rfl

theorem Aggregate.safe_injectPins : (a : Aggregate) → (R : VarName → Prop) →
    ((a.injectPins S).Safe R ↔ a.Safe R)
  | .count _ body, R => by
    simp only [Aggregate.injectPins, Aggregate.Safe, Formula.restricts_injectPins,
      Formula.safe_injectPins body]
  | .sum _ _ body, R => by
    simp only [Aggregate.injectPins, Aggregate.Safe, Formula.restricts_injectPins,
      Formula.safe_injectPins body]

end

theorem Formula.isSafe_injectPins (φ : Formula) : (φ.injectPins S).IsSafe ↔ φ.IsSafe :=
  Formula.safe_injectPins S φ _

/-! ## Time dependence -/

theorem Formula.conjuncts_injectPins : (φ : Formula) →
    (φ.injectPins S).conjuncts = φ.conjuncts.map (·.injectPins S)
  | .and φ ψ => by
    simp [Formula.injectPins, Formula.conjuncts, Formula.conjuncts_injectPins φ,
      Formula.conjuncts_injectPins ψ]
  | .not _ | .formerly _ _ | .previous _ _ | .since _ _ _ | .pred _ _ _ | .cmp _ _ _ | .exist _ _
  | .tp _ => by simp [Formula.injectPins, Formula.conjuncts]

theorem ruleWideArgs_pins (args : List (Path × Term)) (ps : List Pin) :
    (args ++ ps.map fun p => (p.field, p.ref.toTerm)).filterMap
        (fun | (_, .var x) => some x | _ => none) =
      args.filterMap (fun | (_, .var x) => some x | _ => none) := by
  rw [List.filterMap_append]
  conv => rhs; rw [← List.append_nil (List.filterMap _ args)]
  congr 1
  rw [List.filterMap_eq_nil_iff]
  intro x hx
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
  cases p.ref <;> rfl

theorem Formula.ruleWideBinders_injectPins : (φ : Formula) →
    (φ.injectPins S).ruleWideBinders = φ.ruleWideBinders
  | .and φ ψ | .since φ _ ψ => by
    simp [Formula.injectPins, Formula.ruleWideBinders, Formula.ruleWideBinders_injectPins φ,
      Formula.ruleWideBinders_injectPins ψ]
  | .formerly _ φ | .previous _ φ | .exist _ φ => by
    simp [Formula.injectPins, Formula.ruleWideBinders, Formula.ruleWideBinders_injectPins φ]
  | .pred _ _ args => by
    simp only [Formula.injectPins, Formula.ruleWideBinders]
    exact ruleWideArgs_pins _ _
  | .not _ | .cmp _ _ _ | .tp _ => by simp [Formula.injectPins, Formula.ruleWideBinders]

theorem Term.varies_injectPins (E : List VarName) : (t : Term) →
    ((t.injectPins S).Varies E ↔ t.Varies E)
  | .arith _ l r => by
    simp [Term.injectPins, Term.Varies, Term.varies_injectPins E l, Term.varies_injectPins E r]
  | .agg _ | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _ | .scope _ _
  | .var _ | .wildcard => by simp [Term.injectPins, Term.Varies]

theorem Formula.varies_injectPins (E : List VarName) : (φ : Formula) →
    ((φ.injectPins S).Varies E ↔ φ.Varies E)
  | .and φ ψ => by
    simp [Formula.injectPins, Formula.Varies, Formula.varies_injectPins E φ,
      Formula.varies_injectPins E ψ]
  | .not φ => by simp [Formula.injectPins, Formula.Varies, Formula.varies_injectPins E φ]
  | .cmp _ l r => by simp [Formula.injectPins, Formula.Varies, Term.varies_injectPins]
  | .pred _ _ _ | .tp _ | .formerly _ _ | .previous _ _ | .since _ _ _ | .exist _ _ => by
    simp [Formula.injectPins, Formula.Varies]

mutual

theorem Formula.scopesVary_injectPins : (E : List VarName) → (φ : Formula) →
    ((φ.injectPins S).ScopesVary E ↔ φ.ScopesVary E)
  | E, .and φ ψ => by
    simp [Formula.injectPins, Formula.ScopesVary, Formula.scopesVary_injectPins E φ,
      Formula.scopesVary_injectPins E ψ]
  | E, .not φ => by
    simp [Formula.injectPins, Formula.ScopesVary, Formula.scopesVary_injectPins E φ]
  | E, .formerly _ φ | E, .previous _ φ => by
    simp [Formula.injectPins, Formula.ScopesVary, Formula.varies_injectPins,
      Formula.scopesVary_injectPins E φ]
  | E, .since φ _ ψ => by
    simp [Formula.injectPins, Formula.ScopesVary, Formula.varies_injectPins,
      Formula.scopesVary_injectPins E φ, Formula.scopesVary_injectPins E ψ]
  | E, .exist x φ => by
    simp [Formula.injectPins, Formula.ScopesVary, Formula.varies_injectPins,
      Formula.scopesVary_injectPins (x.name :: E) φ]
  | E, .cmp _ l r => by
    simp [Formula.injectPins, Formula.ScopesVary, Term.scopesVary_injectPins E l,
      Term.scopesVary_injectPins E r]
  | E, .pred _ _ _ | E, .tp _ => by simp [Formula.injectPins, Formula.ScopesVary]

theorem Term.scopesVary_injectPins : (E : List VarName) → (t : Term) →
    ((t.injectPins S).ScopesVary E ↔ t.ScopesVary E)
  | E, .agg (.count _ body) => by
    simp [Term.injectPins, Aggregate.injectPins, Term.ScopesVary, Formula.varies_injectPins,
      Formula.scopesVary_injectPins E body]
  | E, .agg (.sum s _ body) => by
    simp [Term.injectPins, Aggregate.injectPins, Term.ScopesVary, Formula.varies_injectPins,
      Formula.scopesVary_injectPins (s :: E) body]
  | E, .arith _ l r => by
    simp [Term.injectPins, Term.ScopesVary, Term.scopesVary_injectPins E l,
      Term.scopesVary_injectPins E r]
  | E, .entity _ | E, .long _ | E, .decimal _ | E, .string _ | E, .bool _ | E, .context _
  | E, .scope _ _ | E, .var _ | E, .wildcard => by simp [Term.injectPins, Term.ScopesVary]

end

/-- **Pin injection keeps time dependence.** -/
theorem Formula.monitorsTime_injectPins (φ : Formula) :
    (φ.injectPins S).MonitorsTime ↔ φ.MonitorsTime := by
  simp [Formula.MonitorsTime, Formula.conjuncts_injectPins, Formula.ruleWideBinders_injectPins,
    Formula.varies_injectPins, Formula.scopesVary_injectPins]

end

/-! ## Typing -/

theorem pathType?_mono {present present' : Path → Bool} (h : ∀ q, present q = true → present' q = true) :
    ∀ (rty : Cedar.Validation.RecordType) (pre p : Path) {ty},
      pathType? present rty pre p = some ty → pathType? present' rty pre p = some ty
  | _, _, [], _, hp => by simp [pathType?] at hp
  | rty, pre, a :: p, ty, hp => by
    unfold pathType? at hp ⊢
    cases hf : rty.find? a with
    | none => simp [hf] at hp
    | some qty =>
      simp only [hf] at hp ⊢
      by_cases hr : (qty.isRequired || present (pre ++ [a])) = true
      · have hr' : (qty.isRequired || present' (pre ++ [a])) = true := by
          simp only [Bool.or_eq_true] at hr ⊢
          exact hr.imp id (h _)
        rw [if_pos hr] at hp
        rw [if_pos hr']
        cases p with
        | nil => exact hp
        | cons b p =>
          cases hg : qty.getType with
          | record rty' =>
            simp only [hg] at hp ⊢
            exact pathType?_mono h rty' (pre ++ [a]) (b :: p) hp
          | _ => simp [hg] at hp
      · rw [if_neg hr] at hp; cases hp

/-- A context's facts only add guards: a pin's reference, typed without facts, is typed with
them. -/
theorem PinRef.typed_of_sort? {C : TypingCtx} {Γ : Bindings} {r : PinRef} {τ : TType}
    (h : r.sort? { C with facts := [] } = some τ) : Term.Typed C Γ r.toTerm τ := by
  have hmono : ∀ (G : Path → Guard) (q : Path),
      decide (G q ∈ ([] : List Guard)) = true → decide (G q ∈ C.facts) = true := by
    intro G q hq; simp at hq
  cases r with
  | context p =>
    simp only [PinRef.sort?, Option.map_eq_some_iff, Option.filter_eq_some_iff] at h
    obtain ⟨ty, ⟨hty, hs⟩, rfl⟩ := h
    refine .context ?_ hs
    exact pathType?_mono (hmono (fun q => .context q)) _ _ _ hty
  | scope root p =>
    cases p with
    | nil =>
      simp only [PinRef.sort?, Option.some.injEq] at h
      subst h
      exact .scopeRoot
    | cons a p =>
      simp only [PinRef.sort?] at h
      simp only [Option.map_eq_some_iff, Option.filter_eq_some_iff] at h
      obtain ⟨ty, ⟨hty, hs⟩, rfl⟩ := h
      refine .scopeAttr (by simp) ?_ hs
      simp only [TypingCtx.scopeAttrType?, TypingCtx.scopeType] at hty ⊢
      split at hty
      · rename_i rty hrty
        exact pathType?_mono (hmono (fun q => .scope root q)) _ _ _ hty
      · cases hty

theorem pinsOf_of_signature {S : EventSchema} {a : Cedar.Spec.EntityUID} {k : String}
    {sig : EventSignature} (h : S.signature? a k = some sig) : S.pinsOf a k = sig.pins := by
  simp [EventSchema.pinsOf, h]

theorem PinRef.toTerm_simple (r : PinRef) : r.toTerm.Simple := by
  cases r <;> simp [PinRef.toTerm, Term.Simple]

mutual

/-- **Pin injection keeps a well-typed condition well-typed.** -/
theorem Formula.wellTyped_injectPins {C : TypingCtx} : {Γ : Bindings} → {φ : Formula} →
    Formula.WellTyped C Γ φ → Formula.WellTyped C Γ (φ.injectPins C.events)
  | _, _, .and h₁ h₂ => .and (Formula.wellTyped_injectPins h₁) (Formula.wellTyped_injectPins h₂)
  | _, _, .not h => .not (Formula.wellTyped_injectPins h)
  | _, _, .formerly hw h => .formerly hw (Formula.wellTyped_injectPins h)
  | _, _, .previous hw h => .previous hw (Formula.wellTyped_injectPins h)
  | _, _, .since hw h₁ h₂ =>
    .since hw (Formula.wellTyped_injectPins h₁) (Formula.wellTyped_injectPins h₂)
  | _, .pred a k args, .pred (sig := sig) hs hargs hpins => by
    simp only [Formula.injectPins, pinsOf_of_signature hs]
    refine .pred hs (fun arg harg => ?_) hpins
    rcases List.mem_append.mp harg with harg | harg
    · exact hargs arg harg
    · obtain ⟨pin, hpin, rfl⟩ := List.mem_map.mp harg
      obtain ⟨fd, τ, hfd, hτ, hacc⟩ := hpins pin hpin
      refine .term hfd (PinRef.toTerm_simple _) (fun x => by cases pin.ref <;> simp [PinRef.toTerm])
        (by cases pin.ref <;> simp [PinRef.toTerm]) (PinRef.typed_of_sort? hτ) hacc
  | _, _, .eq hno hl hr hc => by
    refine .eq hno (Term.typed_injectPins hl) (Term.typed_injectPins hr) ?_
    unfold EqCompatible at hc ⊢
    rwa [eqRestricted_injectPins]
  | _, _, .ord ho hl hr => .ord ho (Term.typed_injectPins hl) (Term.typed_injectPins hr)
  | _, _, .exist hb h => .exist hb (Formula.wellTyped_injectPins h)
  | _, _, .tp h => .tp h

theorem Term.typed_injectPins {C : TypingCtx} : {Γ : Bindings} → {t : Term} → {τ : TType} →
    Term.Typed C Γ t τ → Term.Typed C Γ (t.injectPins C.events) τ
  | _, _, _, .entity h => .entity h
  | _, _, _, .long => .long
  | _, _, _, .decimal h => .decimal h
  | _, _, _, .string => .string
  | _, _, _, .bool => .bool
  | _, _, _, .context h hs => .context h hs
  | _, _, _, .scopeRoot => .scopeRoot
  | _, _, _, .scopeAttr h₁ h₂ hs => .scopeAttr h₁ h₂ hs
  | _, _, _, .var h => .var h
  | _, _, _, .agg h => .agg (Aggregate.typed_injectPins h)
  | _, _, _, .arith h₁ h₂ => .arith (Term.typed_injectPins h₁) (Term.typed_injectPins h₂)

theorem Aggregate.typed_injectPins {C : TypingCtx} : {Γ : Bindings} → {a : Aggregate} →
    Aggregate.Typed C Γ a → Aggregate.Typed C Γ (a.injectPins C.events)
  | _, _, .count hd h => .count hd (Formula.wellTyped_injectPins h)
  | _, _, .sum hd hs h => .sum hd hs (Formula.wellTyped_injectPins h)

end

end Dogwood.Thm
