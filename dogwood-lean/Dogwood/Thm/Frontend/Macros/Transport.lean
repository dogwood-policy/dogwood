import Dogwood.Frontend.Conformance
import Dogwood.Thm.Frontend.Macros.Order

/-!
# From the crate's syntax to the specification's

An authored leaf of the crate's temporal syntax (`Surface.Temporal.Condition`) that projects
to a formula of the specification (`Condition.toFormula`) holds no macro syntax, no internal
disjunction and no array. On such a leaf, the crate's helpers compute the specification's
quantities: its free variables are the formula's (`condFree_eq`), its restricted variables are
`rr` of the formula (`condRR_eq`), it holds no sigil (`condHasSigil_eq`), and its binding
equalities are the specification's (`eqRestrictedVar_eq`).
-/

namespace Dogwood.Thm.Frontend.Macros

open Dogwood.Frontend Dogwood.Frontend.Macros Dogwood.Frontend.Surface.Temporal
open Dogwood.Spec.Temporal (Formula Binder)

abbrev SFormula := Dogwood.Spec.Temporal.Formula
abbrev STerm := Dogwood.Spec.Temporal.Term
abbrev SAggregate := Dogwood.Spec.Temporal.Aggregate

/-! ## `Except` -/

theorem bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem seq_eq_ok {ε β : Type} {x : Except ε Unit} {f : Unit → Except ε β} {b : β} :
    x >>= f = .ok b ↔ x = .ok () ∧ f () = .ok b := by
  rw [bind_eq_ok]
  constructor
  · rintro ⟨⟨⟩, h₁, h₂⟩; exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩; exact ⟨(), h₁, h₂⟩

theorem pure_eq_ok {ε α : Type} {a b : α} : (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

theorem map_eq_ok {ε α β : Type} {x : Except ε α} {f : α → β} {b : β} :
    f <$> x = .ok b ↔ ∃ a, x = .ok a ∧ f a = b := by
  cases x <;> simp [Functor.map, Except.map]

theorem throw_ne_ok {ε α : Type} {e : ε} {b : α} : (throw e : Except ε α) ≠ .ok b := by
  intro h; cases h

theorem forM_eq_ok {ε α : Type} {xs : List α} {f : α → Except ε Unit} :
    xs.forM f = .ok () ↔ ∀ x ∈ xs, f x = .ok () := by
  rw [List.forM_eq_forM]
  induction xs with
  | nil => simp [pure, Except.pure]
  | cons x xs ih =>
    rw [List.forM_cons]
    cases hx : f x <;> simp [bind, Except.bind, ih, hx]

/-! ## Inverting the projection -/

section Inversion

variable {φ : SFormula} {t' : STerm} {a' : SAggregate}

theorem toSpec_name {s : BinderSlot} {n : String} (h : s.toName = .ok n) : s = .name n := by
  cases s <;> simp_all [BinderSlot.toName, throw_ne_ok, pure_eq_ok]

theorem toSpec_binder {b : TypedBinder} {x : Binder} (h : b.toSpec = .ok x) :
    b.slot = .name x.name ∧ b.ty = x.ty := by
  obtain ⟨s, ty⟩ := b
  simp only [TypedBinder.toSpec, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨n, hn, rfl⟩ := h
  exact ⟨toSpec_name hn, rfl⟩

theorem toSpec_binders : {vs : List TypedBinder} → {dom : List Binder} →
    vs.mapM TypedBinder.toSpec = .ok dom → slotNames vs = dom.map (·.name)
  | [], dom, h => by
    simp only [List.mapM_nil, pure_eq_ok] at h
    subst h; rfl
  | v :: vs, dom, h => by
    simp only [List.mapM_cons, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    have := (toSpec_binder hx).1
    simp only [slotNames, List.filterMap_cons, this, slotName?, List.map_cons]
    exact congrArg _ (toSpec_binders hxs)

theorem inv_and {l r : Condition} (h : ConditionKind.toFormula (.and l r) = .ok φ) :
    ∃ a b, l.toFormula = .ok a ∧ r.toFormula = .ok b ∧ φ = .and a b := by
  simp only [ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  exact ⟨a, b, ha, hb, rfl⟩

theorem inv_not {c : Condition} (h : ConditionKind.toFormula (.not c) = .ok φ) :
    ∃ a, c.toFormula = .ok a ∧ φ = .not a := by
  simp only [ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a, ha, rfl⟩

theorem inv_formerly {w : WithinSpec} {c : Condition}
    (h : ConditionKind.toFormula (.formerly w c) = .ok φ) :
    ∃ w' a, w.toSpec = .ok w' ∧ c.toFormula = .ok a ∧ φ = .formerly w' a := by
  simp only [ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨w', hw, a, ha, rfl⟩ := h
  exact ⟨w', a, hw, ha, rfl⟩

theorem inv_previous {w : WithinSpec} {c : Condition}
    (h : ConditionKind.toFormula (.previous w c) = .ok φ) :
    ∃ w' a, w.toSpec = .ok w' ∧ c.toFormula = .ok a ∧ φ = .previous w' a := by
  simp only [ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨w', hw, a, ha, rfl⟩ := h
  exact ⟨w', a, hw, ha, rfl⟩

theorem inv_since {l r : Condition} {w : WithinSpec}
    (h : ConditionKind.toFormula (.since l w r) = .ok φ) :
    ∃ a w' b, l.toFormula = .ok a ∧ w.toSpec = .ok w' ∧ r.toFormula = .ok b ∧
      φ = .since a w' b := by
  simp only [ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨a, ha, w', hw, b, hb, rfl⟩ := h
  exact ⟨a, w', b, ha, hw, hb, rfl⟩

theorem inv_pred {sp : Span} {ns : List String} {act kind : String} {args : List NamedArg}
    (h : ConditionKind.toFormula (.predicate ⟨sp, ns, act, kind, args⟩) = .ok φ) :
    ∃ uid args', NamedArg.toSpecList args = .ok args' ∧ φ = .pred uid kind args' := by
  simp only [ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨uid, _, args', ha, rfl⟩ := h
  exact ⟨uid, args', ha, rfl⟩

theorem inv_cmp {op : Dogwood.Spec.Temporal.CmpOp} {l r : Term}
    (h : ConditionKind.toFormula (.comparison op l r) = .ok φ) :
    ∃ l' r', l.toSpec = .ok l' ∧ r.toSpec = .ok r' ∧ φ = .cmp op l' r' := by
  simp only [ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨l', hl, r', hr, rfl⟩ := h
  exact ⟨l', r', hl, hr, rfl⟩

theorem inv_exists {v : TypedBinder} {c : Condition}
    (h : ConditionKind.toFormula (.exists v c) = .ok φ) :
    ∃ x a, v.slot = .name x.name ∧ c.toFormula = .ok a ∧ φ = .exist x a := by
  simp only [ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨x, hx, a, ha, rfl⟩ := h
  exact ⟨x, a, (toSpec_binder hx).1, ha, rfl⟩

theorem inv_tp {v : BinderSlot} (h : ConditionKind.toFormula (.tp v) = .ok φ) :
    ∃ n, v = .name n ∧ φ = .tp n := by
  simp only [ConditionKind.toFormula, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨n, hn, rfl⟩ := h
  exact ⟨n, toSpec_name hn, rfl⟩

theorem inv_or {l r : Condition} : ConditionKind.toFormula (.or l r) ≠ .ok φ := throw_ne_ok
theorem inv_call {c : Call} : ConditionKind.toFormula (.call c) ≠ .ok φ := throw_ne_ok
theorem inv_sigil {s : Sigil} {n : String} : ConditionKind.toFormula (.sigilRef s n) ≠ .ok φ :=
  throw_ne_ok
theorem inv_refine {b : Condition} {fs : List NamedArg} {sp : Span} :
    ConditionKind.toFormula (.refine b fs sp) ≠ .ok φ := throw_ne_ok

theorem inv_args_cons {n : String} {t : Term} {rest : List NamedArg}
    {args' : List (Dogwood.Spec.Path × STerm)}
    (h : NamedArg.toSpecList (⟨n, t⟩ :: rest) = .ok args') :
    ∃ t' rest', t.toSpec = .ok t' ∧ NamedArg.toSpecList rest = .ok rest' ∧
      args' = (fieldPathSplit n, t') :: rest' := by
  simp only [NamedArg.toSpecList, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨t', ht, rest', hr, rfl⟩ := h
  exact ⟨t', rest', ht, hr, rfl⟩

theorem inv_args_nil {args' : List (Dogwood.Spec.Path × STerm)}
    (h : NamedArg.toSpecList [] = .ok args') : args' = [] := by
  simp only [NamedArg.toSpecList, pure_eq_ok] at h
  exact h.symm

theorem inv_arith {op : Dogwood.Spec.Temporal.ArithOp} {l r : Term}
    (h : Term.toSpec (.arith op l r) = .ok t') :
    ∃ l' r', l.toSpec = .ok l' ∧ r.toSpec = .ok r' ∧ t' = .arith op l' r' := by
  simp only [Term.toSpec, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨l', hl, r', hr, rfl⟩ := h
  exact ⟨l', r', hl, hr, rfl⟩

theorem inv_agg {sp : Span} {k : AggExprKind} (h : Term.toSpec (.agg ⟨sp, k⟩) = .ok t') :
    ∃ a, AggExprKind.toSpec k = .ok a ∧ t' = .agg a := by
  simp only [Term.toSpec, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a, ha, rfl⟩

theorem inv_count {vs : List TypedBinder} {b : Condition}
    (h : AggExprKind.toSpec (.count vs b) = .ok a') :
    ∃ dom body, vs.mapM TypedBinder.toSpec = .ok dom ∧ b.toFormula = .ok body ∧
      a' = .count dom body := by
  simp only [AggExprKind.toSpec, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨dom, hd, body, hb, rfl⟩ := h
  exact ⟨dom, body, hd, hb, rfl⟩

theorem inv_sum {s : BinderSlot} {vs : List TypedBinder} {b : Condition}
    (h : AggExprKind.toSpec (.sum s vs b) = .ok a') :
    ∃ n dom body, s = .name n ∧ vs.mapM TypedBinder.toSpec = .ok dom ∧
      b.toFormula = .ok body ∧ a' = .sum n dom body := by
  simp only [AggExprKind.toSpec, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨n, hn, dom, hd, body, hb, rfl⟩ := h
  exact ⟨n, dom, body, toSpec_name hn, hd, hb, rfl⟩

theorem inv_aggCall {c : Call} : AggExprKind.toSpec (.call c) ≠ .ok a' := throw_ne_ok

/-- Only a variable projects to a variable. -/
theorem toSpec_var {t : Term} {x : String} (h : t.toSpec = .ok (.var x)) : t = .var x := by
  cases t <;> simp [Term.toSpec, bind_eq_ok, pure_eq_ok, map_eq_ok, throw_ne_ok] at h
  case var => rw [h]
  case scopeField p =>
    unfold Term.toSpec at h
    split at h <;> simp_all [pure_eq_ok, throw_ne_ok]
  case agg a =>
    obtain ⟨sp, k⟩ := a
    simp [Term.toSpec, map_eq_ok] at h

end Inversion

/-! ## Free variables, restriction, sigils -/

mutual

theorem condFree_eq : (c : Condition) → {φ : SFormula} → c.toFormula = .ok φ → condFree c = φ.fv
  | ⟨_, k⟩, _, h => kindFree_eq k h

theorem kindFree_eq : (k : ConditionKind) → {φ : SFormula} → ConditionKind.toFormula k = .ok φ →
    kindFree k = φ.fv
  | .and l r, _, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := inv_and h
    simp only [kindFree, Formula.fv, condFree_eq l ha, condFree_eq r hb]
  | .or _ _, _, h => absurd h inv_or
  | .not c, _, h => by
    obtain ⟨a, ha, rfl⟩ := inv_not h
    simp only [kindFree, Formula.fv, condFree_eq c ha]
  | .formerly _ c, _, h => by
    obtain ⟨_, a, _, ha, rfl⟩ := inv_formerly h
    simp only [kindFree, Formula.fv, condFree_eq c ha]
  | .previous _ c, _, h => by
    obtain ⟨_, a, _, ha, rfl⟩ := inv_previous h
    simp only [kindFree, Formula.fv, condFree_eq c ha]
  | .since l _ r, _, h => by
    obtain ⟨a, _, b, ha, _, hb, rfl⟩ := inv_since h
    simp only [kindFree, Formula.fv, condFree_eq l ha, condFree_eq r hb]
  | .predicate ⟨_, _, _, _, args⟩, _, h => by
    obtain ⟨_, args', ha, rfl⟩ := inv_pred h
    simp only [kindFree, Formula.fv, argsFree_eq args ha]
  | .comparison _ l r, _, h => by
    obtain ⟨l', r', hl, hr, rfl⟩ := inv_cmp h
    simp only [kindFree, Formula.fv, termVars_eq l hl, termVars_eq r hr]
  | .exists v c, _, h => by
    obtain ⟨x, a, hv, ha, rfl⟩ := inv_exists h
    simp only [kindFree, Formula.fv, hv, condFree_eq c ha, without]
  | .tp v, _, h => by
    obtain ⟨n, rfl, rfl⟩ := inv_tp h
    rfl
  | .call _, _, h => absurd h inv_call
  | .sigilRef _ _, _, h => absurd h inv_sigil
  | .refine _ _ _, _, h => absurd h inv_refine

theorem argsFree_eq : (args : List NamedArg) → {args' : List (Dogwood.Spec.Path × STerm)} →
    NamedArg.toSpecList args = .ok args' → argsFree args = Formula.argsFv args'
  | [], _, h => by rw [inv_args_nil h]; rfl
  | ⟨_, t⟩ :: rest, _, h => by
    obtain ⟨t', rest', ht, hr, rfl⟩ := inv_args_cons h
    simp only [argsFree, Formula.argsFv, termVars_eq t ht, argsFree_eq rest hr]

theorem termVars_eq : (t : Term) → {t' : STerm} → t.toSpec = .ok t' → termVars t = t'.fv
  | .var _, _, h => by
    simp only [Term.toSpec, pure_eq_ok] at h
    subst h; rfl
  | .arith _ l r, _, h => by
    obtain ⟨l', r', hl, hr, rfl⟩ := inv_arith h
    simp only [termVars, Dogwood.Spec.Temporal.Term.fv, termVars_eq l hl, termVars_eq r hr]
  | .agg ⟨_, k⟩, _, h => by
    obtain ⟨a, ha, rfl⟩ := inv_agg h
    simp only [termVars, Dogwood.Spec.Temporal.Term.fv, aggVars_eq k ha]
  | .entity _ _, _, h => by
    simp only [Term.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, rfl⟩ := h; rfl
  | .integer _, _, h | .decimal _, _, h | .string _, _, h | .bool _, _, h
  | .contextField _, _, h | .wildcard, _, h => by
    simp only [Term.toSpec, pure_eq_ok] at h
    subst h; rfl
  | .scopeField p, _, h => by
    unfold Term.toSpec at h
    split at h <;> simp_all [pure_eq_ok, throw_ne_ok] <;> subst h <;> rfl
  | .array _, _, h => absurd h throw_ne_ok
  | .paramRef _, _, h => absurd h throw_ne_ok
  | .binderRef _, _, h => absurd h throw_ne_ok

theorem aggVars_eq : (k : AggExprKind) → {a : SAggregate} → AggExprKind.toSpec k = .ok a →
    aggVars k = a.fv
  | .count vs b, _, h => by
    obtain ⟨dom, body, hd, hb, rfl⟩ := inv_count h
    simp only [aggVars, withoutAll, Dogwood.Spec.Temporal.Aggregate.fv, toSpec_binders hd,
      condFree_eq b hb]
  | .sum _ vs b, _, h => by
    obtain ⟨_, dom, body, _, hd, hb, rfl⟩ := inv_sum h
    simp only [aggVars, withoutAll, Dogwood.Spec.Temporal.Aggregate.fv, toSpec_binders hd,
      condFree_eq b hb]
  | .call _, _, h => absurd h inv_aggCall

end

mutual

theorem termHasWildcard_eq : (t : Term) → {t' : STerm} → t.toSpec = .ok t' →
    termHasWildcard t = t'.hasWildcard
  | .arith _ l r, _, h => by
    obtain ⟨l', r', hl, hr, rfl⟩ := inv_arith h
    simp only [termHasWildcard, Dogwood.Spec.Temporal.Term.hasWildcard, termHasWildcard_eq l hl,
      termHasWildcard_eq r hr]
  | .wildcard, _, h => by
    simp only [Term.toSpec, pure_eq_ok] at h
    subst h; rfl
  | .array _, _, h => absurd h throw_ne_ok
  | .var _, _, h | .integer _, _, h | .decimal _, _, h | .string _, _, h | .bool _, _, h
  | .contextField _, _, h => by
    simp only [Term.toSpec, pure_eq_ok] at h
    subst h; rfl
  | .entity _ _, _, h => by
    simp only [Term.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, rfl⟩ := h; rfl
  | .scopeField p, _, h => by
    unfold Term.toSpec at h
    split at h <;> simp_all [pure_eq_ok, throw_ne_ok] <;> subst h <;> rfl
  | .agg ⟨_, k⟩, _, h => by
    obtain ⟨a, _, rfl⟩ := inv_agg h
    rfl
  | .paramRef _, _, h => absurd h throw_ne_ok
  | .binderRef _, _, h => absurd h throw_ne_ok

end

/-- The variable a term is, if it is one. -/
def varOf : Term → Option String
  | .var x => some x
  | _ => none

def varOfS : STerm → Option String
  | .var x => some x
  | _ => none

theorem eqRestrictedVar_nf (l r : Term) : eqRestrictedVar l r =
    match varOf l, varOf r with
    | some _, some _ => none
    | some n, none => if isRestrictor r then some n else none
    | none, some n => if isRestrictor l then some n else none
    | none, none => none := by
  cases l <;> cases r <;> rfl

theorem eqRestricted_nf (l r : STerm) : Dogwood.Spec.Temporal.eqRestricted? l r =
    match varOfS l, varOfS r with
    | some _, some _ => none
    | some n, none => if r.hasWildcard then none else some n
    | none, some n => if l.hasWildcard then none else some n
    | none, none => none := by
  cases l <;> cases r <;> rfl

theorem varOf_eq {t : Term} {t' : STerm} (h : t.toSpec = .ok t') : varOf t = varOfS t' := by
  cases ht' : varOfS t' with
  | some x =>
    cases t' <;> simp only [varOfS, reduceCtorEq, Option.some.injEq] at ht'
    subst ht'
    rw [toSpec_var h]; rfl
  | none =>
    cases ht : varOf t with
    | none => rfl
    | some x =>
      cases t <;> simp only [varOf, reduceCtorEq, Option.some.injEq] at ht
      subst ht
      simp only [Term.toSpec, pure_eq_ok] at h
      subst h
      simp [varOfS] at ht'

theorem isRestrictor_eq {t : Term} {t' : STerm} (h : t.toSpec = .ok t') (hv : varOf t = none) :
    isRestrictor t = !t'.hasWildcard := by
  rw [← termHasWildcard_eq t h]
  cases t with
  | var _ => simp [varOf] at hv
  | array _ => exact absurd h throw_ne_ok
  | wildcard => rfl
  | arith _ _ _ => rfl
  | _ => rfl

/-- The crate's binding equality is the specification's. -/
theorem eqRestrictedVar_eq {l r : Term} {l' r' : STerm} (hl : l.toSpec = .ok l')
    (hr : r.toSpec = .ok r') : eqRestrictedVar l r = Dogwood.Spec.Temporal.eqRestricted? l' r' := by
  rw [eqRestrictedVar_nf, eqRestricted_nf, ← varOf_eq hl, ← varOf_eq hr]
  cases hvl : varOf l <;> cases hvr : varOf r <;> simp only
  · rw [isRestrictor_eq hl hvl]; cases l'.hasWildcard <;> rfl
  · rw [isRestrictor_eq hr hvr]; cases r'.hasWildcard <;> rfl

/-- The crate's value side is the specification's. -/
theorem valueSide_toSpec {x : String} {l r : Term} {l' r' : STerm} (hl : l.toSpec = .ok l')
    (hr : r.toSpec = .ok r') :
    (valueSide x l r).toSpec = .ok (Dogwood.Spec.Temporal.valueSide x l' r') := by
  have hv := varOf_eq hl
  cases l with
  | var n =>
    simp only [Term.toSpec, pure_eq_ok] at hl
    subst hl
    simp only [valueSide, Dogwood.Spec.Temporal.valueSide, beq_iff_eq]
    split <;> first | assumption | rfl
  | _ =>
    cases l' <;> simp_all [varOf, varOfS, valueSide, Dogwood.Spec.Temporal.valueSide]

theorem argVarNames_eq : {args : List NamedArg} → {args' : List (Dogwood.Spec.Path × STerm)} →
    NamedArg.toSpecList args = .ok args' → argVarNames args = Dogwood.Spec.Temporal.predVars args'
  | [], _, h => by rw [inv_args_nil h]; rfl
  | ⟨n, t⟩ :: rest, _, h => by
    obtain ⟨t', rest', ht, hr, rfl⟩ := inv_args_cons h
    have hv := varOf_eq ht
    have ih := argVarNames_eq hr
    cases t' <;> cases t <;> simp_all [varOf, varOfS, argVarNames, Dogwood.Spec.Temporal.predVars]

mutual

theorem condRR_eq : (c : Condition) → {φ : SFormula} → c.toFormula = .ok φ → condRR c = rr φ
  | ⟨_, k⟩, _, h => kindRR_eq k h

theorem kindRR_eq : (k : ConditionKind) → {φ : SFormula} → ConditionKind.toFormula k = .ok φ →
    kindRR k = rr φ
  | .and l r, _, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := inv_and h
    simp only [kindRR, rr, condRR_eq l ha, condRR_eq r hb]
  | .or _ _, _, h => absurd h inv_or
  | .not c, _, h => by
    obtain ⟨a, ha, rfl⟩ := inv_not h
    rfl
  | .formerly _ c, _, h => by
    obtain ⟨_, a, _, ha, rfl⟩ := inv_formerly h
    simp only [kindRR, rr, condRR_eq c ha]
  | .previous _ c, _, h => by
    obtain ⟨_, a, _, ha, rfl⟩ := inv_previous h
    simp only [kindRR, rr, condRR_eq c ha]
  | .since _ _ r, _, h => by
    obtain ⟨_, _, b, _, _, hb, rfl⟩ := inv_since h
    simp only [kindRR, rr, condRR_eq r hb]
  | .predicate ⟨_, _, _, _, args⟩, _, h => by
    obtain ⟨_, args', ha, rfl⟩ := inv_pred h
    simp only [kindRR, rr, argVarNames_eq ha]
  | .comparison op l r, _, h => by
    obtain ⟨l', r', hl, hr, rfl⟩ := inv_cmp h
    cases op <;> simp only [kindRR, rr, eqRestrictedVar_eq hl hr]
  | .exists v c, _, h => by
    obtain ⟨x, a, hv, ha, rfl⟩ := inv_exists h
    simp only [kindRR, rr, hv, condRR_eq c ha, without]
  | .tp v, _, h => by
    obtain ⟨n, rfl, rfl⟩ := inv_tp h
    rfl
  | .call _, _, h => absurd h inv_call
  | .sigilRef _ _, _, h => absurd h inv_sigil
  | .refine _ _ _, _, h => absurd h inv_refine

end

mutual

theorem condHasSigil_eq : (c : Condition) → {φ : SFormula} → c.toFormula = .ok φ →
    condHasSigil c = false
  | ⟨_, k⟩, _, h => kindHasSigil_eq k h

theorem kindHasSigil_eq : (k : ConditionKind) → {φ : SFormula} → ConditionKind.toFormula k = .ok φ →
    kindHasSigil k = false
  | .and l r, _, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := inv_and h
    simp only [kindHasSigil, condHasSigil_eq l ha, condHasSigil_eq r hb, Bool.or_false]
  | .or _ _, _, h => absurd h inv_or
  | .not c, _, h => by
    obtain ⟨a, ha, rfl⟩ := inv_not h
    simp only [kindHasSigil, condHasSigil_eq c ha]
  | .formerly _ c, _, h => by
    obtain ⟨_, a, _, ha, rfl⟩ := inv_formerly h
    simp only [kindHasSigil, condHasSigil_eq c ha]
  | .previous _ c, _, h => by
    obtain ⟨_, a, _, ha, rfl⟩ := inv_previous h
    simp only [kindHasSigil, condHasSigil_eq c ha]
  | .since l _ r, _, h => by
    obtain ⟨a, _, b, ha, _, hb, rfl⟩ := inv_since h
    simp only [kindHasSigil, condHasSigil_eq l ha, condHasSigil_eq r hb, Bool.or_false]
  | .predicate ⟨_, _, _, _, args⟩, _, h => by
    obtain ⟨_, args', ha, rfl⟩ := inv_pred h
    simp only [kindHasSigil, argsHaveSigil_eq args ha]
  | .comparison _ l r, _, h => by
    obtain ⟨l', r', hl, hr, rfl⟩ := inv_cmp h
    simp only [kindHasSigil, termHasSigil_eq l hl, termHasSigil_eq r hr, Bool.or_false]
  | .exists _ c, _, h => by
    obtain ⟨x, a, _, ha, rfl⟩ := inv_exists h
    simp only [kindHasSigil, condHasSigil_eq c ha]
  | .tp v, _, h => by
    obtain ⟨n, rfl, rfl⟩ := inv_tp h
    rfl
  | .call _, _, h => absurd h inv_call
  | .sigilRef _ _, _, h => absurd h inv_sigil
  | .refine _ _ _, _, h => absurd h inv_refine

theorem argsHaveSigil_eq : (args : List NamedArg) → {args' : List (Dogwood.Spec.Path × STerm)} →
    NamedArg.toSpecList args = .ok args' → argsHaveSigil args = false
  | [], _, _ => rfl
  | ⟨_, t⟩ :: rest, _, h => by
    obtain ⟨t', rest', ht, hr, rfl⟩ := inv_args_cons h
    simp only [argsHaveSigil, termHasSigil_eq t ht, argsHaveSigil_eq rest hr, Bool.or_false]

theorem termHasSigil_eq : (t : Term) → {t' : STerm} → t.toSpec = .ok t' → termHasSigil t = false
  | .arith _ l r, _, h => by
    obtain ⟨l', r', hl, hr, rfl⟩ := inv_arith h
    simp only [termHasSigil, termHasSigil_eq l hl, termHasSigil_eq r hr, Bool.or_false]
  | .agg ⟨_, k⟩, _, h => by
    obtain ⟨a, ha, rfl⟩ := inv_agg h
    simp only [termHasSigil, aggHasSigil_eq k ha]
  | .array _, _, h => absurd h throw_ne_ok
  | .paramRef _, _, h => absurd h throw_ne_ok
  | .binderRef _, _, h => absurd h throw_ne_ok
  | .var _, _, _ | .integer _, _, _ | .decimal _, _, _ | .string _, _, _ | .bool _, _, _
  | .contextField _, _, _ | .entity _ _, _, _ | .scopeField _, _, _ | .wildcard, _, _ => rfl

theorem aggHasSigil_eq : (k : AggExprKind) → {a : SAggregate} → AggExprKind.toSpec k = .ok a →
    aggHasSigil k = false
  | .count _ b, _, h => by
    obtain ⟨_, _, _, hb, rfl⟩ := inv_count h
    simp only [aggHasSigil, condHasSigil_eq b hb]
  | .sum _ _ b, _, h => by
    obtain ⟨_, _, _, _, _, hb, rfl⟩ := inv_sum h
    simp only [aggHasSigil, condHasSigil_eq b hb]
  | .call _, _, h => absurd h inv_aggCall

end

end Dogwood.Thm.Frontend.Macros
