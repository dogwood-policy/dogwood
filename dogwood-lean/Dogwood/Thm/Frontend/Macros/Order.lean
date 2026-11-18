import Dogwood.Thm.Restriction
import Dogwood.Thm.Monitorable
import Dogwood.Thm.SafetyDecide
import Dogwood.Frontend.Macros.Check

/-!
# Safety read left to right

The crate's static checks (`Dogwood.Frontend.Macros.checkLeaf`) decide a variant of the
specification's safety (`Formula.Safe`) in which each `&&` chain is read left to right: a
conjunct may read only the variables restricted outside the chain or by the conjuncts before it,
where `Formula.Safe` lets it read every variable of the chain's closure. This module defines the
variant, `SafeLR`, and the crate's checks restated on the specification's formulas:

* `rr φ`: the variables the crate takes `φ` to restrict (`collect_range_restricted`), whatever
  the restricting atoms read;
* `ChainF ρ φ`, with `ConjF`, `DescF`, `DescTerm`: the crate's evaluation-order check
  (`check_chain`, `check_conjunct_demands`, `descend_nested_chains`) from the seed `ρ`;
* `FactsF φ`: what the crate's scoping pass (`check_condition`) asks of restriction: every
  `exists` variable and every `for` variable in the `rr` of its body;
* `WF φ`: what the scoping pass asks besides: no binder or `tp` variable named after a Cedar
  request variable, every summand one of its `for` variables, and no aggregate or arithmetic as
  a predicate argument.

The results:

* `safeLR_safe`: `SafeLR R φ` implies `φ.Safe R`;
* `chainF_factsF_iff`: `ChainF ρ φ ∧ FactsF φ` is `SafeLR (· ∈ ρ) φ`.

`SafeLR` is strictly stronger than `Safe`, and not only because of the order of the conjuncts:
see `Dogwood.Thm.Frontend.Macros.Examples` for a condition that is safe and that `SafeLR` rejects
in every order of its conjuncts.
-/

namespace Dogwood.Thm.Frontend.Macros

open Dogwood.Spec Dogwood.Spec.Temporal
open Dogwood.Thm (pred_ext eqRestricted_cases valueSide_of_eq eqRestricted_mem_fv mem_predVars)

/-! ## Safety, each chain read left to right -/

mutual

/-- `SafeLR R φ`: `Formula.Safe R φ`, except that in `φ && ψ`, `φ` is checked with the variables
restricted outside the chain and `ψ` with those and the ones `φ` restricts, instead of both
with the chain's closure. -/
def SafeLR (R : VarName → Prop) : Formula → Prop
  | .and φ ψ => SafeLR R φ ∧ SafeLR (φ.Restricted R) ψ
  | .not φ => (∀ y ∈ φ.fv, R y) ∧ SafeLR R φ
  | .formerly _ φ => SafeLR R φ
  | .previous _ φ => SafeLR R φ
  | .since φ _ ψ => SafeLR R ψ ∧ (∀ y ∈ φ.fv, ψ.Restricted R y) ∧ SafeLR (ψ.Restricted R) φ
  | .pred _ _ _ => True
  | .tp _ => True
  | .cmp op l r =>
    (∀ y ∈ l.fv ++ r.fv, (Formula.cmp op l r).Restricted R y) ∧ TermSafeLR R l ∧ TermSafeLR R r
  | .exist x φ =>
    φ.Restricts (fun z => z ≠ x.name ∧ R z) x.name ∧ SafeLR (fun z => z ≠ x.name ∧ R z) φ

def TermSafeLR (R : VarName → Prop) : Term → Prop
  | .agg a => AggSafeLR R a
  | .arith _ l r => TermSafeLR R l ∧ TermSafeLR R r
  | _ => True

def AggSafeLR (R : VarName → Prop) : Aggregate → Prop
  | .count dom body | .sum _ dom body =>
    (∀ b ∈ dom, body.Restricts (fun z => z ∉ dom.map (·.name) ∧ R z) b.name) ∧
      SafeLR (fun z => z ∉ dom.map (·.name) ∧ R z) body

end

mutual

/-- Reading each chain left to right is safe. -/
theorem safeLR_safe : (φ : Formula) → {R : VarName → Prop} → SafeLR R φ → φ.Safe R
  | .and φ ψ, R, ⟨h₁, h₂⟩ => by
    have hC : ∀ z, R z → (Formula.and φ ψ).Restricts R z := fun _ hz =>
      Dogwood.Thm.Formula.restricts_and_base hz
    have hC' : ∀ z, φ.Restricted R z → (Formula.and φ ψ).Restricts R z := by
      intro z hz
      rcases hz with hz | hz
      · exact hC z hz
      · exact Dogwood.Thm.Formula.restricts_and_closed_left
          (Dogwood.Thm.Formula.restricts_mono φ hC hz)
    exact ⟨Dogwood.Thm.Formula.safe_mono φ hC (safeLR_safe φ h₁),
      Dogwood.Thm.Formula.safe_mono ψ hC' (safeLR_safe ψ h₂)⟩
  | .not φ, _, ⟨h₁, h₂⟩ => ⟨h₁, safeLR_safe φ h₂⟩
  | .formerly _ φ, _, h => safeLR_safe φ h
  | .previous _ φ, _, h => safeLR_safe φ h
  | .since φ _ ψ, _, ⟨h₁, h₂, h₃⟩ => ⟨safeLR_safe ψ h₁, h₂, safeLR_safe φ h₃⟩
  | .pred _ _ _, _, _ => trivial
  | .tp _, _, _ => trivial
  | .cmp _ l r, _, ⟨h₁, h₂, h₃⟩ => ⟨h₁, termSafeLR_safe l h₂, termSafeLR_safe r h₃⟩
  | .exist _ φ, _, ⟨h₁, h₂⟩ => ⟨h₁, safeLR_safe φ h₂⟩

theorem termSafeLR_safe : (t : Term) → {R : VarName → Prop} → TermSafeLR R t → t.Safe R
  | .agg a, _, h => aggSafeLR_safe a h
  | .arith _ l r, _, ⟨h₁, h₂⟩ => ⟨termSafeLR_safe l h₁, termSafeLR_safe r h₂⟩
  | .entity _, _, _ | .long _, _, _ | .decimal _, _, _ | .string _, _, _ | .bool _, _, _
  | .context _, _, _ | .scope _ _, _, _ | .var _, _, _ | .wildcard, _, _ => trivial

theorem aggSafeLR_safe : (a : Aggregate) → {R : VarName → Prop} → AggSafeLR R a → a.Safe R
  | .count _ body, _, ⟨h₁, h₂⟩ | .sum _ _ body, _, ⟨h₁, h₂⟩ => ⟨h₁, safeLR_safe body h₂⟩

end

/-- A leaf whose chains, read left to right, are safe is safe. -/
theorem safeLR_isSafe {φ : Formula} (h : SafeLR (fun _ => False) φ) : φ.IsSafe :=
  safeLR_safe φ h

/-! ## The crate's checks on formulas -/

/-- The variables the crate takes a condition to restrict (crate `collect_range_restricted`): a
binding equality restricts its variable whatever its value side reads. -/
def rr : Formula → List VarName
  | .and φ ψ => rr φ ++ rr ψ
  | .not _ => []
  | .pred _ _ args => predVars args
  | .tp x => [x]
  | .cmp op l r => match op with
    | .eq => (eqRestricted? l r).toList
    | _ => []
  | .formerly _ φ => rr φ
  | .previous _ φ => rr φ
  | .since _ _ ψ => rr ψ
  | .exist x φ => (rr φ).filter (· != x.name)

/-- A seed without the variables of a `for` list. -/
def withoutDom (ρ : List VarName) (dom : List Binder) : List VarName :=
  ρ.filter fun z => !(dom.map (·.name)).contains z

/-- The demands of a comparison conjunct (crate `check_conjunct_demands`): the value side's
variables for a binding equality, all of its variables for a filter. -/
def CmpDemands (ρ : List VarName) (op : CmpOp) (l r : Term) : Prop :=
  match op, eqRestricted? l r with
  | .eq, some x => ∀ y ∈ (valueSide x l r).fv, y ∈ ρ
  | _, _ => ∀ y ∈ l.fv ++ r.fv, y ∈ ρ

mutual

/-- One `&&` chain read left to right from the seed `ρ` (crate `check_chain`): each conjunct's
demands (`ConjF`), then the chains nested in it (`DescF`). -/
def ChainF (ρ : List VarName) : Formula → Prop
  | .and φ ψ => ChainF ρ φ ∧ ChainF (ρ ++ rr φ) ψ
  | .not φ => (∀ y ∈ φ.fv, y ∈ ρ) ∧ DescF ρ φ
  | .formerly _ φ => ConjF ρ φ ∧ ChainF ρ φ
  | .previous _ φ => ConjF ρ φ ∧ ChainF ρ φ
  | .since φ _ ψ => (∀ y ∈ φ.fv, y ∈ rr ψ ∨ y ∈ ρ) ∧ (ChainF (ρ ++ rr ψ) φ ∧ ChainF ρ ψ)
  | .exist x φ =>
    ConjF (ρ.filter (· != x.name)) φ ∧ ChainF (ρ.filter (· != x.name)) φ
  | .cmp op l r => CmpDemands ρ op l r ∧ (DescTerm ρ l ∧ DescTerm ρ r)
  | .pred _ _ _ => True ∧ True
  | .tp _ => True ∧ True

/-- The demands of one conjunct (crate `check_conjunct_demands`). -/
def ConjF (ρ : List VarName) : Formula → Prop
  | .cmp op l r => CmpDemands ρ op l r
  | .not φ => ∀ y ∈ φ.fv, y ∈ ρ
  | .since φ _ ψ => ∀ y ∈ φ.fv, y ∈ rr ψ ∨ y ∈ ρ
  | .formerly _ φ => ConjF ρ φ
  | .previous _ φ => ConjF ρ φ
  | .exist x φ => ConjF (ρ.filter (· != x.name)) φ
  | .and _ _ => True
  | .pred _ _ _ => True
  | .tp _ => True

/-- The chains nested in one conjunct (crate `descend_nested_chains`). -/
def DescF (ρ : List VarName) : Formula → Prop
  | .and φ ψ => ChainF ρ φ ∧ ChainF (ρ ++ rr φ) ψ
  | .not φ => DescF ρ φ
  | .formerly _ φ => ChainF ρ φ
  | .previous _ φ => ChainF ρ φ
  | .since φ _ ψ => ChainF (ρ ++ rr ψ) φ ∧ ChainF ρ ψ
  | .exist x φ => ChainF (ρ.filter (· != x.name)) φ
  | .cmp _ l r => DescTerm ρ l ∧ DescTerm ρ r
  | .pred _ _ _ => True
  | .tp _ => True

/-- The chains of the aggregates of a comparison operand. -/
def DescTerm (ρ : List VarName) : Term → Prop
  | .agg (.count dom b) => ChainF (withoutDom ρ dom) b
  | .agg (.sum _ dom b) => ChainF (withoutDom ρ dom) b
  | .arith _ l r => DescTerm ρ l ∧ DescTerm ρ r
  | _ => True

end

mutual

/-- The restriction facts the crate's scoping pass checks (crate `check_exists_safe`,
`check_aggregation`). -/
def FactsF : Formula → Prop
  | .and φ ψ => FactsF φ ∧ FactsF ψ
  | .not φ => FactsF φ
  | .formerly _ φ => FactsF φ
  | .previous _ φ => FactsF φ
  | .since φ _ ψ => FactsF φ ∧ FactsF ψ
  | .exist x φ => x.name ∈ rr φ ∧ FactsF φ
  | .cmp _ l r => TermFacts l ∧ TermFacts r
  | .pred _ _ _ => True
  | .tp _ => True

def TermFacts : Term → Prop
  | .agg (.count dom b) => (∀ v ∈ dom, v.name ∈ rr b) ∧ FactsF b
  | .agg (.sum _ dom b) => (∀ v ∈ dom, v.name ∈ rr b) ∧ FactsF b
  | .arith _ l r => TermFacts l ∧ TermFacts r
  | _ => True

end

/-- A term that may be a predicate argument: neither an aggregate nor arithmetic. -/
def IsPlain : Term → Prop
  | .agg _ => False
  | .arith _ _ _ => False
  | _ => True

/-- The binders no condition may name (crate `RESERVED_BINDER_NAMES`). -/
abbrev reserved : List VarName := Dogwood.Frontend.Macros.reservedBinderNames

mutual

/-- What the crate's scoping pass checks besides restriction: no binder or `tp` variable named
after a Cedar request variable, every summand one of its `for` variables, and only plain
predicate arguments. -/
def WF : Formula → Prop
  | .and φ ψ => WF φ ∧ WF ψ
  | .not φ => WF φ
  | .formerly _ φ => WF φ
  | .previous _ φ => WF φ
  | .since φ _ ψ => WF φ ∧ WF ψ
  | .exist x φ => x.name ∉ reserved ∧ WF φ
  | .cmp _ l r => TermWF l ∧ TermWF r
  | .pred _ _ args => ∀ a ∈ args, IsPlain a.2
  | .tp x => x ∉ reserved

def TermWF : Term → Prop
  | .agg (.count dom b) => (∀ v ∈ dom, v.name ∉ reserved) ∧ WF b
  | .agg (.sum s dom b) => (∀ v ∈ dom, v.name ∉ reserved) ∧ s ∈ dom.map (·.name) ∧ WF b
  | .arith _ l r => TermWF l ∧ TermWF r
  | _ => True

end

/-! ## What `rr` is -/

/-- Given its demands, the crate's restriction is the specification's: every variable of `rr φ`
is restricted by `φ`, or outside it. -/
theorem rr_sound : (φ : Formula) → {ρ : List VarName} → ChainF ρ φ →
    ∀ v ∈ rr φ, v ∈ ρ ∨ φ.Restricts (· ∈ ρ) v
  | .pred _ _ args, _, _, v, hv => .inr (mem_predVars.mp hv)
  | .tp _, _, _, v, hv => by
    simp only [rr, List.mem_singleton] at hv
    exact .inr hv
  | .cmp op l r, ρ, ⟨hd, _⟩, v, hv => by
    cases op <;> simp only [rr, List.not_mem_nil] at hv
    simp only [Option.mem_toList] at hv
    simp only [CmpDemands, hv] at hd
    exact .inr ⟨hv, hd⟩
  | .not _, _, _, _, hv => by simp [rr] at hv
  | .formerly _ φ, _, ⟨_, h⟩, v, hv => rr_sound φ h v hv
  | .previous _ φ, _, ⟨_, h⟩, v, hv => rr_sound φ h v hv
  | .since _ _ ψ, _, ⟨_, _, h⟩, v, hv => rr_sound ψ h v hv
  | .exist x φ, ρ, ⟨_, h⟩, v, hv => by
    simp only [rr, List.mem_filter, bne_iff_ne, ne_eq] at hv
    rcases rr_sound φ h v hv.1 with h' | h'
    · simp only [List.mem_filter] at h'
      exact .inl h'.1
    · refine .inr ⟨hv.2, Dogwood.Thm.Formula.restricts_mono φ ?_ h'⟩
      intro z hz
      simp only [List.mem_filter, bne_iff_ne, ne_eq] at hz
      exact ⟨hz.2, hz.1⟩
  | .and φ ψ, ρ, ⟨h₁, h₂⟩, v, hv => by
    have hl : ∀ v ∈ rr φ, (Formula.and φ ψ).Restricts (· ∈ ρ) v := by
      intro v hv
      rcases rr_sound φ h₁ v hv with h | h
      · exact Dogwood.Thm.Formula.restricts_and_base h
      · exact Dogwood.Thm.Formula.restricts_and_closed_left
          (Dogwood.Thm.Formula.restricts_mono φ
            (fun _ hz => Dogwood.Thm.Formula.restricts_and_base hz) h)
    refine .inr ?_
    simp only [rr, List.mem_append] at hv
    rcases hv with hv | hv
    · exact hl v hv
    · rcases rr_sound ψ h₂ v hv with h | h
      · simp only [List.mem_append] at h
        rcases h with h | h
        · exact Dogwood.Thm.Formula.restricts_and_base h
        · exact hl v h
      · refine Dogwood.Thm.Formula.restricts_and_closed_right
          (Dogwood.Thm.Formula.restricts_mono ψ ?_ h)
        intro z hz
        simp only [List.mem_append] at hz
        rcases hz with hz | hz
        · exact Dogwood.Thm.Formula.restricts_and_base hz
        · exact hl z hz

/-- What `φ` restricts is in `rr φ`, or restricted outside it. -/
theorem rr_complete : (φ : Formula) → {R : VarName → Prop} → ∀ {v}, φ.Restricts R v →
    R v ∨ v ∈ rr φ
  | .pred _ _ args, _, _, h => .inr (mem_predVars.mpr h)
  | .tp _, _, _, h => .inr (by simp only [Formula.Restricts] at h; simp [rr, h])
  | .cmp op l r, _, _, h => by
    cases op <;> simp only [Formula.Restricts] at h
    exact .inr (by simp [rr, h.1])
  | .not _, _, _, h => h.elim
  | .formerly _ φ, _, _, h => rr_complete φ h
  | .previous _ φ, _, _, h => rr_complete φ h
  | .since _ _ ψ, _, _, h => rr_complete ψ h
  | .exist x φ, _, v, ⟨hne, h⟩ => by
    rcases rr_complete φ h with h | h
    · exact .inl h.2
    · exact .inr (by simp [rr, h, hne])
  | .and φ ψ, R, v, h => by
    refine h (fun z => R z ∨ z ∈ rr (.and φ ψ)) (fun z hz => .inl hz) ?_ ?_
    · intro z hz
      rcases rr_complete φ hz with h | h
      · exact h
      · exact .inr (by simp [rr, h])
    · intro z hz
      rcases rr_complete ψ hz with h | h
      · exact h
      · exact .inr (by simp [rr, h])

/-- Given its demands, `rr` is exactly what a condition restricts, besides the seed. -/
theorem restricted_iff {φ : Formula} {ρ : List VarName} (h : ChainF ρ φ) (z : VarName) :
    z ∈ ρ ++ rr φ ↔ φ.Restricted (· ∈ ρ) z := by
  constructor
  · intro hz
    simp only [List.mem_append] at hz
    rcases hz with hz | hz
    · exact .inl hz
    · exact rr_sound φ h z hz
  · intro hz
    rcases hz with hz | hz
    · exact List.mem_append_left _ hz
    · rcases rr_complete φ hz with hz | hz
      · exact List.mem_append_left _ hz
      · exact List.mem_append_right _ hz

theorem restricted_eq {φ : Formula} {ρ : List VarName} (h : ChainF ρ φ) :
    φ.Restricted (· ∈ ρ) = (· ∈ ρ ++ rr φ) :=
  pred_ext fun z => (restricted_iff h z).symm

theorem filter_ne_eq (ρ : List VarName) (x : VarName) :
    (fun z => z ≠ x ∧ z ∈ ρ) = (· ∈ ρ.filter (· != x)) :=
  pred_ext fun z => by simp [List.mem_filter, and_comm]

theorem withoutDom_eq (ρ : List VarName) (dom : List Binder) :
    (fun z => z ∉ dom.map (·.name) ∧ z ∈ ρ) = (· ∈ withoutDom ρ dom) :=
  pred_ext fun z => by simp [withoutDom, List.mem_filter, and_comm]

/-! ## The parts of a chain -/

theorem chainF_conj : (φ : Formula) → {ρ : List VarName} → ChainF ρ φ → ConjF ρ φ
  | .and _ _, _, _ => trivial
  | .not _, _, h => h.1
  | .formerly _ _, _, h => h.1
  | .previous _ _, _, h => h.1
  | .since _ _ _, _, h => h.1
  | .exist _ _, _, h => h.1
  | .cmp _ _ _, _, h => h.1
  | .pred _ _ _, _, _ => trivial
  | .tp _, _, _ => trivial

theorem chainF_desc : (φ : Formula) → {ρ : List VarName} → ChainF ρ φ → DescF ρ φ
  | .and _ _, _, h => h
  | .not _, _, h => h.2
  | .formerly _ _, _, h => h.2
  | .previous _ _, _, h => h.2
  | .since _ _ _, _, h => h.2
  | .exist _ _, _, h => h.2
  | .cmp _ _ _, _, h => h.2
  | .pred _ _ _, _, _ => trivial
  | .tp _, _, _ => trivial

theorem cmpDemands_of_fv {ρ : List VarName} {op : CmpOp} {l r : Term}
    (h : ∀ y ∈ l.fv ++ r.fv, y ∈ ρ) : CmpDemands ρ op l r := by
  unfold CmpDemands
  split
  · rename_i x hx
    intro y hy
    apply h
    rcases valueSide_of_eq hx with ⟨_, he⟩ | ⟨_, he⟩ <;> rw [he] at hy <;> simp [hy]
  · exact h

/-- Under a negation, the crate checks the free variables and the nested chains, not the
demands: those follow. -/
theorem chainF_of_desc : (φ : Formula) → {ρ : List VarName} → (∀ y ∈ φ.fv, y ∈ ρ) →
    DescF ρ φ → ChainF ρ φ
  | .and _ _, _, _, h => h
  | .not _, _, hfv, h => ⟨by simpa [Formula.fv] using hfv, h⟩
  | .formerly _ φ, _, _, h => ⟨chainF_conj φ h, h⟩
  | .previous _ φ, _, _, h => ⟨chainF_conj φ h, h⟩
  | .since _ _ _, _, hfv, h =>
    ⟨fun y hy => .inr (hfv y (by simp [Formula.fv, hy])), h⟩
  | .exist _ φ, _, _, h => ⟨chainF_conj φ h, h⟩
  | .cmp _ _ _, _, hfv, h => ⟨cmpDemands_of_fv (by simpa [Formula.fv] using hfv), h⟩
  | .pred _ _ _, _, _, _ => ⟨trivial, trivial⟩
  | .tp _, _, _, _ => ⟨trivial, trivial⟩

/-! ## The crate's checks decide `SafeLR` -/

/-- The value side of a binding equality on `x` reads every variable of the equality but `x`. -/
theorem mem_valueSide {l r : Term} {x y : VarName} (hx : eqRestricted? l r = some x)
    (hy : y ∈ l.fv ++ r.fv) : y = x ∨ y ∈ (valueSide x l r).fv := by
  rcases valueSide_of_eq hx with ⟨rfl, he⟩ | ⟨rfl, he⟩ <;> rw [he]
  · simpa only [Term.fv, List.mem_append, List.mem_singleton] using hy
  · simp only [Term.fv, List.mem_append, List.mem_singleton] at hy
    exact hy.symm

/-- The value side reads only variables of the equality. -/
theorem valueSide_sub {l r : Term} {x y : VarName} (hx : eqRestricted? l r = some x)
    (hy : y ∈ (valueSide x l r).fv) : y ∈ l.fv ++ r.fv := by
  rcases valueSide_of_eq hx with ⟨_, he⟩ | ⟨_, he⟩ <;> rw [he] at hy <;> simp [hy]

/-- The crate's demands of a comparison are the specification's: every variable it reads is
restricted, outside or by the comparison itself. -/
theorem cmpDemands_iff {ρ : List VarName} {op : CmpOp} {l r : Term} :
    CmpDemands ρ op l r ↔ ∀ y ∈ l.fv ++ r.fv, (Formula.cmp op l r).Restricted (· ∈ ρ) y := by
  cases op <;> cases hx : eqRestricted? l r <;>
    simp only [CmpDemands, hx, Formula.Restricted, Formula.Restricts, reduceCtorEq, false_and,
      or_false]
  rename_i x
  constructor
  · intro hd y hy
    rcases mem_valueSide hx hy with rfl | h
    · exact .inr ⟨rfl, hd⟩
    · exact .inl (hd y h)
  · intro h y hy
    rcases h y (valueSide_sub hx hy) with h | ⟨he, h⟩
    · exact h
    · simp only [Option.some.injEq] at he
      subst he
      exact h _ hy

theorem not_mem_withoutDom {ρ : List VarName} {dom : List Binder} {v : Binder} (hv : v ∈ dom) :
    v.name ∉ withoutDom ρ dom := by
  intro h
  have hm : v.name ∈ dom.map (·.name) := List.mem_map_of_mem (f := (·.name)) hv
  simp only [withoutDom, List.mem_filter] at h
  simp [hm] at h

mutual

theorem safeLR_of_chainF : (φ : Formula) → {ρ : List VarName} → ChainF ρ φ → FactsF φ →
    SafeLR (· ∈ ρ) φ
  | .and φ ψ, ρ, ⟨h₁, h₂⟩, ⟨f₁, f₂⟩ => by
    refine ⟨safeLR_of_chainF φ h₁ f₁, ?_⟩
    rw [restricted_eq h₁]
    exact safeLR_of_chainF ψ h₂ f₂
  | .not φ, _, ⟨hfv, hd⟩, f => ⟨hfv, safeLR_of_chainF φ (chainF_of_desc φ hfv hd) f⟩
  | .formerly _ φ, _, ⟨_, h⟩, f => safeLR_of_chainF φ h f
  | .previous _ φ, _, ⟨_, h⟩, f => safeLR_of_chainF φ h f
  | .since φ _ ψ, ρ, ⟨hfv, h₁, h₂⟩, ⟨f₁, f₂⟩ => by
    refine ⟨safeLR_of_chainF ψ h₂ f₂, ?_, ?_⟩
    · intro y hy
      rw [← restricted_iff h₂]
      rcases hfv y hy with h | h
      · exact List.mem_append_right _ h
      · exact List.mem_append_left _ h
    · rw [restricted_eq h₂]
      exact safeLR_of_chainF φ h₁ f₁
  | .pred _ _ _, _, _, _ => trivial
  | .tp _, _, _, _ => trivial
  | .cmp _ l r, _, ⟨hd, h₁, h₂⟩, ⟨f₁, f₂⟩ =>
    ⟨cmpDemands_iff.mp hd, termSafeLR_of_desc l h₁ f₁, termSafeLR_of_desc r h₂ f₂⟩
  | .exist x φ, ρ, ⟨_, h⟩, ⟨hx, f⟩ => by
    simp only [SafeLR]
    rw [filter_ne_eq]
    refine ⟨?_, safeLR_of_chainF φ h f⟩
    rcases rr_sound φ h x.name hx with h' | h'
    · simp at h'
    · exact h'

theorem termSafeLR_of_desc : (t : Term) → {ρ : List VarName} → DescTerm ρ t → TermFacts t →
    TermSafeLR (· ∈ ρ) t
  | .agg (.count dom b), ρ, h, ⟨hv, f⟩ | .agg (.sum _ dom b), ρ, h, ⟨hv, f⟩ => by
    simp only [TermSafeLR, AggSafeLR]
    rw [withoutDom_eq]
    refine ⟨fun v hvd => ?_, safeLR_of_chainF b h f⟩
    rcases rr_sound b h v.name (hv v hvd) with h' | h'
    · exact absurd h' (not_mem_withoutDom hvd)
    · exact h'
  | .arith _ l r, _, ⟨h₁, h₂⟩, ⟨f₁, f₂⟩ => ⟨termSafeLR_of_desc l h₁ f₁, termSafeLR_of_desc r h₂ f₂⟩
  | .entity _, _, _, _ | .long _, _, _, _ | .decimal _, _, _, _ | .string _, _, _, _
  | .bool _, _, _, _ | .context _, _, _, _ | .scope _ _, _, _, _ | .var _, _, _, _
  | .wildcard, _, _, _ => trivial

end

mutual

theorem chainF_of_safeLR : (φ : Formula) → {ρ : List VarName} → SafeLR (· ∈ ρ) φ →
    ChainF ρ φ ∧ FactsF φ
  | .and φ ψ, ρ, ⟨h₁, h₂⟩ => by
    obtain ⟨c₁, f₁⟩ := chainF_of_safeLR φ h₁
    rw [restricted_eq c₁] at h₂
    obtain ⟨c₂, f₂⟩ := chainF_of_safeLR ψ h₂
    exact ⟨⟨c₁, c₂⟩, ⟨f₁, f₂⟩⟩
  | .not φ, _, ⟨hfv, h⟩ => by
    obtain ⟨c, f⟩ := chainF_of_safeLR φ h
    exact ⟨⟨hfv, chainF_desc φ c⟩, f⟩
  | .formerly _ φ, _, h => by
    obtain ⟨c, f⟩ := chainF_of_safeLR φ h
    exact ⟨⟨chainF_conj φ c, c⟩, f⟩
  | .previous _ φ, _, h => by
    obtain ⟨c, f⟩ := chainF_of_safeLR φ h
    exact ⟨⟨chainF_conj φ c, c⟩, f⟩
  | .since φ _ ψ, ρ, ⟨h₁, h₂, h₃⟩ => by
    obtain ⟨c₂, f₂⟩ := chainF_of_safeLR ψ h₁
    rw [restricted_eq c₂] at h₃
    obtain ⟨c₁, f₁⟩ := chainF_of_safeLR φ h₃
    refine ⟨⟨fun y hy => ?_, c₁, c₂⟩, ⟨f₁, f₂⟩⟩
    have := (restricted_iff c₂ y).mpr (h₂ y hy)
    simp only [List.mem_append] at this
    exact this.symm
  | .pred _ _ _, _, _ => ⟨⟨trivial, trivial⟩, trivial⟩
  | .tp _, _, _ => ⟨⟨trivial, trivial⟩, trivial⟩
  | .cmp op l r, ρ, ⟨hfv, h₁, h₂⟩ => by
    obtain ⟨c₁, f₁⟩ := descTerm_of_safeLR l h₁
    obtain ⟨c₂, f₂⟩ := descTerm_of_safeLR r h₂
    exact ⟨⟨cmpDemands_iff.mpr hfv, c₁, c₂⟩, ⟨f₁, f₂⟩⟩
  | .exist x φ, ρ, ⟨h₁, h₂⟩ => by
    rw [filter_ne_eq] at h₁ h₂
    obtain ⟨c, f⟩ := chainF_of_safeLR φ h₂
    refine ⟨⟨chainF_conj φ c, c⟩, ⟨?_, f⟩⟩
    rcases rr_complete φ h₁ with h | h
    · simp at h
    · exact h

theorem descTerm_of_safeLR : (t : Term) → {ρ : List VarName} → TermSafeLR (· ∈ ρ) t →
    DescTerm ρ t ∧ TermFacts t
  | .agg (.count dom b), ρ, ⟨h₁, h₂⟩ | .agg (.sum _ dom b), ρ, ⟨h₁, h₂⟩ => by
    rw [withoutDom_eq] at h₁ h₂
    obtain ⟨c, f⟩ := chainF_of_safeLR b h₂
    refine ⟨c, fun v hv => ?_, f⟩
    rcases rr_complete b (h₁ v hv) with h | h
    · exact absurd h (not_mem_withoutDom hv)
    · exact h
  | .arith _ l r, _, ⟨h₁, h₂⟩ => by
    obtain ⟨c₁, f₁⟩ := descTerm_of_safeLR l h₁
    obtain ⟨c₂, f₂⟩ := descTerm_of_safeLR r h₂
    exact ⟨⟨c₁, c₂⟩, ⟨f₁, f₂⟩⟩
  | .entity _, _, _ | .long _, _, _ | .decimal _, _, _ | .string _, _, _ | .bool _, _, _
  | .context _, _, _ | .scope _ _, _, _ | .var _, _, _ | .wildcard, _, _ => ⟨trivial, trivial⟩

end

/-- **The crate's order check and restriction facts decide `SafeLR`.** -/
theorem chainF_factsF_iff (φ : Formula) (ρ : List VarName) :
    ChainF ρ φ ∧ FactsF φ ↔ SafeLR (· ∈ ρ) φ :=
  ⟨fun ⟨c, f⟩ => safeLR_of_chainF φ c f, chainF_of_safeLR φ⟩

end Dogwood.Thm.Frontend.Macros
