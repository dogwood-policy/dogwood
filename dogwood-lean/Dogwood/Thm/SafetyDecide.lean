import Dogwood.Eval.Safety
import Dogwood.Thm.Restriction

/-!
# The safety check decides safety

`restrictsB_iff`: `restrictsB` computes the restriction closure. `safeB_iff`: `safeB` decides
`Formula.Safe`, and `isSafeB_iff` decides `Formula.IsSafe`.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Eval

theorem mem_predVars {args : List (Path × Term)} {x : VarName} :
    x ∈ predVars args ↔ ∃ p, (p, Term.var x) ∈ args := by
  induction args with
  | nil => simp [predVars]
  | cons a args ih =>
    obtain ⟨p, t⟩ := a
    cases t
    case var y =>
      simp only [predVars, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨q, hq⟩)
        · exact ⟨p, .inl rfl⟩
        · exact ⟨q, .inr hq⟩
      · rintro ⟨q, hq | hq⟩
        · cases hq; exact .inl rfl
        · exact .inr ⟨q, hq⟩
    all_goals
      simp only [predVars, ih, List.mem_cons]
      constructor
      · rintro ⟨q, hq⟩; exact ⟨q, .inr hq⟩
      · rintro ⟨q, hq | hq⟩
        · cases hq
        · exact ⟨q, hq⟩

/-- Two predicates that agree everywhere are equal. -/
theorem pred_ext {R R' : VarName → Prop} (h : ∀ z, R z ↔ R' z) : R = R' :=
  funext fun z => propext (h z)

theorem restrictsB_iff : (φ : Formula) → (R : List VarName) → ∀ x,
    x ∈ restrictsB R φ ↔ φ.Restricts (· ∈ R) x
  | .pred _ _ args, R, x => by simp only [restrictsB, Formula.Restricts]; exact mem_predVars
  | .tp y, R, x => by simp [restrictsB, Formula.Restricts]
  | .cmp op l r, R, x => by
    cases op <;> simp only [restrictsB, Formula.Restricts, List.not_mem_nil]
    cases h : eqRestricted? l r with
    | none => simp
    | some y =>
      simp only
      split
      · rename_i hall
        simp only [List.all_eq_true, List.contains_iff_mem] at hall
        simp only [List.mem_singleton, Option.some.injEq]
        constructor
        · rintro rfl; exact ⟨rfl, hall⟩
        · rintro ⟨rfl, _⟩; rfl
      · rename_i hall
        simp only [List.all_eq_true, List.contains_iff_mem] at hall
        simp only [List.not_mem_nil, false_iff, not_and, Option.some.injEq]
        rintro rfl hall'
        exact hall hall'
  | .not _, R, x => by simp [restrictsB, Formula.Restricts]
  | .formerly _ φ, R, x => restrictsB_iff φ R x
  | .previous _ φ, R, x => restrictsB_iff φ R x
  | .since _ _ ψ, R, x => restrictsB_iff ψ R x
  | .exist y φ, R, x => by
    simp only [restrictsB, Formula.Restricts, List.mem_filter, bne_iff_ne, ne_eq]
    rw [restrictsB_iff φ, and_comm]
    have : (· ∈ R.filter (· != y.name)) = fun z => z ≠ y.name ∧ z ∈ R :=
      pred_ext fun z => by simp [List.mem_filter, and_comm]
    rw [this]
  | .and φ ψ, R, x => by
    let f : List VarName → List VarName := fun S =>
      (S ++ restrictsB S φ ++ restrictsB S ψ).eraseDups
    have stage : ∀ i z, z ∈ iter f i R ↔ Formula.stage (· ∈ R) φ ψ i z := by
      intro i
      induction i with
      | zero => intro z; rfl
      | succ i ih =>
        intro z
        show z ∈ f (iter f i R) ↔ _
        simp only [f, List.mem_eraseDups, List.mem_append, restrictsB_iff φ, restrictsB_iff ψ, ih,
          Formula.stage, or_assoc]
    show x ∈ iter f ((Formula.and φ ψ).fv.length + 1) R ↔ _
    rw [stage, Formula.restricts_and_iff]
    rfl

theorem restrictedB_iff {φ : Formula} {R : List VarName} {x : VarName} :
    x ∈ R ++ restrictsB R φ ↔ φ.Restricted (· ∈ R) x := by
  simp [Formula.Restricted, restrictsB_iff]

mutual

theorem safeB_iff : (φ : Formula) → (R : List VarName) → (safeB R φ = true ↔ φ.Safe (· ∈ R))
  | .and φ ψ, R => by
    have h : (· ∈ restrictsB R (.and φ ψ)) = (Formula.and φ ψ).Restricts (· ∈ R) :=
      pred_ext (restrictsB_iff (.and φ ψ) R)
    simp only [safeB, Bool.and_eq_true, Formula.Safe, safeB_iff φ, safeB_iff ψ, h]
  | .not φ, R => by
    simp only [safeB, Bool.and_eq_true, Formula.Safe, safeB_iff φ, List.all_eq_true,
      List.contains_iff_mem]
  | .formerly _ φ, R => safeB_iff φ R
  | .previous _ φ, R => safeB_iff φ R
  | .since φ _ ψ, R => by
    have h : (· ∈ R ++ restrictsB R ψ) = ψ.Restricted (· ∈ R) :=
      pred_ext fun z => restrictedB_iff
    simp only [safeB, Bool.and_eq_true, Formula.Safe, safeB_iff φ, safeB_iff ψ, List.all_eq_true,
      List.contains_iff_mem, h, and_assoc]
  | .pred _ _ _, R => by simp [safeB, Formula.Safe]
  | .tp _, R => by simp [safeB, Formula.Safe]
  | .cmp op l r, R => by
    simp only [safeB, Bool.and_eq_true, Formula.Safe, termSafeB_iff l, termSafeB_iff r,
      List.all_eq_true, List.contains_iff_mem, restrictedB_iff, and_assoc]
  | .exist x φ, R => by
    have h : (· ∈ R.filter (· != x.name)) = fun z => z ≠ x.name ∧ z ∈ R :=
      pred_ext fun z => by simp [List.mem_filter, and_comm]
    simp only [safeB, Bool.and_eq_true, Formula.Safe, safeB_iff φ, List.contains_iff_mem,
      restrictsB_iff, h]

theorem termSafeB_iff : (t : Term) → {R : List VarName} → (termSafeB R t = true ↔ t.Safe (· ∈ R))
  | .agg a, R => aggSafeB_iff a
  | .arith _ l r, R => by
    simp only [termSafeB, Bool.and_eq_true, Term.Safe, termSafeB_iff l, termSafeB_iff r]
  | .entity _, _ | .long _, _ | .decimal _, _ | .string _, _ | .bool _, _ | .context _, _
  | .scope _ _, _ | .var _, _ | .wildcard, _ => by simp [termSafeB, Term.Safe]

theorem aggSafeB_iff : (a : Aggregate) → {R : List VarName} →
    (aggSafeB R a = true ↔ a.Safe (· ∈ R))
  | .count dom body, R | .sum _ dom body, R => by
    have h : (· ∈ R.filter fun z => !(dom.map (·.name)).contains z) =
        fun z => z ∉ dom.map (·.name) ∧ z ∈ R :=
      pred_ext fun z => by simp [List.mem_filter, and_comm]
    simp only [aggSafeB, Bool.and_eq_true, Aggregate.Safe, safeB_iff body, List.all_eq_true,
      List.contains_iff_mem, restrictsB_iff, h]

end

/-- **The safety check decides safety.** -/
theorem isSafeB_iff (φ : Formula) : isSafeB φ = true ↔ φ.IsSafe := by
  have h : (· ∈ ([] : List VarName)) = fun _ => False := pred_ext fun z => by simp
  rw [isSafeB, safeB_iff, h]
  rfl

instance (φ : Formula) : Decidable φ.IsSafe := decidable_of_iff _ (isSafeB_iff φ)

end Dogwood.Thm
