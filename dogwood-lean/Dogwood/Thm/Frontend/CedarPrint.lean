import Dogwood.Frontend.CedarPrint

/-!
# Theorems about Cedar's printing of the lowered rules

The shape of what `Dogwood.Frontend.CedarPrint` computes: one canonical text per rule
(`ruleCanonical_length`), one policy JSON and one text per lowered rule (`policiesEst_length`,
`policiesText_length`), and the escaping of a character (`escapeChar`, which a pattern's
characters and every character of a string but its first go through) leaves every printable
ASCII character other than `"`, `'` and `\` as it is (`escapeChar_printable`). Names and
identifiers are printed without escaping (`nameStr`).
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.CedarPrint Dogwood.Frontend.Escape

/-- A `mapM` in `Except` that succeeds returns one result per element. -/
theorem mapM_except_length {ε α β : Type} (f : α → Except ε β) :
    ∀ (l : List α) (r : List β), l.mapM f = .ok r → r.length = l.length
  | [], r, h => by
    simp only [List.mapM_nil] at h
    cases h; rfl
  | a :: l, r, h => by
    simp only [List.mapM_cons] at h
    cases hf : f a with
    | error e => simp [hf] at h
    | ok b =>
      cases hl : l.mapM f with
      | error e => simp [hf, hl] at h
      | ok bs =>
        simp [hf, hl] at h
        cases h
        simp [mapM_except_length f l bs hl]

/-- Lowering every rule for its canonical text gives one text per rule. -/
theorem ruleCanonical_length (ps : Surface.PolicySet) (decls : Option ProviderDecls.Declarations)
    (enumNames : List (String × String)) (ts : List String)
    (h : ruleCanonical ps decls enumNames = .ok ts) : ts.length = ps.policies.length :=
  mapM_except_length _ _ _ h

/-- One policy JSON per lowered rule that has an expanded rule. -/
theorem policiesEst_length (ps : Surface.PolicySet) (rules : List Cedar.Spec.Policy) :
    (policiesEst ps rules).length = min rules.length ps.policies.length := by
  simp [policiesEst]

/-- One text per lowered rule that has an expanded rule. -/
theorem policiesText_length (ps : Surface.PolicySet) (rules : List Cedar.Spec.Policy) :
    (policiesText ps rules).length = min rules.length ps.policies.length := by
  simp [policiesText]

/-- Every ASCII character from `0x20` to `0x7e` is printable. -/
theorem isPrintable_ascii (c : Char) (h₁ : 0x20 ≤ c.toNat) (h₂ : c.toNat < 0x7f) :
    isPrintable c = true := by
  unfold isPrintable
  simp only
  rw [if_neg (by omega), if_pos h₂]

/-- A printable ASCII character other than `"`, `'` and `\` is printed as itself. -/
theorem escapeChar_printable (e : Bool) (c : Char) (h₁ : 0x20 ≤ c.toNat) (h₂ : c.toNat < 0x7f)
    (hq : c ≠ '"') (ha : c ≠ '\'') (hb : c ≠ '\\') : escapeChar e c = String.singleton c := by
  have h0 : c.toNat ≠ 0 := by omega
  have ht : c ≠ '\t' := by intro h; subst h; simp at h₁
  have hr : c ≠ '\r' := by intro h; subst h; simp at h₁
  have hn : c ≠ '\n' := by intro h; subst h; simp at h₁
  have hg : isGraphemeExtended c = false := by
    unfold isGraphemeExtended; simp; omega
  unfold escapeChar escapeDebugExt
  simp [h0, ht, hr, hn, hb, hq, ha, hg, isPrintable_ascii c h₁ h₂]

end Dogwood.Thm.Frontend
