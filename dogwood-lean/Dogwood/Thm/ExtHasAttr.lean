import Cedar.Spec.Evaluator
import Cedar.Thm.Data.Map

/-!
# Cedar's extended `has`

Cedar 4.14 keeps `x has a.b.c` as one node (`Cedar.Spec.Expr.extHasAttr`), evaluated by
`Cedar.Spec.hasAttrs`: it walks the path, testing each attribute with `has` and reading it with
`.` before the next. These lemmas relate a step of the walk to Cedar's `hasAttr` and `getAttr`,
so that a proof about `x has a && x.a has b && …` carries over to the one node.
-/

namespace Dogwood.Thm

open Cedar.Spec (Value Attr Entities hasAttr getAttr hasAttrs attrsOf)
open Cedar.Data (Map)

/-- The walk over one attribute is `has`. -/
theorem hasAttrs_loop_single (v : Value) (a : Attr) (es : Entities) :
    hasAttrs.loop v [a] es = hasAttr v a es := by
  simp only [hasAttrs.loop, hasAttr]
  cases h : attrsOf v (fun uid => .ok (es.attrsOrEmpty uid)) with
  | error e =>
    have : e = .typeError := by
      unfold attrsOf at h
      split at h <;> simp_all
    subst this
    rfl
  | ok r =>
    simp only [Except.bind_ok]
    cases hf : r.find? a with
    | none =>
      have : r.contains a = false := by
        cases hc : r.contains a
        · rfl
        · obtain ⟨w, hw⟩ := (Map.contains_iff_some_find?).mp hc
          rw [hf] at hw; cases hw
      rw [this]
    | some w =>
      have : r.contains a = true := (Map.contains_iff_some_find?).mpr ⟨w, hf⟩
      rw [this]

/-- A walk that finds the first attribute: its `has` holds, and its `.` reads the value the walk
goes on from. -/
theorem hasAttrs_loop_cons_true {v : Value} {a : Attr} {as : List Attr} {es : Entities}
    (h : hasAttrs.loop v (a :: as) es = .ok true) :
    hasAttr v a es = .ok (.prim (.bool true)) ∧
      ∃ w, getAttr v a es = .ok w ∧ hasAttrs.loop w as es = .ok true := by
  simp only [hasAttrs.loop] at h
  split at h
  · rename_i r hr
    split at h
    · rename_i w hf
      refine ⟨?_, w, ?_, h⟩
      · simp only [hasAttr, hr, Except.bind_ok]
        rw [(Map.contains_iff_some_find?).mpr ⟨w, hf⟩]
      · simp only [getAttr]
        unfold attrsOf at hr ⊢
        split at hr
        · simp only [Except.ok.injEq] at hr
          subst hr
          simp [Map.findOrErr, hf]
        · simp only [Except.ok.injEq] at hr
          subst hr
          simp only [Entities.attrsOrEmpty] at hf
          simp only [Entities.attrs, Map.findOrErr]
          split at hf
          · rename_i d hd
            simp [hd, hf]
          · simp [Map.empty, Map.find?] at hf
        · cases hr
    · cases h
  · cases h

end Dogwood.Thm
