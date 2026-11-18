import Dogwood.Thm.Frontend.Relativization.Core
import Dogwood.Thm.Frontend.Relativization.Ord
import Dogwood.Thm.Frontend.LeafPasses.Conservative
import Dogwood.Thm.Frontend.LeafPasses.Relativize
import Dogwood.Thm.Injection

/-!
# The relativization theorem

The crate realizes key-local semantics by rewriting each temporal leaf (`LeafPasses.relativize`)
and evaluating the rewrite with every timepoint visible. The specification states key-local
semantics directly, by visibility (`EventSchema.Visible`). `relativization_correct` proves that
the two agree, on traces whose timestamps strictly increase (`LeafPasses.RelativizationTheorem`,
whose docstring lists the hypotheses and why each is needed).

The proof composes four steps, for a leaf `c` authored as `φ`, with its pins injected
(`c' = injectCond d c`, which projects to `φ.injectPins S`):

1. **The executable form is `c'` itself** (`unorderFree_of_typed`, `unorderCond_eq_self`):
   typing orders and computes only with `Long`s.
2. **The rewrite with every timepoint visible is `c'` with the key's timepoints visible**
   (`rsat_relCond`), both under `RSat`. Without a universal symmetric pin the rewrite is the
   identity and every timepoint is visible to the specification too.
3. **Ordering timepoints by position changes nothing on `c'`** (`xsat_ord_iff`): typing and
   safety keep timepoints out of every ordering.
4. **The extended relation is the specification's `Sat`** (`xsat_iff_sat`).
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.LeafPasses Surface.Temporal
open Dogwood.Spec (Event Trace TickRate EventSchema PolicySet)
open Dogwood.Spec.Temporal (Valuation ImplChoices Formula)

/-- The crate's universal pins are empty exactly when the specification's are. -/
theorem universalPins_nil_iff {d : DerivedEventSchema} {S : EventSchema} (h : Agrees d S)
    {pins : List Pin} (hp : universalPins d = .ok pins) :
    pins = [] ↔ EventSchema.universalPins S = [] := by
  have hS : d.events.mapM eventToSpec = .ok (strip S) := h.untyped
  obtain ⟨qs, hqs, hmem, _⟩ := universalPins_toSpec hS hp
  rw [universalPins_strip] at hmem
  constructor
  · rintro rfl
    simp only [List.mapM_nil, pure_eq_ok] at hqs
    subst hqs
    exact List.eq_nil_iff_forall_not_mem.mpr fun q hq => by simpa using (hmem q).mpr hq
  · intro hu
    cases pins with
    | nil => rfl
    | cons p ps =>
      simp only [List.mapM_cons, bind_eq_ok, pure_eq_ok] at hqs
      obtain ⟨q, _, qs', _, rfl⟩ := hqs
      have := (hmem q).mp (List.mem_cons_self ..)
      rw [hu] at this
      cases this

/-- **The relativization theorem.** On a trace whose timestamps strictly increase, and which is
not longer than the largest `Long`, the crate's relativized executable leaf, evaluated with every
timepoint visible, holds at a decision exactly when the specification's leaf does
(`PolicySet.LeafHolds`), for a well-typed, safe leaf, over a derived event schema that agrees
with the policy set's (`LeafPasses.RelativizationTheorem` lists every hypothesis). The rewrite's
fresh names start with a prefix no variable of the leaf starts with (`noFreshNames_freshPrefix`).
-/
theorem relativization_correct : RelativizationTheorem := by
  intro ι P d pins c φ r σ n hag hpins hc hinj hty hsafe hrel hinc hlen
  obtain ⟨C, hCe, hty⟩ := hty
  have hσ : σ.Nondecreasing := Dogwood.Spec.Trace.StrictlyIncreasing.nondecreasing hinc
  -- The injected leaf: typed, safe, pinned.
  have hty' : (φ.injectPins P.schema).WellTyped C [] := by
    have := Dogwood.Thm.Formula.wellTyped_injectPins hty
    rwa [hCe] at this
  have hsafe' : (φ.injectPins P.schema).IsSafe :=
    (Dogwood.Thm.Formula.isSafe_injectPins P.schema φ).mpr hsafe
  have hpin : (φ.injectPins P.schema).Pinned P.schema := by
    have := pinned_injectPins hty
    rwa [hCe] at this
  -- Step 1: the executable form is the injected leaf.
  have hfree : unorderFree [] (injectCond d c) = true :=
    unorderFree_of_typed _ hinj hty' (Γt := []) fun x h => by simp [isTimepoint] at h
  rw [unorderCond_eq_self _ [] hfree] at hrel
  unfold PolicySet.LeafHolds
  refine exists_congr fun p => and_congr_right fun _ => ?_
  -- Steps 3 and 4: the injected leaf under `RSat` is the specification's.
  have hspec : RSat ι P.tickRate σ p.event (P.schema.Visible σ p.event) Valuation.empty n
      (injectCond d c) ↔ Dogwood.Spec.Temporal.Sat ι P.tickRate σ p.event
        (P.schema.Visible σ p.event) Valuation.empty n (φ.injectPins P.schema) :=
    (xsat_ord_iff (injectCond d c) hinj hty' hsafe' (fun _ h => h.elim) n).trans
      (xsat_iff_sat _ hinj _ _)
  rw [← hspec]
  -- Step 2: the rewrite.
  by_cases hne : pins = []
  · subst hne
    rw [relativize_nil, Except.ok.injEq] at hrel
    subst hrel
    have hu := (universalPins_nil_iff hag hpins).mp rfl
    have hvis : P.schema.Visible σ p.event = fun _ => True :=
      funext fun k => propext (by simp [EventSchema.Visible, hu])
    rw [hvis]
  · have hune : EventSchema.universalPins P.schema ≠ [] :=
      fun h => hne ((universalPins_nil_iff hag hpins).mpr h)
    cases hev : d.events with
    | nil =>
      simp [relativize, hne, hev, throw, throwThe, MonadExceptOf.throw] at hrel
    | cons e₀ es =>
      have hr : r = ((relCond (freshPrefix (condNames (injectCond d c))) (mu pins e₀ es)
          (injectCond d c)).run 0).1 := by
        simp only [relativize, hev] at hrel
        rw [if_neg (by simpa using hne)] at hrel
        simp only [pure, Except.pure, Except.ok.injEq] at hrel
        exact hrel.symm
      subst hr
      exact rsat_relCond (S := P.schema)
        (fun sp v k => xsat_mu_iff_visible hag hune hpins hev sp v k) hσ hlen
        (injectCond d c) hinj hpin (noFreshNames_freshPrefix _) 0 Valuation.empty n

end Dogwood.Thm.Frontend
