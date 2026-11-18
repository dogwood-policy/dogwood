import Dogwood.Examples.Common
import Dogwood.Thm.Canonical

/-!
# Canonical values

Regression examples for the canonical-value rule of runtime conformance
(`Dogwood.Spec.Canonical`, `EventSignature.Admits.canonical`). A set held out of order, `["b",
"a"]`, is a different Cedar value from `["a", "b"]` and compares unequal to it, though the two
have the same members. If an event that logged it conformed, a pin or a comparison over the
field could tell two spellings of one set apart. So it does not conform: an implementation
canonicalizes the set first, and then the two spellings are one value.
-/

namespace Dogwood.Examples.CanonicalValues

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Examples Dogwood.Thm
open Cedar.Spec (EntityUID Value Attr)
open Cedar.Validation (CedarType)
open Cedar.Data (Map Set)

def tag := action "Tag"
def actions : List ActionDecl := [(tag, [("tags", .set .string)])]
def schema : EventSchema := defaultSchema true actions
def A := actionSchema actions

def a : Value := .prim (.string "a")
def b : Value := .prim (.string "b")

/-- `["b", "a"]`, out of order. -/
def unsorted : Value := .set (Set.mk [b, a])
/-- `["a", "b"]`, as `Set.make` builds it. -/
def sorted : Value := .set (Set.make [b, a])

/-! The kernel cannot evaluate Cedar's order on values (`Value.decLt` is defined by well-founded
recursion), so the checks over sets below run the compiled deciders with `#guard`; the facts about
membership and equality are proved. -/

#guard sorted == .set (Set.mk [a, b])
-- The two spellings are different values, with the same members.
#guard unsorted != sorted
example : ∀ v, v ∈ Set.mk [b, a] ↔ v ∈ Set.mk [a, b] := fun _ => (List.Perm.swap a b []).mem_iff

#guard !canonicalB unsorted
#guard canonicalB sorted

theorem prims_canonical {xs : List Value} (h : ∀ v ∈ xs, ∃ p, v = .prim p) :
    ∀ v ∈ xs, Canonical v := fun v hv => by
  obtain ⟨p, rfl⟩ := h v hv; exact .prim p

/-- On canonical sets, equality is equality of members: `Set.make [b, a]` is `Set.make [a, b, a]`. -/
example : Value.set (Set.make [b, a]) = .set (Set.make [a, b, a]) :=
  (canonical_set_eq_iff
    (canonical_set_make (prims_canonical (by simp [a, b])))
    (canonical_set_make (prims_canonical (by simp [a, b])))).mpr fun v => by
    simp only [Set.mem_make, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (h | h) <;> simp [h]
    · rintro (h | h | h) <;> simp [h]

def tagged (tags : Value) : Event := logEvent (oauthUser "alice") tag "request" "t" [("tags", tags)]

-- An event that logs the unsorted set does not conform.
#guard !(tagged unsorted).conformsB A schema

-- The same event, canonicalized, conforms.
#guard (tagged sorted).conformsB A schema

end Dogwood.Examples.CanonicalValues
