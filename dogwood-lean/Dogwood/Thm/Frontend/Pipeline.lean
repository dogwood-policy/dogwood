import Dogwood.Frontend.Pipeline

/-!
# Theorems about the one-call pipeline

`lowerManyFull` of one entry under a distincter is `lowerFull` of it under that distincter, up to
the entry its errors name (`lowerManyFull_one`): the multi-entry checks (no repeated distincter,
an entry) pass for one entry, and naming the entry of an error is the only other difference
(`lowerEach_untag`, `lowerAndMerge_untag`).
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.Driver

/-- An error without the entry it belongs to. -/
def untag (e : Error) : Error := { e with entry := none }

/-- A pipeline error without its entry. -/
def untagP (p : Error × Option CedarSchema.Fragment) : Error × Option CedarSchema.Fragment :=
  (untag p.1, p.2)

/-- Naming the entry of an entry's error changes nothing else. -/
theorem lowerEach_untag (b : Base) : ∀ (k : Nat) (es : List EntryIn),
    (lowerEach b true k es).mapError untag = (lowerEach b false k es).mapError untag
  | _, [] => rfl
  | k, e :: es => by
    have ih := lowerEach_untag b (k + 1) es
    simp only [lowerEach, tagEntry, ↓reduceIte, Bool.false_eq_true, bind, Except.bind]
    cases h : lowerEntry b e with
    | error err => simp [Except.mapError, untag]
    | ok x =>
      simp only [Except.mapError]
      cases h1 : lowerEach b true (k + 1) es <;> cases h2 : lowerEach b false (k + 1) es <;>
        simp_all [Except.mapError, pure, Except.pure]

/-- Lowering and merging entries, with the entries of errors named or not, agree but for the
names. -/
theorem lowerAndMerge_untag (b : Base) (es : List EntryIn) :
    (lowerAndMerge b es true).mapError untagP = (lowerAndMerge b es false).mapError untagP := by
  have h := lowerEach_untag b 0 es
  simp only [lowerAndMerge, bind, Except.bind]
  cases h1 : lowerEach b true 0 es <;> cases h2 : lowerEach b false 0 es <;>
    simp_all [Except.mapError, untagP, untag]

/-- `lowerManyFull` of one entry under a distincter is `lowerFull` of it, but for the entry its
errors name (crate: `lower_many(&[(&p, d)], s)` is `p.lower_with_distincter(s, d)`). -/
theorem lowerManyFull_one (s : SharedInput) (e : EntryInput) (d : String)
    (hd : e.distincter = some d) :
    (lowerManyFull s [e]).mapError untagP = (lowerFull s e).mapError untagP := by
  simp only [lowerManyFull, lowerFull, hd, List.zipIdx_cons, List.zipIdx_nil, List.mapM_cons,
    List.mapM_nil, List.map_cons, List.map_nil, Option.getD_some, bind, Except.bind, pure,
    Except.pure]
  cases checkShared s with
  | error err => rfl
  | ok sh =>
  simp only [Except.mapError]
  cases parseEntry s e with
  | error err => simp [untagP, untag, atEntry]
  | ok p =>
  simp only [List.forIn_cons, List.forIn_nil, bind, Except.bind, pure, Except.pure]
  cases Ids.checkDistincter d with
  | error err => simp [untagP, untag, atEntry]
  | ok u =>
  simp only [Ids.firstRepeat, List.contains_nil, Bool.false_eq_true, ↓reduceIte, List.isEmpty_cons]
  cases actionSchemaOf s with
  | error err => rfl
  | ok frag =>
  simp only
  cases Base.derive sh.1 frag sh.2 with
  | error err => rfl
  | ok b =>
  simp only [List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil]
  exact lowerAndMerge_untag b _

end Dogwood.Thm.Frontend
