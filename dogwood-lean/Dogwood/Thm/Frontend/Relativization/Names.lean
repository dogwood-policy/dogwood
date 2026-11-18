import Dogwood.Thm.Frontend.LeafPasses.Basic

/-!
# The fresh names of the relativization rewrite

The rewrite draws its binders' names from a counter, with a prefix: `<pre><stem><n>`
(`LeafPasses.fresh`), the prefix chosen from the leaf's names (`LeafPasses.freshPrefix`). This
module proves what the relativization theorem needs of them:

* no variable of the leaf starts with the chosen prefix (`freshPrefix_fresh`), and every fresh
  name does (`startsWith_freshName`), so the leaf (`LeafPasses.NoFreshNames`) uses none of them
  (`ne_freshName`);
* the names one encoding draws are pairwise distinct: two stems that differ at a position both
  have (`freshName_ne_of_get`), or one stem and two counters (`freshName_inj`, by the injectivity
  of the decimal form of a number, `toString_nat_inj`);
* the variables of a condition do not change under pin injection (`condNames_injectCond`).
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.LeafPasses Surface.Temporal

/-! ## Prefixes -/

/-- A string starts with each of its prefixes. -/
theorem hasPrefix_append (p t : String) : hasPrefix p (p ++ t) = true := by
  simp [hasPrefix, String.toList_append, List.isPrefixOf_iff_prefix]

/-- No string starts with a longer one. -/
theorem hasPrefix_eq_false_of_length {p x : String} (h : x.length < p.length) :
    hasPrefix p x = false := by
  cases hs : hasPrefix p x with
  | false => rfl
  | true =>
    simp only [hasPrefix, List.isPrefixOf_iff_prefix] at hs
    have := hs.length_le
    simp only [String.length_toList] at this
    omega

theorem length_pinPrefix (k : Nat) : (pinPrefix k).length = 6 + k := by
  simp only [pinPrefix, String.length_append, String.length_ofList, List.length_replicate]
  rfl

theorem le_foldl_max_init : (xs : List Nat) → (a : Nat) → a ≤ xs.foldl max a
  | [], _ => Nat.le_refl _
  | y :: ys, a => Nat.le_trans (Nat.le_max_left a y) (le_foldl_max_init ys (max a y))

theorem le_foldl_max : (xs : List Nat) → (a : Nat) → ∀ x ∈ xs, x ≤ xs.foldl max a
  | [], _, _, hx => by simp at hx
  | y :: ys, a, x, hx => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_trans (Nat.le_max_right a x) (le_foldl_max_init ys _)
    · exact le_foldl_max ys _ x hx

/-- **The chosen prefix starts no name of the leaf.** -/
theorem freshPrefix_fresh (names : List String) :
    ∀ x ∈ names, hasPrefix (freshPrefix names) x = false := by
  intro x hx
  simp only [freshPrefix]
  split
  · rename_i k hk
    have := List.find?_some hk
    simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
    exact this x hx
  · apply hasPrefix_eq_false_of_length
    rw [length_pinPrefix]
    have := le_foldl_max (names.map String.length) 0 x.length (List.mem_map.mpr ⟨x, hx, rfl⟩)
    omega

/-- The fresh name of a prefix, a stem and a counter. -/
def freshName (pre stem : String) (n : Nat) : String := pre ++ (stem ++ toString n)

/-- Drawing a fresh name: the counter's name, and the counter moves on. -/
theorem fresh_run (pre stem : String) (n : Nat) :
    (fresh pre stem).run n = (freshName pre stem n, n + 1) := by
  simp only [fresh, StateT.run, get, set, getThe, MonadStateOf.get, StateT.get, MonadStateOf.set,
    StateT.set, bind, StateT.bind, pure, StateT.pure]
  simp [freshName, String.append_assoc]
  rfl

theorem startsWith_freshName (pre stem : String) (n : Nat) :
    hasPrefix pre (freshName pre stem n) = true :=
  hasPrefix_append _ _

/-- A name that does not start with the prefix is no fresh name. -/
theorem ne_freshName {pre x : String} (hx : hasPrefix pre x = false) (stem : String) (n : Nat) :
    x ≠ freshName pre stem n := by
  rintro rfl
  rw [startsWith_freshName] at hx
  cases hx

/-- A name that does not start with a prefix differs from every name that does. -/
theorem ne_of_startsWith {pre x y : String} (hx : hasPrefix pre x = false)
    (hy : hasPrefix pre y = true) : x ≠ y := by
  rintro rfl
  rw [hy] at hx
  cases hx

/-! ## Distinct fresh names -/

/-- Two fresh names whose stems differ at a position both stems have are distinct. -/
theorem freshName_ne_of_get {pre s t : String} (i : Nat) (hs : i < s.toList.length)
    (ht : i < t.toList.length) (h : s.toList[i] ≠ t.toList[i]) (a b : Nat) :
    freshName pre s a ≠ freshName pre t b := by
  intro heq
  have key : ∀ (u : String) (n : Nat) (hu : i < u.toList.length),
      (pre.toList ++ (u.toList ++ (toString n).toList))[pre.toList.length + i]? =
        some u.toList[i] := by
    intro u n hu
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left hu, List.getElem?_eq_getElem hu]
  have := congrArg (fun x => x.toList[pre.toList.length + i]?) heq
  simp only [freshName, String.toList_append] at this
  rw [key s a hs, key t b ht, Option.some.injEq] at this
  exact h this

theorem toDigits_inj : (m n : Nat) → Nat.toDigits 10 m = Nat.toDigits 10 n → m = n
  | m, n, h => by
    have hdig' : ∀ a, a < 10 → ∀ b, b < 10 → Nat.digitChar a = Nat.digitChar b → a = b := by
      decide
    have hdig : ∀ a b : Nat, a < 10 → b < 10 → Nat.digitChar a = Nat.digitChar b → a = b :=
      fun a b ha hb => hdig' a ha b hb
    rw [Nat.toDigits_eq_if (by decide), Nat.toDigits_eq_if (b := 10) (n := n) (by decide)] at h
    split at h <;> split at h
    · simp only [List.cons.injEq, and_true] at h
      exact hdig m n (by assumption) (by assumption) h
    · have := congrArg List.length h
      simp only [List.length_cons, List.length_nil, List.length_append] at this
      have := Nat.length_toDigits_pos (b := 10) (n := n / 10)
      omega
    · have := congrArg List.length h
      simp only [List.length_cons, List.length_nil, List.length_append] at this
      have := Nat.length_toDigits_pos (b := 10) (n := m / 10)
      omega
    · obtain ⟨h₁, h₂⟩ := List.append_inj' h rfl
      have hq := toDigits_inj (m / 10) (n / 10) h₁
      simp only [List.cons.injEq, and_true] at h₂
      have hr := hdig (m % 10) (n % 10) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) h₂
      omega
  termination_by m _ _ => m
  decreasing_by omega

/-- The decimal form of a number determines it. -/
theorem toString_nat_inj {m n : Nat} (h : toString m = toString n) : m = n := by
  rw [Nat.toString_eq_ofList_toDigits, Nat.toString_eq_ofList_toDigits] at h
  have := congrArg String.toList h
  simp only [String.toList_ofList] at this
  exact toDigits_inj m n this

/-- Two fresh names of one stem are distinct when their counters are. -/
theorem freshName_inj {pre s : String} {a b : Nat} (h : freshName pre s a = freshName pre s b) :
    a = b := by
  simp only [freshName] at h
  have h' := congrArg String.toList h
  simp only [String.toList_append, List.append_cancel_left_eq] at h'
  exact toString_nat_inj (String.toList_inj.mp h')

/-! ## Names under pin injection -/

theorem termNames_pinTerm (p : Pin) : termNames (pinTerm p) = [] := by
  unfold pinTerm; split <;> rfl

theorem argNames_append : (xs ys : List NamedArg) → argNames (xs ++ ys) = argNames xs ++ argNames ys
  | [], ys => rfl
  | ⟨_, t⟩ :: xs, ys => by
    simp only [List.cons_append, argNames, argNames_append xs ys, List.append_assoc]

theorem argNames_pinArgs : (ps : List Pin) → argNames (ps.map pinArg) = []
  | [] => rfl
  | p :: ps => by simp only [List.map_cons, pinArg, argNames, termNames_pinTerm, argNames_pinArgs ps]; rfl

mutual

/-- Pin injection adds no variable. -/
theorem condNames_injectCond (d : DerivedEventSchema) : (c : Condition) →
    condNames (injectCond d c) = condNames c
  | ⟨_, .and l r⟩ => by
    simp only [injectCond, injectKind, condNames, kindNames, condNames_injectCond d l,
      condNames_injectCond d r]
  | ⟨_, .or l r⟩ => by
    simp only [injectCond, injectKind, condNames, kindNames, condNames_injectCond d l,
      condNames_injectCond d r]
  | ⟨_, .since l _ r⟩ => by
    simp only [injectCond, injectKind, condNames, kindNames, condNames_injectCond d l,
      condNames_injectCond d r]
  | ⟨_, .not c⟩ => by simp only [injectCond, injectKind, condNames, kindNames, condNames_injectCond d c]
  | ⟨_, .formerly _ c⟩ => by
    simp only [injectCond, injectKind, condNames, kindNames, condNames_injectCond d c]
  | ⟨_, .previous _ c⟩ => by
    simp only [injectCond, injectKind, condNames, kindNames, condNames_injectCond d c]
  | ⟨_, .exists _ c⟩ => by
    simp only [injectCond, injectKind, condNames, kindNames, condNames_injectCond d c]
  | ⟨_, .predicate ⟨_, _, _, _, args⟩⟩ => by
    simp only [injectCond, injectKind, injectPred, condNames, kindNames, argNames_append,
      argNames_pinArgs, List.append_nil]
  | ⟨_, .comparison _ l r⟩ => by
    simp only [injectCond, injectKind, condNames, kindNames, termNames_injectTerm d l,
      termNames_injectTerm d r]
  | ⟨_, .tp _⟩ => rfl
  | ⟨_, .call _⟩ => rfl
  | ⟨_, .sigilRef _ _⟩ => rfl
  | ⟨_, .refine b _ _⟩ => by
    simp only [injectCond, injectKind, condNames, kindNames, condNames_injectCond d b]

theorem termNames_injectTerm (d : DerivedEventSchema) : (t : Surface.Temporal.Term) →
    termNames (injectTerm d t) = termNames t
  | .agg ⟨_, k⟩ => by
    simp only [injectTerm, injectAgg, termNames, aggNames_injectAggKind d k]
  | .arith _ l r => by
    simp only [injectTerm, termNames, termNames_injectTerm d l, termNames_injectTerm d r]
  | .entity _ _ | .integer _ | .decimal _ | .string _ | .bool _ | .contextField _ | .scopeField _
  | .var _ | .wildcard | .array _ | .paramRef _ | .binderRef _ => rfl

theorem aggNames_injectAggKind (d : DerivedEventSchema) : (k : AggExprKind) →
    aggNames (injectAggKind d k) = aggNames k
  | .sum _ _ b => by simp only [injectAggKind, aggNames, condNames_injectCond d b]
  | .count _ b => by simp only [injectAggKind, aggNames, condNames_injectCond d b]
  | .call _ => rfl

end

/-- The rewrite's prefix for a leaf is fresh for it. -/
theorem noFreshNames_freshPrefix (c : Condition) : NoFreshNames (freshPrefix (condNames c)) c :=
  freshPrefix_fresh (condNames c)

end Dogwood.Thm.Frontend
