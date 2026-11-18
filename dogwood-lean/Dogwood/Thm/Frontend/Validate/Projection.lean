import Dogwood.Thm.Frontend.Validate.Interface
import Dogwood.Thm.Facts
import Dogwood.Thm.Lowering
import Dogwood.Thm.Conservative
import Cedar.Thm.Data.List

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.Validate
open Dogwood.Spec (Expr Leaf leafAttr)
open Dogwood.Spec.Temporal (Formula Guard)

/-! ## The specification's leaf names are distinct -/

def decodeDigits (cs : List Char) : Nat := cs.foldl (fun acc c => 10 * acc + (c.toNat - 48)) 0

theorem digitChar_toNat : ∀ n, n < 10 → (Nat.digitChar n).toNat = 48 + n := by decide

theorem decode_toDigits (n : Nat) : decodeDigits (Nat.toDigits 10 n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.toDigits_eq_if (by decide)]
    split
    · rename_i h
      simp [decodeDigits, digitChar_toNat n h]
    · rename_i h
      have h1 := ih (n / 10) (by omega)
      unfold decodeDigits at h1 ⊢
      rw [List.foldl_append, h1]
      simp [digitChar_toNat (n % 10) (by omega)]
      omega

theorem repr_inj {i j : Nat} (h : i.repr = j.repr) : i = j := by
  have : Nat.toDigits 10 i = Nat.toDigits 10 j := by
    have := congrArg String.toList h
    simpa [Nat.repr_eq_ofList_toDigits, String.toList_ofList] using this
  rw [← decode_toDigits i, ← decode_toDigits j, this]

/-- The specification's leaf names are distinct. -/
theorem leafAttr_inj {i j : Nat} (h : leafAttr i = leafAttr j) : i = j := by
  unfold leafAttr at h
  exact repr_inj ((String.append_right_inj _).mp h)

theorem isPrefixOf_self_append : ∀ (l₁ l₂ : List Char), l₁.isPrefixOf (l₁ ++ l₂) = true
  | [], _ => rfl
  | _ :: l₁, l₂ => by simp [isPrefixOf_self_append l₁ l₂]

theorem isSpecLeafName_leafAttr (k : Nat) : isSpecLeafName (leafAttr k) = true := by
  simp only [isSpecLeafName, leafAttr, String.toList_append]
  exact isPrefixOf_self_append _ _

/-! ## Put-back leaves are the hoisted reads -/

/-- The leaf a hoisted read is put back as. -/
def readLeaf (T : List (String × Formula)) (P : List (String × Dogwood.Spec.Provider.Call)) :
    Bool × String → Leaf
  | (true, a) => .inl ((T.lookup a).getD default)
  | (false, a) => .inr ((P.lookup a).getD default)

theorem lookup_isSome_iff {β : Type} {L : List (String × β)} {a : String} :
    (L.lookup a).isSome = (L.map Prod.fst).contains a := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨k, v⟩ := p
    by_cases h : a = k
    · subst h; simp [List.lookup]
    · have : (a == k) = false := by simpa using h
      simp [List.lookup, this, ih, h]


theorem lookup_eq_some_of_contains {β : Type} {L : List (String × β)} {a : String}
    (h : (L.map Prod.fst).contains a = true) : ∃ v, L.lookup a = some v := by
  rw [← lookup_isSome_iff] at h
  exact Option.isSome_iff_exists.mp h

theorem lookup_eq_none_of_not_contains {β : Type} {L : List (String × β)} {a : String}
    (h : (L.map Prod.fst).contains a = false) : L.lookup a = none := by
  rw [← lookup_isSome_iff] at h
  simpa using h

section
variable (T : List (String × Formula)) (P : List (String × Dogwood.Spec.Provider.Call))

/-- `putBack` on an attribute access, by cases. -/
theorem putBack_getAttr (e : Expr) (a : String) :
    putBack T P (.getAttr e a) =
      if isContext e && (T.map Prod.fst).contains a then .temporal ((T.lookup a).getD default)
      else if isContextProviders e && (P.map Prod.fst).contains a then
        .provider ((P.lookup a).getD default)
      else .getAttr (putBack T P e) a := by
  by_cases hc : isContext e = true
  · have hp : isContextProviders e = false := by
      cases e <;> simp_all [isContext, isContextProviders]
    by_cases ha : (T.map Prod.fst).contains a = true
    · obtain ⟨φ, hφ⟩ := lookup_eq_some_of_contains ha
      rw [if_pos (by rw [hc, ha]; rfl)]
      simp only [putBack, hc, if_true, hφ, hp, Option.getD_some]
    · have ha' : (T.map Prod.fst).contains a = false := Bool.eq_false_iff.mpr ha
      have hn := lookup_eq_none_of_not_contains ha'
      rw [if_neg (by rw [hc, ha']; simp), if_neg (by rw [hp]; simp)]
      simp only [putBack, hc, if_true, hn, hp]
      rfl
  · have hc' : isContext e = false := Bool.eq_false_iff.mpr hc
    rw [if_neg (by rw [hc']; simp)]
    by_cases hp : isContextProviders e = true
    · by_cases ha : (P.map Prod.fst).contains a = true
      · obtain ⟨c, hcv⟩ := lookup_eq_some_of_contains ha
        rw [if_pos (by rw [hp, ha]; rfl)]
        simp only [putBack, hc', hp, hcv, Option.getD_some]
        rfl
      · have ha' : (P.map Prod.fst).contains a = false := Bool.eq_false_iff.mpr ha
        have hn := lookup_eq_none_of_not_contains ha'
        rw [if_neg (by rw [hp, ha']; simp)]
        simp only [putBack, hc', hp, hn]
        rfl
    · have hp' : isContextProviders e = false := Bool.eq_false_iff.mpr hp
      rw [if_neg (by rw [hp']; simp)]
      simp only [putBack, hc', hp']
      rfl

mutual

/-- **The leaves of a put-back expression are its hoisted reads**, in order. -/
theorem leaves_putBack : (x : Expr) → x.leaves = [] →
    (putBack T P x).leaves = (hoistedReads (T.map Prod.fst) (P.map Prod.fst) x).map (readLeaf T P)
  | .getAttr e a, h => by
    simp only [Expr.leaves] at h
    rw [putBack_getAttr]
    simp only [hoistedReads]
    split
    · simp [Expr.leaves, readLeaf]
    · split
      · simp [Expr.leaves, readLeaf]
      · simp only [Expr.leaves]; exact leaves_putBack e h
  | .lit _, _ | .var _, _ => by simp [putBack, Expr.leaves, hoistedReads]
  | .temporal _, h | .provider _, h => by simp [Expr.leaves] at h
  | .ite c t e, h => by
    simp only [Expr.leaves, List.append_eq_nil_iff] at h
    simp only [putBack, Expr.leaves, hoistedReads, List.map_append, leaves_putBack c h.1.1,
      leaves_putBack t h.1.2, leaves_putBack e h.2]
  | .and a b, h | .or a b, h | .binaryApp _ a b, h => by
    simp only [Expr.leaves, List.append_eq_nil_iff] at h
    simp only [putBack, Expr.leaves, hoistedReads, List.map_append, leaves_putBack a h.1,
      leaves_putBack b h.2]
  | .unaryApp _ e, h | .hasAttr e _, h | .extHasAttr e _ _, h => by
    simp only [Expr.leaves] at h
    simp only [putBack, Expr.leaves, hoistedReads, leaves_putBack e h]
  | .set xs, h | .call _ xs, h => by
    simp only [Expr.leaves] at h
    simp only [putBack, Expr.leaves, hoistedReads, leaves_putBackList xs h]
  | .record axs, h => by
    simp only [Expr.leaves] at h
    simp only [putBack, Expr.leaves, hoistedReads, leaves_putBackRecord axs h]

theorem leaves_putBackList : (xs : List Expr) → Expr.leavesList xs = [] →
    Expr.leavesList (putBackList T P xs) =
      (hoistedReadsList (T.map Prod.fst) (P.map Prod.fst) xs).map (readLeaf T P)
  | [], _ => rfl
  | x :: xs, h => by
    simp only [Expr.leavesList, List.append_eq_nil_iff] at h
    simp only [putBackList, Expr.leavesList, hoistedReadsList, List.map_append,
      leaves_putBack x h.1, leaves_putBackList xs h.2]

theorem leaves_putBackRecord : (axs : List (String × Expr)) → Expr.leavesRecord axs = [] →
    Expr.leavesRecord (putBackRecord T P axs) =
      (hoistedReadsRecord (T.map Prod.fst) (P.map Prod.fst) axs).map (readLeaf T P)
  | [], _ => rfl
  | (_, x) :: axs, h => by
    simp only [Expr.leavesRecord, List.append_eq_nil_iff] at h
    simp only [putBackRecord, Expr.leavesRecord, hoistedReadsRecord, List.map_append,
      leaves_putBack x h.1, leaves_putBackRecord axs h.2]

end

end

/-! ## Facts survive the put-back, outside reserved heads -/

/-- The facts `G` are among `F`, outside the paths whose head lowering reserves. -/
def NrSub (G F : List Guard) : Prop := ∀ g ∈ G, g.reservedHead = false → g ∈ F

theorem NrSub.append {G₁ G₂ F₁ F₂ : List Guard} (h₁ : NrSub G₁ F₁) (h₂ : NrSub G₂ F₂) :
    NrSub (G₁ ++ G₂) (F₁ ++ F₂) := by
  intro g hg hr
  rcases List.mem_append.mp hg with h | h
  · exact List.mem_append_left _ (h₁ g h hr)
  · exact List.mem_append_right _ (h₂ g h hr)

theorem isHoistedName_providers : isHoistedName "providers" = true := by
  simp [isHoistedName]

theorem mem_of_contains {l : List String} {a : String} (h : l.contains a = true) : a ∈ l := by
  simpa using h

theorem eq_of_isContext {y : Expr} (h : isContext y = true) : y = .var .context := by
  unfold isContext at h; split at h <;> simp_all

theorem eq_of_isContextProviders {y : Expr} (h : isContextProviders y = true) :
    y = .getAttr (.var .context) "providers" := by
  unfold isContextProviders at h; split at h <;> simp_all

variable {T P} in
/-- An attribute chain that does not pass through a hoisted read is unchanged by the put-back. -/
theorem attrChain_putBack (hT : ∀ a ∈ T.map Prod.fst, isHoistedName a = true) :
    ∀ (x : Expr) (v : Cedar.Spec.Var) (p : Dogwood.Spec.Path), x.attrChain? = some (v, p) →
      (v = .context → ∀ h t, p = h :: t → isHoistedName h = false) →
      (putBack T P x).attrChain? = some (v, p)
  | .var w, v, p, h, _ => by
    simp only [Expr.attrChain?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .getAttr y a, v, p, h, hn => by
    simp only [Expr.attrChain?] at h
    cases hy : y.attrChain? with
    | none => rw [hy] at h; cases h
    | some vp =>
      obtain ⟨v', p'⟩ := vp
      rw [hy] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [putBack_getAttr]
      split
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        exfalso
        have hy' := eq_of_isContext hc.1
        subst hy'
        simp only [Expr.attrChain?, Option.some.injEq, Prod.mk.injEq] at hy
        obtain ⟨rfl, rfl⟩ := hy
        have := hn rfl a [] rfl
        rw [hT a (mem_of_contains hc.2)] at this
        cases this
      · split
        · rename_i _ hc
          simp only [Bool.and_eq_true] at hc
          exfalso
          have hy' := eq_of_isContextProviders hc.1
          subst hy'
          simp only [Expr.attrChain?, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hy
          obtain ⟨rfl, rfl⟩ := hy
          have := hn rfl "providers" [a] rfl
          rw [isHoistedName_providers] at this
          cases this
        · simp only [Expr.attrChain?]
          rw [attrChain_putBack hT y v' p' hy (fun hv h t hp => hn hv h (t ++ [a]) (by simp [hp]))]
          rfl
  | .lit _, _, _, h, _ | .ite _ _ _, _, _, h, _ | .and _ _, _, _, h, _ | .or _ _, _, _, h, _
  | .unaryApp _ _, _, _, h, _ | .binaryApp _ _ _, _, _, h, _ | .hasAttr _ _, _, _, h, _
  | .extHasAttr _ _ _, _, _, h, _
  | .set _, _, _, h, _ | .record _, _, _, h, _ | .call _ _, _, _, h, _
  | .temporal _, _, _, h, _ | .provider _, _, _, h, _ => by simp [Expr.attrChain?] at h

/-- The facts of an extended `has` depend only on its operand's attribute chain. -/
theorem extHasFacts_congr : ∀ (as : List String) (x y : Expr) (a : String),
    x.attrChain? = y.attrChain? → x.extHasFacts a as = y.extHasFacts a as
  | [], x, y, a, h => by simp only [Expr.extHasFacts, Expr.hasFact?, h]
  | b :: bs, x, y, a, h => by
    simp only [Expr.extHasFacts]
    rw [extHasFacts_congr bs (.getAttr x a) (.getAttr y a) b (by simp only [Expr.attrChain?, h])]
    simp only [Expr.hasFact?, h]

/-- An extended `has` on an operand that is not an attribute chain establishes no fact. -/
theorem extHasFacts_none : ∀ (as : List String) (x : Expr) (a : String),
    x.attrChain? = none → x.extHasFacts a as = []
  | [], x, a, h => by simp [Expr.extHasFacts, Expr.hasFact?, h]
  | b :: bs, x, a, h => by
    simp only [Expr.extHasFacts]
    rw [extHasFacts_none bs (.getAttr x a) b (by simp [Expr.attrChain?, h])]
    simp [Expr.hasFact?, h]

/-- The facts of an extended `has` on an attribute chain of the context with head `h` are paths
of the context with head `h`. -/
theorem extHasFacts_context {h : String} : ∀ (as : List String) (x : Expr) (t : Dogwood.Spec.Path)
    (a : String), x.attrChain? = some (.context, h :: t) →
    ∀ g ∈ x.extHasFacts a as, ∃ r, g = .context (h :: r)
  | [], x, t, a, hx, g, hg => by
    simp only [Expr.extHasFacts, Expr.hasFact?, hx, Option.toList_some, List.mem_singleton] at hg
    exact ⟨t ++ [a], by rw [hg]; rfl⟩
  | b :: bs, x, t, a, hx, g, hg => by
    simp only [Expr.extHasFacts, List.mem_append] at hg
    rcases hg with hg | hg
    · simp only [Expr.hasFact?, hx, Option.toList_some, List.mem_singleton] at hg
      exact ⟨t ++ [a], by rw [hg]; rfl⟩
    · exact extHasFacts_context bs (.getAttr x a) (t ++ [a]) b
        (by simp only [Expr.attrChain?, hx, Option.map_some]; rfl) g hg

variable {T P} in
/-- **The facts an expression establishes survive the put-back**, outside reserved heads. -/
theorem facts_putBack (hT : ∀ a ∈ T.map Prod.fst, isHoistedName a = true) :
    ∀ x : Expr, NrSub x.facts (putBack T P x).facts
  | .hasAttr x a => by
    intro g hg hr
    simp only [Expr.facts, putBack] at hg ⊢
    unfold Expr.hasFact? at hg ⊢
    cases hc : x.attrChain? with
    | none => rw [hc] at hg; simp at hg
    | some vp =>
      obtain ⟨v, p⟩ := vp
      rw [attrChain_putBack hT x v p hc (fun hv h t hp => by
        subst hv hp
        rw [hc] at hg
        simp only [Option.toList_some, List.mem_singleton] at hg
        subst hg
        simpa [Guard.reservedHead] using hr)]
      rw [hc] at hg
      exact hg
  | .extHasAttr x a as => by
    intro g hg hr
    simp only [Expr.facts, putBack] at hg ⊢
    cases hc : x.attrChain? with
    | none => rw [extHasFacts_none as x a hc] at hg; cases hg
    | some vp =>
      obtain ⟨v, p⟩ := vp
      by_cases hbad : v = .context ∧ ∃ h t, p = h :: t ∧ isHoistedName h = true
      · exfalso
        obtain ⟨rfl, h, t, rfl, hh⟩ := hbad
        obtain ⟨r, rfl⟩ := extHasFacts_context as x t a hc g hg
        simp [Guard.reservedHead, hh] at hr
      · have hH : v = .context → ∀ h t, p = h :: t → isHoistedName h = false := by
          intro hv h t hp
          cases hn : isHoistedName h
          · rfl
          · exact absurd ⟨hv, h, t, hp, hn⟩ hbad
        rwa [extHasFacts_congr as (putBack T P x) x a (by rw [attrChain_putBack hT x v p hc hH, hc])]
  | .and a b => by
    simp only [Expr.facts, putBack]
    exact NrSub.append (facts_putBack hT a) (facts_putBack hT b)
  | .getAttr _ _ | .lit _ | .var _ | .ite _ _ _ | .or _ _ | .unaryApp _ _ | .binaryApp _ _ _
  | .set _ | .record _ | .call _ _ | .temporal _ | .provider _ => by
    intro g hg; simp [Expr.facts] at hg

variable {T P} in
mutual

/-- **Each temporal leaf of a put-back expression is a temporal read of the crate's**, at a
position whose facts the crate computes, outside reserved heads, among the specification's. -/
theorem leafFacts_putBack_temporal (hT : ∀ a ∈ T.map Prod.fst, isHoistedName a = true) :
    ∀ (x : Expr) (F₀ G₀ : List Guard), x.leaves = [] → NrSub G₀ F₀ →
      ∀ φ F, (.inl φ, F) ∈ (putBack T P x).leafFacts F₀ →
      ∃ a G, (T.map Prod.fst).contains a = true ∧ (T.lookup a).getD default = φ ∧
        (a, G) ∈ leafFactsW ((T.map Prod.fst).contains ·) G₀ x ∧ NrSub G F
  | .getAttr e a, F₀, G₀, hl, hG, φ, F, hm => by
    simp only [Expr.leaves] at hl
    rw [putBack_getAttr] at hm
    split at hm
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      have he := eq_of_isContext hc.1
      subst he
      simp only [Expr.leafFacts, List.mem_singleton, Prod.mk.injEq, Sum.inl.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact ⟨a, G₀, hc.2, rfl, by simp only [leafFactsW, hc.2, if_true, List.mem_singleton], hG⟩
    · split at hm
      · simp [Expr.leafFacts] at hm
      · simp only [Expr.leafFacts] at hm
        obtain ⟨a', G, h₁, h₂, h₃, h₄⟩ := leafFacts_putBack_temporal hT e F₀ G₀ hl hG φ F hm
        refine ⟨a', G, h₁, h₂, ?_, h₄⟩
        cases e with
        | var v =>
          cases v <;> simp [putBack, Expr.leafFacts] at hm
        | _ => simp only [leafFactsW]; exact h₃
  | .lit _, _, _, _, _, _, _, hm | .var _, _, _, _, _, _, _, hm => by
    simp [putBack, Expr.leafFacts] at hm
  | .temporal _, _, _, hl, _, _, _, _ | .provider _, _, _, hl, _, _, _, _ => by
    simp [Expr.leaves] at hl
  | .ite c t e, F₀, G₀, hl, hG, φ, F, hm => by
    simp only [Expr.leaves, List.append_eq_nil_iff] at hl
    simp only [putBack, Expr.leafFacts, List.mem_append] at hm
    rcases hm with (hm | hm) | hm
    · obtain ⟨a, G, h₁, h₂, h₃, h₄⟩ := leafFacts_putBack_temporal hT c F₀ G₀ hl.1.1 hG φ F hm
      exact ⟨a, G, h₁, h₂, by simp only [leafFactsW, List.mem_append]; exact Or.inl (Or.inl h₃), h₄⟩
    · obtain ⟨a, G, h₁, h₂, h₃, h₄⟩ := leafFacts_putBack_temporal hT t _ _ hl.1.2
        (NrSub.append hG (facts_putBack hT c)) φ F hm
      exact ⟨a, G, h₁, h₂, by simp only [leafFactsW, List.mem_append]; exact Or.inl (Or.inr h₃), h₄⟩
    · obtain ⟨a, G, h₁, h₂, h₃, h₄⟩ := leafFacts_putBack_temporal hT e F₀ G₀ hl.2 hG φ F hm
      exact ⟨a, G, h₁, h₂, by simp only [leafFactsW, List.mem_append]; exact Or.inr h₃, h₄⟩
  | .and a b, F₀, G₀, hl, hG, φ, F, hm => by
    simp only [Expr.leaves, List.append_eq_nil_iff] at hl
    simp only [putBack, Expr.leafFacts, List.mem_append] at hm
    rcases hm with hm | hm
    · obtain ⟨i, G, h₁, h₂, h₃, h₄⟩ := leafFacts_putBack_temporal hT a F₀ G₀ hl.1 hG φ F hm
      exact ⟨i, G, h₁, h₂, by simp only [leafFactsW, List.mem_append]; exact Or.inl h₃, h₄⟩
    · obtain ⟨i, G, h₁, h₂, h₃, h₄⟩ := leafFacts_putBack_temporal hT b _ _ hl.2
        (NrSub.append hG (facts_putBack hT a)) φ F hm
      exact ⟨i, G, h₁, h₂, by simp only [leafFactsW, List.mem_append]; exact Or.inr h₃, h₄⟩
  | .or a b, F₀, G₀, hl, hG, φ, F, hm => by
    simp only [Expr.leaves, List.append_eq_nil_iff] at hl
    simp only [putBack, Expr.leafFacts, List.mem_append] at hm
    rcases hm with hm | hm
    · obtain ⟨i, G, h₁, h₂, h₃, h₄⟩ := leafFacts_putBack_temporal hT a F₀ G₀ hl.1 hG φ F hm
      exact ⟨i, G, h₁, h₂, by simp only [leafFactsW, List.mem_append]; exact Or.inl h₃, h₄⟩
    · obtain ⟨i, G, h₁, h₂, h₃, h₄⟩ := leafFacts_putBack_temporal hT b F₀ G₀ hl.2 hG φ F hm
      exact ⟨i, G, h₁, h₂, by simp only [leafFactsW, List.mem_append]; exact Or.inr h₃, h₄⟩
  | .binaryApp _ a b, F₀, G₀, hl, hG, φ, F, hm => by
    simp only [Expr.leaves, List.append_eq_nil_iff] at hl
    simp only [putBack, Expr.leafFacts, List.mem_append] at hm
    rcases hm with hm | hm
    · obtain ⟨i, G, h₁, h₂, h₃, h₄⟩ := leafFacts_putBack_temporal hT a F₀ G₀ hl.1 hG φ F hm
      exact ⟨i, G, h₁, h₂, by simp only [leafFactsW, List.mem_append]; exact Or.inl h₃, h₄⟩
    · obtain ⟨i, G, h₁, h₂, h₃, h₄⟩ := leafFacts_putBack_temporal hT b F₀ G₀ hl.2 hG φ F hm
      exact ⟨i, G, h₁, h₂, by simp only [leafFactsW, List.mem_append]; exact Or.inr h₃, h₄⟩
  | .unaryApp _ a, F₀, G₀, hl, hG, φ, F, hm | .hasAttr a _, F₀, G₀, hl, hG, φ, F, hm
  | .extHasAttr a _ _, F₀, G₀, hl, hG, φ, F, hm => by
    simp only [Expr.leaves] at hl
    simp only [putBack, Expr.leafFacts] at hm
    obtain ⟨i, G, h₁, h₂, h₃, h₄⟩ := leafFacts_putBack_temporal hT a F₀ G₀ hl hG φ F hm
    exact ⟨i, G, h₁, h₂, by simp only [leafFactsW]; exact h₃, h₄⟩
  | .set xs, F₀, G₀, hl, hG, φ, F, hm | .call _ xs, F₀, G₀, hl, hG, φ, F, hm => by
    simp only [Expr.leaves] at hl
    simp only [putBack, Expr.leafFacts] at hm
    obtain ⟨i, G, h₁, h₂, h₃, h₄⟩ := leafFactsList_putBack_temporal hT xs F₀ G₀ hl hG φ F hm
    exact ⟨i, G, h₁, h₂, by simp only [leafFactsW]; exact h₃, h₄⟩
  | .record axs, F₀, G₀, hl, hG, φ, F, hm => by
    simp only [Expr.leaves] at hl
    simp only [putBack, Expr.leafFacts] at hm
    obtain ⟨i, G, h₁, h₂, h₃, h₄⟩ := leafFactsRecord_putBack_temporal hT axs F₀ G₀ hl hG φ F hm
    exact ⟨i, G, h₁, h₂, by simp only [leafFactsW]; exact h₃, h₄⟩

theorem leafFactsList_putBack_temporal (hT : ∀ a ∈ T.map Prod.fst, isHoistedName a = true) :
    ∀ (xs : List Expr) (F₀ G₀ : List Guard), Expr.leavesList xs = [] → NrSub G₀ F₀ →
      ∀ φ F, (.inl φ, F) ∈ Expr.leafFactsList F₀ (putBackList T P xs) →
      ∃ a G, (T.map Prod.fst).contains a = true ∧ (T.lookup a).getD default = φ ∧
        (a, G) ∈ leafFactsWList ((T.map Prod.fst).contains ·) G₀ xs ∧ NrSub G F
  | [], _, _, _, _, _, _, hm => by simp [putBackList, Expr.leafFactsList] at hm
  | x :: xs, F₀, G₀, hl, hG, φ, F, hm => by
    simp only [Expr.leavesList, List.append_eq_nil_iff] at hl
    simp only [putBackList, Expr.leafFactsList, List.mem_append] at hm
    rcases hm with hm | hm
    · obtain ⟨i, G, h₁, h₂, h₃, h₄⟩ := leafFacts_putBack_temporal hT x F₀ G₀ hl.1 hG φ F hm
      exact ⟨i, G, h₁, h₂, by simp only [leafFactsWList, List.mem_append]; exact Or.inl h₃, h₄⟩
    · obtain ⟨i, G, h₁, h₂, h₃, h₄⟩ := leafFactsList_putBack_temporal hT xs F₀ G₀ hl.2 hG φ F hm
      exact ⟨i, G, h₁, h₂, by simp only [leafFactsWList, List.mem_append]; exact Or.inr h₃, h₄⟩

theorem leafFactsRecord_putBack_temporal (hT : ∀ a ∈ T.map Prod.fst, isHoistedName a = true) :
    ∀ (axs : List (String × Expr)) (F₀ G₀ : List Guard), Expr.leavesRecord axs = [] → NrSub G₀ F₀ →
      ∀ φ F, (.inl φ, F) ∈ Expr.leafFactsRecord F₀ (putBackRecord T P axs) →
      ∃ a G, (T.map Prod.fst).contains a = true ∧ (T.lookup a).getD default = φ ∧
        (a, G) ∈ leafFactsWRecord ((T.map Prod.fst).contains ·) G₀ axs ∧ NrSub G F
  | [], _, _, _, _, _, _, hm => by simp [putBackRecord, Expr.leafFactsRecord] at hm
  | (_, x) :: axs, F₀, G₀, hl, hG, φ, F, hm => by
    simp only [Expr.leavesRecord, List.append_eq_nil_iff] at hl
    simp only [putBackRecord, Expr.leafFactsRecord, List.mem_append] at hm
    rcases hm with hm | hm
    · obtain ⟨i, G, h₁, h₂, h₃, h₄⟩ := leafFacts_putBack_temporal hT x F₀ G₀ hl.1 hG φ F hm
      exact ⟨i, G, h₁, h₂, by simp only [leafFactsWRecord, List.mem_append]; exact Or.inl h₃, h₄⟩
    · obtain ⟨i, G, h₁, h₂, h₃, h₄⟩ := leafFactsRecord_putBack_temporal hT axs F₀ G₀ hl.2 hG φ F hm
      exact ⟨i, G, h₁, h₂, by simp only [leafFactsWRecord, List.mem_append]; exact Or.inr h₃, h₄⟩

end

/-! ## Scopes read nothing -/

variable {T : List (String × Formula)} {P : List (String × Dogwood.Spec.Provider.Call)}

mutual

/-- An expression with no attribute access, `has` test, or leaf: a scope constraint. -/
def plain : Expr → Bool
  | .lit _ | .var _ => true
  | .ite a b c => plain a && plain b && plain c
  | .and a b | .or a b | .binaryApp _ a b => plain a && plain b
  | .unaryApp _ a => plain a
  | .set xs | .call _ xs => plainList xs
  | .record axs => plainRecord axs
  | .getAttr _ _ | .hasAttr _ _ | .extHasAttr _ _ _ | .temporal _ | .provider _ => false

def plainList : List Expr → Bool
  | [] => true
  | x :: xs => plain x && plainList xs

def plainRecord : List (String × Expr) → Bool
  | [] => true
  | (_, x) :: axs => plain x && plainRecord axs

end

mutual

theorem putBack_plain : (x : Expr) → plain x = true → putBack T P x = x
  | .lit _, _ | .var _, _ => rfl
  | .ite a b c, h => by
    simp only [plain, Bool.and_eq_true] at h
    simp only [putBack, putBack_plain a h.1.1, putBack_plain b h.1.2, putBack_plain c h.2]
  | .and a b, h | .or a b, h | .binaryApp _ a b, h => by
    simp only [plain, Bool.and_eq_true] at h
    simp only [putBack, putBack_plain a h.1, putBack_plain b h.2]
  | .unaryApp _ a, h => by
    simp only [plain] at h
    simp only [putBack, putBack_plain a h]
  | .set xs, h | .call _ xs, h => by
    simp only [plain] at h
    simp only [putBack, putBackList_plain xs h]
  | .record axs, h => by
    simp only [plain] at h
    simp only [putBack, putBackRecord_plain axs h]
  | .getAttr _ _, h | .hasAttr _ _, h | .extHasAttr _ _ _, h | .temporal _, h | .provider _, h => by
    simp [plain] at h

theorem putBackList_plain : (xs : List Expr) → plainList xs = true → putBackList T P xs = xs
  | [], _ => rfl
  | x :: xs, h => by
    simp only [plainList, Bool.and_eq_true] at h
    simp only [putBackList, putBack_plain x h.1, putBackList_plain xs h.2]

theorem putBackRecord_plain : (axs : List (String × Expr)) → plainRecord axs = true →
    putBackRecord T P axs = axs
  | [], _ => rfl
  | (_, x) :: axs, h => by
    simp only [plainRecord, Bool.and_eq_true] at h
    simp only [putBackRecord, putBack_plain x h.1, putBackRecord_plain axs h.2]

end

mutual

theorem hoistedReads_plain (tids pids : List String) : (x : Expr) → plain x = true →
    hoistedReads tids pids x = []
  | .lit _, _ | .var _, _ => rfl
  | .ite a b c, h => by
    simp only [plain, Bool.and_eq_true] at h
    simp only [hoistedReads, hoistedReads_plain tids pids a h.1.1, hoistedReads_plain tids pids b h.1.2,
      hoistedReads_plain tids pids c h.2, List.append_nil]
  | .and a b, h | .or a b, h | .binaryApp _ a b, h => by
    simp only [plain, Bool.and_eq_true] at h
    simp only [hoistedReads, hoistedReads_plain tids pids a h.1, hoistedReads_plain tids pids b h.2,
      List.append_nil]
  | .unaryApp _ a, h => by
    simp only [plain] at h
    simp only [hoistedReads, hoistedReads_plain tids pids a h]
  | .set xs, h | .call _ xs, h => by
    simp only [plain] at h
    simp only [hoistedReads, hoistedReadsList_plain tids pids xs h]
  | .record axs, h => by
    simp only [plain] at h
    simp only [hoistedReads, hoistedReadsRecord_plain tids pids axs h]
  | .getAttr _ _, h | .hasAttr _ _, h | .extHasAttr _ _ _, h | .temporal _, h | .provider _, h => by
    simp [plain] at h

theorem hoistedReadsList_plain (tids pids : List String) : (xs : List Expr) → plainList xs = true →
    hoistedReadsList tids pids xs = []
  | [], _ => rfl
  | x :: xs, h => by
    simp only [plainList, Bool.and_eq_true] at h
    simp only [hoistedReadsList, hoistedReads_plain tids pids x h.1,
      hoistedReadsList_plain tids pids xs h.2, List.append_nil]

theorem hoistedReadsRecord_plain (tids pids : List String) : (axs : List (String × Expr)) →
    plainRecord axs = true → hoistedReadsRecord tids pids axs = []
  | [], _ => rfl
  | (_, x) :: axs, h => by
    simp only [plainRecord, Bool.and_eq_true] at h
    simp only [hoistedReadsRecord, hoistedReads_plain tids pids x h.1,
      hoistedReadsRecord_plain tids pids axs h.2, List.append_nil]

end

mutual

theorem leafFactsW_plain (isLeaf : String → Bool) (G : List Guard) : (x : Expr) → plain x = true →
    leafFactsW isLeaf G x = []
  | .lit _, _ | .var _, _ => rfl
  | .ite a b c, h => by
    simp only [plain, Bool.and_eq_true] at h
    simp only [leafFactsW, leafFactsW_plain isLeaf _ a h.1.1, leafFactsW_plain isLeaf _ b h.1.2,
      leafFactsW_plain isLeaf _ c h.2, List.append_nil]
  | .and a b, h => by
    simp only [plain, Bool.and_eq_true] at h
    simp only [leafFactsW, leafFactsW_plain isLeaf _ a h.1, leafFactsW_plain isLeaf _ b h.2,
      List.append_nil]
  | .or a b, h | .binaryApp _ a b, h => by
    simp only [plain, Bool.and_eq_true] at h
    simp only [leafFactsW, leafFactsW_plain isLeaf _ a h.1, leafFactsW_plain isLeaf _ b h.2,
      List.append_nil]
  | .unaryApp _ a, h => by
    simp only [plain] at h
    simp only [leafFactsW, leafFactsW_plain isLeaf _ a h]
  | .set xs, h | .call _ xs, h => by
    simp only [plain] at h
    simp only [leafFactsW, leafFactsWList_plain isLeaf G xs h]
  | .record axs, h => by
    simp only [plain] at h
    simp only [leafFactsW, leafFactsWRecord_plain isLeaf G axs h]
  | .getAttr _ _, h | .hasAttr _ _, h | .extHasAttr _ _ _, h | .temporal _, h | .provider _, h => by
    simp [plain] at h

theorem leafFactsWList_plain (isLeaf : String → Bool) (G : List Guard) : (xs : List Expr) →
    plainList xs = true → leafFactsWList isLeaf G xs = []
  | [], _ => rfl
  | x :: xs, h => by
    simp only [plainList, Bool.and_eq_true] at h
    simp only [leafFactsWList, leafFactsW_plain isLeaf G x h.1, leafFactsWList_plain isLeaf G xs h.2,
      List.append_nil]

theorem leafFactsWRecord_plain (isLeaf : String → Bool) (G : List Guard) :
    (axs : List (String × Expr)) → plainRecord axs = true → leafFactsWRecord isLeaf G axs = []
  | [], _ => rfl
  | (_, x) :: axs, h => by
    simp only [plainRecord, Bool.and_eq_true] at h
    simp only [leafFactsWRecord, leafFactsW_plain isLeaf G x h.1,
      leafFactsWRecord_plain isLeaf G axs h.2, List.append_nil]

end

theorem facts_plain : (x : Expr) → plain x = true → x.facts = []
  | .and a b, h => by
    simp only [plain, Bool.and_eq_true] at h
    simp [Expr.facts, facts_plain a h.1, facts_plain b h.2]
  | .hasAttr _ _, h | .extHasAttr _ _ _, h => by simp [plain] at h
  | .lit _, _ | .var _, _ | .ite _ _ _, _ | .or _ _, _ | .binaryApp _ _ _, _ | .unaryApp _ _, _
  | .set _, _ | .call _ _, _ | .record _, _ | .getAttr _ _, _ | .temporal _, _ | .provider _, _ => by
    simp [Expr.facts]

theorem plain_scope (s : Cedar.Spec.Scope) (v : Cedar.Spec.Var) : plain (Expr.ofCedar (s.toExpr v)) = true := by
  cases s <;> simp [Cedar.Spec.Scope.toExpr, Cedar.Spec.Var.eqEntityUID, Cedar.Spec.Var.inEntityUID,
    Cedar.Spec.Var.isEntityType, Expr.ofCedar, plain]

theorem plainList_lits (es : List Cedar.Spec.EntityUID) :
    plainList (Expr.ofCedarList (es.map fun e => .lit (.entityUID e))) = true := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.map_cons, Expr.ofCedarList, plainList, ih, Bool.and_true]; rfl

theorem plain_principal (ps : Cedar.Spec.PrincipalScope) : plain (Expr.ofCedar ps.toExpr) = true := by
  cases ps; exact plain_scope _ _

theorem plain_resource (rs : Cedar.Spec.ResourceScope) : plain (Expr.ofCedar rs.toExpr) = true := by
  cases rs; exact plain_scope _ _

theorem plain_action (as : Cedar.Spec.ActionScope) : plain (Expr.ofCedar as.toExpr) = true := by
  cases as with
  | actionScope s => exact plain_scope _ _
  | actionInAny es =>
    simp only [Cedar.Spec.ActionScope.toExpr, Expr.ofCedar, plain, plainList_lits es, Bool.and_true]

/-! ## A put-back rule, as one expression -/

theorem condition_putBack (c : Dogwood.Spec.Condition) :
    ({ c with body := putBack T P c.body } : Dogwood.Spec.Condition).toExpr = putBack T P c.toExpr := by
  obtain ⟨kind, body⟩ := c
  cases kind <;> rfl

theorem conditions_putBack : (cs : Dogwood.Spec.Conditions) →
    Dogwood.Spec.Conditions.toExpr (cs.map fun c => { c with body := putBack T P c.body }) =
      putBack T P (Dogwood.Spec.Conditions.toExpr cs)
  | [] => rfl
  | [c] => by
    show ({ c with body := putBack T P c.body } : Dogwood.Spec.Condition).toExpr = putBack T P c.toExpr
    exact condition_putBack c
  | c :: d :: cs => by
    rw [List.map_cons, Dogwood.Thm.conditions_toExpr_cons _ _ (by simp), Dogwood.Thm.conditions_toExpr_cons _ _ (by simp),
      condition_putBack, conditions_putBack (d :: cs)]
    rfl

/-- **A put-back rule is the put-back of the rule**, as one expression: its scope reads nothing. -/
theorem putBackPolicy_toExpr (q : Dogwood.Spec.Policy) :
    (putBackPolicy T P q).toExpr = putBack T P q.toExpr := by
  simp only [putBackPolicy, Dogwood.Spec.Policy.toExpr, putBack,
    putBack_plain _ (plain_principal _), putBack_plain _ (plain_action _),
    putBack_plain _ (plain_resource _), conditions_putBack]

theorem hoistedReads_policy (tids pids : List String) (q : Dogwood.Spec.Policy) :
    hoistedReads tids pids q.toExpr =
      hoistedReads tids pids (Dogwood.Spec.Conditions.toExpr q.condition) := by
  simp only [Dogwood.Spec.Policy.toExpr, hoistedReads,
    hoistedReads_plain tids pids _ (plain_principal _), hoistedReads_plain tids pids _ (plain_action _),
    hoistedReads_plain tids pids _ (plain_resource _), List.nil_append]

theorem leafFactsW_policy (isLeaf : String → Bool) (q : Dogwood.Spec.Policy) :
    leafFactsW isLeaf [] q.toExpr = leafFactsW isLeaf [] (Dogwood.Spec.Conditions.toExpr q.condition) := by
  simp only [Dogwood.Spec.Policy.toExpr, leafFactsW,
    leafFactsW_plain isLeaf _ _ (plain_principal _), leafFactsW_plain isLeaf _ _ (plain_action _),
    leafFactsW_plain isLeaf _ _ (plain_resource _), facts_plain _ (plain_principal _),
    facts_plain _ (plain_action _), facts_plain _ (plain_resource _), List.nil_append, List.append_nil]

/-! ## The lowering of a put-back rule is the crate's, renamed -/

mutual

/-- An expression without leaves is a Cedar expression. -/
theorem eq_ofCedar_lowerFrom : (x : Expr) → x.leaves = [] → x = Expr.ofCedar (x.lowerFrom 0).1
  | .lit _, _ | .var _, _ => rfl
  | .temporal _, h | .provider _, h => by simp [Expr.leaves] at h
  | .ite a b c, h => by
    simp only [Expr.leaves, List.append_eq_nil_iff] at h
    have ha := eq_ofCedar_lowerFrom a h.1.1
    have hb := eq_ofCedar_lowerFrom b h.1.2
    have hc := eq_ofCedar_lowerFrom c h.2
    rw [ha] at ⊢; rw [hb, hc]
    simp only [Expr.lowerFrom, Dogwood.Thm.lowerFrom_ofCedar, Expr.ofCedar]
  | .and a b, h => by
    simp only [Expr.leaves, List.append_eq_nil_iff] at h
    rw [eq_ofCedar_lowerFrom a h.1, eq_ofCedar_lowerFrom b h.2]
    simp only [Expr.lowerFrom, Dogwood.Thm.lowerFrom_ofCedar, Expr.ofCedar]
  | .or a b, h => by
    simp only [Expr.leaves, List.append_eq_nil_iff] at h
    rw [eq_ofCedar_lowerFrom a h.1, eq_ofCedar_lowerFrom b h.2]
    simp only [Expr.lowerFrom, Dogwood.Thm.lowerFrom_ofCedar, Expr.ofCedar]
  | .binaryApp _ a b, h => by
    simp only [Expr.leaves, List.append_eq_nil_iff] at h
    rw [eq_ofCedar_lowerFrom a h.1, eq_ofCedar_lowerFrom b h.2]
    simp only [Expr.lowerFrom, Dogwood.Thm.lowerFrom_ofCedar, Expr.ofCedar]
  | .unaryApp _ a, h => by
    simp only [Expr.leaves] at h
    rw [eq_ofCedar_lowerFrom a h]
    simp only [Expr.lowerFrom, Dogwood.Thm.lowerFrom_ofCedar, Expr.ofCedar]
  | .getAttr a _, h => by
    simp only [Expr.leaves] at h
    rw [eq_ofCedar_lowerFrom a h]
    simp only [Expr.lowerFrom, Dogwood.Thm.lowerFrom_ofCedar, Expr.ofCedar]
  | .hasAttr a _, h => by
    simp only [Expr.leaves] at h
    rw [eq_ofCedar_lowerFrom a h]
    simp only [Expr.lowerFrom, Dogwood.Thm.lowerFrom_ofCedar, Expr.ofCedar]
  | .extHasAttr a _ _, h => by
    simp only [Expr.leaves] at h
    rw [eq_ofCedar_lowerFrom a h]
    simp only [Expr.lowerFrom, Dogwood.Thm.lowerFrom_ofCedar, Expr.ofCedar]
  | .set xs, h => by
    simp only [Expr.leaves] at h
    rw [eq_ofCedarList_lowerFrom xs h]
    simp only [Expr.lowerFrom, Dogwood.Thm.lowerListFrom_ofCedar, Expr.ofCedar]
  | .call _ xs, h => by
    simp only [Expr.leaves] at h
    rw [eq_ofCedarList_lowerFrom xs h]
    simp only [Expr.lowerFrom, Dogwood.Thm.lowerListFrom_ofCedar, Expr.ofCedar]
  | .record axs, h => by
    simp only [Expr.leaves] at h
    rw [eq_ofCedarRecord_lowerFrom axs h]
    simp only [Expr.lowerFrom, Dogwood.Thm.lowerRecordFrom_ofCedar, Expr.ofCedar]

theorem eq_ofCedarList_lowerFrom : (xs : List Expr) → Expr.leavesList xs = [] →
    xs = Expr.ofCedarList (Expr.lowerListFrom 0 xs).1
  | [], _ => rfl
  | x :: xs, h => by
    simp only [Expr.leavesList, List.append_eq_nil_iff] at h
    rw [eq_ofCedar_lowerFrom x h.1, eq_ofCedarList_lowerFrom xs h.2]
    simp only [Expr.lowerListFrom, Dogwood.Thm.lowerFrom_ofCedar, Dogwood.Thm.lowerListFrom_ofCedar,
      Expr.ofCedarList]

theorem eq_ofCedarRecord_lowerFrom : (axs : List (String × Expr)) → Expr.leavesRecord axs = [] →
    axs = Expr.ofCedarRecord (Expr.lowerRecordFrom 0 axs).1
  | [], _ => rfl
  | (a, x) :: axs, h => by
    simp only [Expr.leavesRecord, List.append_eq_nil_iff] at h
    rw [eq_ofCedar_lowerFrom x h.1, eq_ofCedarRecord_lowerFrom axs h.2]
    simp only [Expr.lowerRecordFrom, Dogwood.Thm.lowerFrom_ofCedar, Dogwood.Thm.lowerRecordFrom_ofCedar,
      Expr.ofCedarRecord]

end

theorem isContext_ofCedar (e : Cedar.Spec.Expr) : isContext (Expr.ofCedar e) = isContextC e := by
  cases e with
  | var v => cases v <;> rfl
  | _ => rfl

theorem isContextProviders_ofCedar (e : Cedar.Spec.Expr) :
    isContextProviders (Expr.ofCedar e) = isContextProvidersC e := by
  cases e with
  | getAttr e' a =>
    cases e' with
    | var v =>
      cases v <;> simp only [Expr.ofCedar, isContextProviders, isContextProvidersC]
      by_cases ha : a = "providers"
      · subst ha; rfl
      · simp [ha]
    | _ => rfl
  | _ => rfl

theorem reads_shift {ren : Bool → String → Cedar.Spec.Attr} {k : Nat}
    {r₁ r₂ : List (Bool × String)} (h : ∀ i x, (r₁ ++ r₂)[i]? = some x → ren x.1 x.2 = leafAttr (k + i)) :
    (∀ i x, r₁[i]? = some x → ren x.1 x.2 = leafAttr (k + i)) ∧
      (∀ i x, r₂[i]? = some x → ren x.1 x.2 = leafAttr (k + r₁.length + i)) := by
  refine ⟨fun i x hx => h i x ?_, fun i x hx => ?_⟩
  · have hi : i < r₁.length := by
      rcases Nat.lt_or_ge i r₁.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at hx; cases hx
    rw [List.getElem?_append_left hi]; exact hx
  · have := h (r₁.length + i) x (by rw [List.getElem?_append_right (by omega)]; simpa using hx)
    rw [← Nat.add_assoc] at this
    exact this

mutual

/-- **The specification's lowering of a put-back Cedar expression is the expression with its
hoisted reads renamed**, when the reads, in order, are named from the leaf index `k` on. -/
theorem lowerFrom_putBack (ren : Bool → String → Cedar.Spec.Attr) :
    (y : Cedar.Spec.Expr) → (k : Nat) →
    (∀ i r, (hoistedReads (T.map Prod.fst) (P.map Prod.fst) (Expr.ofCedar y))[i]? = some r →
      ren r.1 r.2 = leafAttr (k + i)) →
    ((putBack T P (Expr.ofCedar y)).lowerFrom k).1 =
      renameHoisted (T.map Prod.fst) (P.map Prod.fst) ren y
  | .getAttr e a, k, h => by
    have hr := h
    simp only [Expr.ofCedar] at hr ⊢
    rw [putBack_getAttr]
    simp only [hoistedReads, isContext_ofCedar, isContextProviders_ofCedar] at hr
    simp only [renameHoisted, isContext_ofCedar, isContextProviders_ofCedar]
    split
    · rename_i hc
      rw [if_pos hc] at hr
      simp only [Expr.lowerFrom]
      rw [h0 (hr 0 (true, a) rfl)]
    · rename_i hc
      rw [if_neg hc] at hr
      split
      · rename_i hp
        rw [if_pos hp] at hr
        simp only [Expr.lowerFrom]
        rw [h0 (hr 0 (false, a) rfl)]
      · rename_i hp
        rw [if_neg hp] at hr
        simp only [Expr.lowerFrom]
        rw [lowerFrom_putBack ren e k hr]
  | .lit _, _, _ | .var _, _, _ => rfl
  | .ite c t e, k, h => by
    simp only [Expr.ofCedar, hoistedReads] at h
    obtain ⟨h₁₂, h₃⟩ := reads_shift h
    obtain ⟨h₁, h₂⟩ := reads_shift h₁₂
    simp only [Expr.ofCedar, putBack, Expr.lowerFrom, renameHoisted]
    rw [lowerFrom_putBack ren c k h₁, Dogwood.Thm.lowerFrom_snd,
      leaves_putBack _ _ _ (leaves_ofCedar c), List.length_map, lowerFrom_putBack ren t _ h₂,
      Dogwood.Thm.lowerFrom_snd, leaves_putBack _ _ _ (leaves_ofCedar t), List.length_map,
      lowerFrom_putBack ren e _ (by intro i r hr; have := h₃ i r hr; simpa [Nat.add_assoc] using this)]
  | .and a b, k, h => by
    simp only [Expr.ofCedar, hoistedReads] at h
    obtain ⟨h₁, h₂⟩ := reads_shift h
    simp only [Expr.ofCedar, putBack, Expr.lowerFrom, renameHoisted]
    rw [lowerFrom_putBack ren a k h₁, Dogwood.Thm.lowerFrom_snd,
      leaves_putBack _ _ _ (leaves_ofCedar a), List.length_map, lowerFrom_putBack ren b _ h₂]
  | .or a b, k, h => by
    simp only [Expr.ofCedar, hoistedReads] at h
    obtain ⟨h₁, h₂⟩ := reads_shift h
    simp only [Expr.ofCedar, putBack, Expr.lowerFrom, renameHoisted]
    rw [lowerFrom_putBack ren a k h₁, Dogwood.Thm.lowerFrom_snd,
      leaves_putBack _ _ _ (leaves_ofCedar a), List.length_map, lowerFrom_putBack ren b _ h₂]
  | .binaryApp _ a b, k, h => by
    simp only [Expr.ofCedar, hoistedReads] at h
    obtain ⟨h₁, h₂⟩ := reads_shift h
    simp only [Expr.ofCedar, putBack, Expr.lowerFrom, renameHoisted]
    rw [lowerFrom_putBack ren a k h₁, Dogwood.Thm.lowerFrom_snd,
      leaves_putBack _ _ _ (leaves_ofCedar a), List.length_map, lowerFrom_putBack ren b _ h₂]
  | .unaryApp _ a, k, h => by
    simp only [Expr.ofCedar, hoistedReads] at h
    simp only [Expr.ofCedar, putBack, Expr.lowerFrom, renameHoisted, lowerFrom_putBack ren a k h]
  | .hasAttr a _, k, h => by
    simp only [Expr.ofCedar, hoistedReads] at h
    simp only [Expr.ofCedar, putBack, Expr.lowerFrom, renameHoisted, lowerFrom_putBack ren a k h]
  | .extHasAttr a _ _, k, h => by
    simp only [Expr.ofCedar, hoistedReads] at h
    simp only [Expr.ofCedar, putBack, Expr.lowerFrom, renameHoisted, lowerFrom_putBack ren a k h]
  | .set xs, k, h => by
    simp only [Expr.ofCedar, hoistedReads] at h
    simp only [Expr.ofCedar, putBack, Expr.lowerFrom, renameHoisted, lowerListFrom_putBack ren xs k h]
  | .call _ xs, k, h => by
    simp only [Expr.ofCedar, hoistedReads] at h
    simp only [Expr.ofCedar, putBack, Expr.lowerFrom, renameHoisted, lowerListFrom_putBack ren xs k h]
  | .record axs, k, h => by
    simp only [Expr.ofCedar, hoistedReads] at h
    simp only [Expr.ofCedar, putBack, Expr.lowerFrom, renameHoisted,
      lowerRecordFrom_putBack ren axs k h]
where
  h0 {x : Cedar.Spec.Attr} {k : Nat} (hx : x = leafAttr (k + 0)) : leafAttr k = x := by simp [hx]

theorem lowerListFrom_putBack (ren : Bool → String → Cedar.Spec.Attr) :
    (ys : List Cedar.Spec.Expr) → (k : Nat) →
    (∀ i r, (hoistedReadsList (T.map Prod.fst) (P.map Prod.fst) (Expr.ofCedarList ys))[i]? = some r →
      ren r.1 r.2 = leafAttr (k + i)) →
    (Expr.lowerListFrom k (putBackList T P (Expr.ofCedarList ys))).1 =
      renameHoistedList (T.map Prod.fst) (P.map Prod.fst) ren ys
  | [], _, _ => rfl
  | y :: ys, k, h => by
    simp only [Expr.ofCedarList, hoistedReadsList] at h
    obtain ⟨h₁, h₂⟩ := reads_shift h
    simp only [Expr.ofCedarList, putBackList, Expr.lowerListFrom, renameHoistedList]
    rw [lowerFrom_putBack ren y k h₁, Dogwood.Thm.lowerFrom_snd,
      leaves_putBack _ _ _ (leaves_ofCedar y), List.length_map, lowerListFrom_putBack ren ys _ h₂]

theorem lowerRecordFrom_putBack (ren : Bool → String → Cedar.Spec.Attr) :
    (ays : List (Cedar.Spec.Attr × Cedar.Spec.Expr)) → (k : Nat) →
    (∀ i r, (hoistedReadsRecord (T.map Prod.fst) (P.map Prod.fst) (Expr.ofCedarRecord ays))[i]? =
      some r → ren r.1 r.2 = leafAttr (k + i)) →
    (Expr.lowerRecordFrom k (putBackRecord T P (Expr.ofCedarRecord ays))).1 =
      renameHoistedRecord (T.map Prod.fst) (P.map Prod.fst) ren ays
  | [], _, _ => rfl
  | (a, y) :: ays, k, h => by
    simp only [Expr.ofCedarRecord, hoistedReadsRecord] at h
    obtain ⟨h₁, h₂⟩ := reads_shift h
    simp only [Expr.ofCedarRecord, putBackRecord, Expr.lowerRecordFrom, renameHoistedRecord]
    rw [lowerFrom_putBack ren y k h₁, Dogwood.Thm.lowerFrom_snd,
      leaves_putBack _ _ _ (leaves_ofCedar y), List.length_map, lowerRecordFrom_putBack ren ays _ h₂]

end

theorem conditions_cons_toExpr {α : Type} (f : Expr → List α)
    (hand : ∀ a b, f (.and a b) = f a ++ f b) (hnot : ∀ a, f (.unaryApp .not a) = f a) :
    (cs : Dogwood.Spec.Conditions) → cs ≠ [] →
      f (Dogwood.Spec.Conditions.toExpr cs) = cs.flatMap fun c => f c.body
  | [c], _ => by
    show f c.toExpr = [c].flatMap fun c => f c.body
    obtain ⟨kind, body⟩ := c
    cases kind <;> simp [Dogwood.Spec.Condition.toExpr, hnot]
  | c :: d :: cs, _ => by
    rw [Dogwood.Thm.conditions_toExpr_cons _ _ (by simp), hand,
      conditions_cons_toExpr f hand hnot (d :: cs) (by simp)]
    obtain ⟨kind, body⟩ := c
    cases kind <;> simp [Dogwood.Spec.Condition.toExpr, hnot]

theorem hoistedReads_conditions (tids pids : List String) (cs : Dogwood.Spec.Conditions) :
    hoistedReads tids pids (Dogwood.Spec.Conditions.toExpr cs) =
      cs.flatMap fun c => hoistedReads tids pids c.body := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    exact conditions_cons_toExpr (hoistedReads tids pids) (fun _ _ => rfl) (fun _ => rfl) _ (by simp)

theorem leaves_conditions (cs : Dogwood.Spec.Conditions) :
    (Dogwood.Spec.Conditions.toExpr cs).leaves = cs.flatMap fun c => c.body.leaves := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    exact conditions_cons_toExpr Expr.leaves (fun _ _ => rfl) (fun _ => rfl) _ (by simp)

theorem leaves_policy (q : Dogwood.Spec.Policy) :
    q.toExpr.leaves = q.condition.flatMap fun c => c.body.leaves := by
  simp only [Dogwood.Spec.Policy.toExpr, Expr.leaves, leaves_ofCedar, List.nil_append,
    leaves_conditions]

theorem conditions_lowerFrom_putBack (ren : Bool → String → Cedar.Spec.Attr) :
    (cs : Dogwood.Spec.Conditions) → (k : Nat) → (∀ c ∈ cs, c.body.leaves = []) →
    (∀ i r, (cs.flatMap fun c => hoistedReads (T.map Prod.fst) (P.map Prod.fst) c.body)[i]? = some r →
      ren r.1 r.2 = leafAttr (k + i)) →
    (Dogwood.Spec.Conditions.lowerFrom k (cs.map fun c => { c with body := putBack T P c.body })).1 =
      (Dogwood.Spec.Conditions.lowerFrom 0 cs).1.map fun c =>
        { c with body := renameHoisted (T.map Prod.fst) (P.map Prod.fst) ren c.body }
  | [], _, _, _ => rfl
  | c :: cs, k, hl, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨h₁, h₂⟩ := reads_shift h
    have hc := hl c (by simp)
    have hcs : ∀ c ∈ cs, c.body.leaves = [] := fun c' hc' => hl c' (by simp [hc'])
    have hb := eq_ofCedar_lowerFrom c.body hc
    simp only [List.map_cons, Dogwood.Spec.Conditions.lowerFrom, List.cons.injEq]
    have hsnd : (c.body.lowerFrom 0).2 = 0 := by rw [Dogwood.Thm.lowerFrom_snd, hc]; rfl
    rw [hsnd]
    refine ⟨?_, ?_⟩
    · rw [hb] at h₁ ⊢
      rw [lowerFrom_putBack ren _ k h₁, Dogwood.Thm.lowerFrom_ofCedar]
    · rw [Dogwood.Thm.lowerFrom_snd, leaves_putBack _ _ _ hc, List.length_map]
      exact conditions_lowerFrom_putBack ren cs _ hcs h₂

/-- The crate's lowered rule, as a Cedar policy, from its leafless form. -/
theorem policy_lowerFrom_putBack (ren : Bool → String → Cedar.Spec.Attr) (q : Dogwood.Spec.Policy)
    (k : Nat) (hl : q.toExpr.leaves = [])
    (h : ∀ i r, (hoistedReads (T.map Prod.fst) (P.map Prod.fst) q.toExpr)[i]? = some r →
      ren r.1 r.2 = leafAttr (k + i)) :
    ((putBackPolicy T P q).lowerFrom k).1 =
      renamePolicy (T.map Prod.fst) (P.map Prod.fst) ren (q.lowerFrom 0).1 := by
  rw [leaves_policy, List.flatMap_eq_nil_iff] at hl
  rw [hoistedReads_policy, hoistedReads_conditions] at h
  simp only [Dogwood.Spec.Policy.lowerFrom, putBackPolicy, renamePolicy,
    conditions_lowerFrom_putBack ren q.condition k hl h]

theorem policies_lowerFrom_putBack (ren : Bool → String → Cedar.Spec.Attr) :
    (ps : Dogwood.Spec.Policies) → (k : Nat) → (∀ q ∈ ps, q.toExpr.leaves = []) →
    (∀ i r, (ps.flatMap fun q => hoistedReads (T.map Prod.fst) (P.map Prod.fst) q.toExpr)[i]? = some r →
      ren r.1 r.2 = leafAttr (k + i)) →
    (Dogwood.Spec.Policies.lowerFrom k (ps.map (putBackPolicy T P))).1 =
      (Dogwood.Spec.Policies.lowerFrom 0 ps).1.map (renamePolicy (T.map Prod.fst) (P.map Prod.fst) ren)
  | [], _, _, _ => rfl
  | q :: ps, k, hl, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨h₁, h₂⟩ := reads_shift h
    have hq := hl q (by simp)
    have hps : ∀ q ∈ ps, q.toExpr.leaves = [] := fun q' hq' => hl q' (by simp [hq'])
    simp only [List.map_cons, Dogwood.Spec.Policies.lowerFrom, List.cons.injEq]
    have hsnd : (q.lowerFrom 0).2 = 0 := by rw [Dogwood.Thm.policy_lowerFrom_snd, hq]; rfl
    rw [hsnd]
    refine ⟨policy_lowerFrom_putBack ren q k hq h₁, ?_⟩
    rw [Dogwood.Thm.policy_lowerFrom_snd, putBackPolicy_toExpr, leaves_putBack _ _ _ hq, List.length_map]
    exact policies_lowerFrom_putBack ren ps _ hps h₂

/-! ## The crate's context reads -/

theorem isSpecLeafName_providers : isSpecLeafName "providers" = false := by decide

/-- `contextReads` on an attribute access, by cases. -/
theorem contextReads_getAttr (g : Generated) (e : Expr) (a : String) :
    contextReads g (.getAttr e a) =
      if isContextProviders e then (if g.providers.contains a then [] else [(false, "providers")])
      else if isContext e then (if isHoistedName a && !(g.temporal.contains a) then [(false, a)] else [])
      else contextReads g e := by
  cases e with
  | getAttr e' a' =>
    cases e' with
    | var v =>
      cases v
      case context =>
        by_cases h : a' = "providers"
        · subst h; simp [contextReads, isContextProviders]
        · simp [contextReads, isContextProviders, isContext, h]
      all_goals simp [contextReads, isContextProviders, isContext]
    | _ => simp [contextReads, isContextProviders, isContext]
  | var v => cases v <;> simp [contextReads, isContext, isContextProviders]
  | _ => simp [contextReads, isContext, isContextProviders]

theorem contextReads_hasAttr (g : Generated) (e : Expr) (a : String) :
    contextReads g (.hasAttr e a) =
      if isContext e then (if isHoistedName a then [(false, a)] else []) else contextReads g e := by
  by_cases hc : isContext e = true
  · have := eq_of_isContext hc
    subst this
    simp [contextReads, isContext]
  · rw [if_neg hc]
    cases e with
    | var v => cases v <;> simp_all [contextReads, isContext]
    | _ => rfl

theorem contextReads_extHasAttr (g : Generated) (e : Expr) (a : String) (as : List String) :
    contextReads g (.extHasAttr e a as) =
      if isContext e then (if isHoistedName a then [(false, a)] else []) else contextReads g e := by
  by_cases hc : isContext e = true
  · have := eq_of_isContext hc
    subst this
    simp [contextReads, isContext]
  · rw [if_neg hc]
    cases e with
    | var v => cases v <;> simp_all [contextReads, isContext]
    | _ => rfl

theorem contextAttrs_getAttr (e : Expr) (a : String) :
    contextAttrs (.getAttr e a) = if isContext e then [a] else contextAttrs e := by
  cases e with
  | var v => cases v <;> rfl
  | _ => rfl

theorem contextAttrs_hasAttr (e : Expr) (a : String) :
    contextAttrs (.hasAttr e a) = if isContext e then [a] else contextAttrs e := by
  cases e with
  | var v => cases v <;> rfl
  | _ => rfl

theorem contextAttrs_extHasAttr (e : Expr) (a : String) (as : List String) :
    contextAttrs (.extHasAttr e a as) = if isContext e then [a] else contextAttrs e := by
  cases e with
  | var v => cases v <;> rfl
  | _ => rfl

/-- The frontend's `isContext` is the specification's. -/
theorem isContext_eq_isContext (e : Expr) : e.isContext = isContext e := by
  cases e with
  | var v => cases v <;> rfl
  | _ => rfl

theorem isContext_putBack {e : Expr} (h : isContext e = false) : isContext (putBack T P e) = false := by
  cases e with
  | getAttr e' a =>
    rw [putBack_getAttr]; split
    · rfl
    · split <;> rfl
  | var v => cases v <;> simp_all [isContext, putBack]
  | _ => rfl

mutual

/-- **The crate's context-read check gives the specification's `ReadsContext`** on the put-back
rule, when no rule reads an attribute named like the specification's leaves and the names `R`
are named so. -/
theorem readsContext_putBack {R : List Cedar.Spec.Attr} (hR : ∀ a ∈ R, isSpecLeafName a = true)
    (htp : (T.map Prod.fst).contains "providers" = false) :
    (x : Expr) → contextReads ⟨T.map Prod.fst, P.map Prod.fst⟩ x = [] →
      (contextAttrs x).all (fun a => !isSpecLeafName a) = true →
      (putBack T P x).ReadsContext R
  | .getAttr e a, hr, ha => by
    rw [contextReads_getAttr] at hr
    rw [contextAttrs_getAttr] at ha
    rw [putBack_getAttr]
    split
    · trivial
    · split
      · trivial
      · rename_i hc hp
        show if (putBack T P e).isContext then a ∉ R else (putBack T P e).ReadsContext R
        by_cases hpe : isContextProviders e = true
        · rw [if_pos hpe] at hr
          have := eq_of_isContextProviders hpe
          subst this
          split at hr
          · rename_i hpa
            exfalso; apply hp; simp only [Bool.and_eq_true]; exact ⟨hpe, hpa⟩
          · cases hr
        · rw [if_neg hpe] at hr
          by_cases hce : isContext e = true
          · have := eq_of_isContext hce
            subst this
            simp only [isContext, if_true, List.all_cons, List.all_nil, Bool.and_true,
              Bool.not_eq_true'] at ha
            simp only [putBack, Expr.isContext, if_true]
            intro haR
            rw [hR a haR] at ha
            cases ha
          · rw [if_neg hce] at hr ha
            have hce' : isContext e = false := Bool.eq_false_iff.mpr hce
            have h1 := isContext_putBack (T := T) (P := P) hce'
            have h2 : (putBack T P e).isContext = false := by
              rw [isContext_eq_isContext]; exact h1
            rw [if_neg (by simp [h2])]
            exact readsContext_putBack hR htp e hr ha
  | .hasAttr e a, hr, ha => by
    rw [contextReads_hasAttr] at hr
    rw [contextAttrs_hasAttr] at ha
    show if (putBack T P e).isContext then a ∉ R else (putBack T P e).ReadsContext R
    by_cases hce : isContext e = true
    · have := eq_of_isContext hce
      subst this
      simp only [isContext, if_true, List.all_cons, List.all_nil, Bool.and_true,
        Bool.not_eq_true'] at ha
      simp only [putBack, Expr.isContext, if_true]
      intro haR
      rw [hR a haR] at ha
      cases ha
    · rw [if_neg hce] at hr ha
      have hce' : isContext e = false := Bool.eq_false_iff.mpr hce
      have h1 := isContext_putBack (T := T) (P := P) hce'
      have h2 : (putBack T P e).isContext = false := by rw [isContext_eq_isContext]; exact h1
      rw [if_neg (by simp [h2])]
      exact readsContext_putBack hR htp e hr ha
  | .extHasAttr e a as, hr, ha => by
    rw [contextReads_extHasAttr] at hr
    rw [contextAttrs_extHasAttr] at ha
    show if (putBack T P e).isContext then a ∉ R else (putBack T P e).ReadsContext R
    by_cases hce : isContext e = true
    · have := eq_of_isContext hce
      subst this
      simp only [isContext, if_true, List.all_cons, List.all_nil, Bool.and_true,
        Bool.not_eq_true'] at ha
      simp only [putBack, Expr.isContext, if_true]
      intro haR
      rw [hR a haR] at ha
      cases ha
    · rw [if_neg hce] at hr ha
      have hce' : isContext e = false := Bool.eq_false_iff.mpr hce
      have h1 := isContext_putBack (T := T) (P := P) hce'
      have h2 : (putBack T P e).isContext = false := by rw [isContext_eq_isContext]; exact h1
      rw [if_neg (by simp [h2])]
      exact readsContext_putBack hR htp e hr ha
  | .var v, hr, _ => by
    cases v <;> simp_all [contextReads, putBack, Expr.ReadsContext]
  | .lit _, _, _ | .temporal _, _, _ | .provider _, _, _ => trivial
  | .unaryApp _ e, hr, ha => by
    simp only [contextReads] at hr; simp only [contextAttrs] at ha
    exact readsContext_putBack hR htp e hr ha
  | .ite a b c, hr, ha => by
    simp only [contextReads, List.append_eq_nil_iff] at hr
    simp only [contextAttrs, List.all_append, Bool.and_eq_true] at ha
    exact ⟨readsContext_putBack hR htp a hr.1.1 ha.1.1, readsContext_putBack hR htp b hr.1.2 ha.1.2,
      readsContext_putBack hR htp c hr.2 ha.2⟩
  | .and a b, hr, ha | .or a b, hr, ha | .binaryApp _ a b, hr, ha => by
    simp only [contextReads, List.append_eq_nil_iff] at hr
    simp only [contextAttrs, List.all_append, Bool.and_eq_true] at ha
    exact ⟨readsContext_putBack hR htp a hr.1 ha.1, readsContext_putBack hR htp b hr.2 ha.2⟩
  | .set xs, hr, ha | .call _ xs, hr, ha => by
    simp only [contextReads] at hr; simp only [contextAttrs] at ha
    exact readsContextList_putBack hR htp xs hr ha
  | .record axs, hr, ha => by
    simp only [contextReads] at hr; simp only [contextAttrs] at ha
    exact readsContextRecord_putBack hR htp axs hr ha

theorem readsContextList_putBack {R : List Cedar.Spec.Attr} (hR : ∀ a ∈ R, isSpecLeafName a = true)
    (htp : (T.map Prod.fst).contains "providers" = false) :
    (xs : List Expr) → contextReadsList ⟨T.map Prod.fst, P.map Prod.fst⟩ xs = [] →
      (contextAttrsList xs).all (fun a => !isSpecLeafName a) = true →
      Expr.ReadsContextList R (putBackList T P xs)
  | [], _, _ => trivial
  | x :: xs, hr, ha => by
    simp only [contextReadsList, List.append_eq_nil_iff] at hr
    simp only [contextAttrsList, List.all_append, Bool.and_eq_true] at ha
    exact ⟨readsContext_putBack hR htp x hr.1 ha.1, readsContextList_putBack hR htp xs hr.2 ha.2⟩

theorem readsContextRecord_putBack {R : List Cedar.Spec.Attr} (hR : ∀ a ∈ R, isSpecLeafName a = true)
    (htp : (T.map Prod.fst).contains "providers" = false) :
    (axs : List (String × Expr)) → contextReadsRecord ⟨T.map Prod.fst, P.map Prod.fst⟩ axs = [] →
      (contextAttrsRecord axs).all (fun a => !isSpecLeafName a) = true →
      Expr.ReadsContextRecord R (putBackRecord T P axs)
  | [], _, _ => trivial
  | (_, x) :: axs, hr, ha => by
    simp only [contextReadsRecord, List.append_eq_nil_iff] at hr
    simp only [contextAttrsRecord, List.all_append, Bool.and_eq_true] at ha
    exact ⟨readsContext_putBack hR htp x hr.1 ha.1, readsContextRecord_putBack hR htp axs hr.2 ha.2⟩

end

mutual

/-- **The crate's context-read check gives the renaming's side condition** on the lowered rule. -/
theorem renameOk_of_reads (g : Generated) (hT : ∀ a ∈ g.temporal, isHoistedName a = true)
    (htp : g.temporal.contains "providers" = false) :
    (y : Cedar.Spec.Expr) → contextReads g (Expr.ofCedar y) = [] →
      (contextAttrs (Expr.ofCedar y)).all (fun a => !isSpecLeafName a) = true →
      renameOk g.temporal g.providers isSpecLeafName y = true
  | .getAttr e a, hr, ha => by
    simp only [Expr.ofCedar] at hr ha
    rw [contextReads_getAttr, isContextProviders_ofCedar, isContext_ofCedar] at hr
    rw [contextAttrs_getAttr, isContext_ofCedar] at ha
    simp only [renameOk]
    by_cases hp : isContextProvidersC e = true
    · rw [if_pos hp] at hr
      have hc : isContextC e = false := by
        cases e with
        | var v => simp [isContextProvidersC] at hp
        | _ => rfl
      rw [if_neg (by simp [hc])]
      split at hr
      · rename_i hpa; rw [if_pos (by rw [hp, hpa]; rfl)]
      · cases hr
    · rw [if_neg hp] at hr
      by_cases hc : isContextC e = true
      · rw [if_pos hc] at hr ha
        rw [if_pos hc]
        simp only [List.all_cons, List.all_nil, Bool.and_true] at ha
        by_cases ht : g.temporal.contains a = true
        · rw [ht]; rfl
        · have ht' : g.temporal.contains a = false := Bool.eq_false_iff.mpr ht
          have : isHoistedName a = false := by
            by_contra hh
            simp only [Bool.not_eq_false] at hh
            rw [hh, ht'] at hr
            simp at hr
          have hne : a ≠ "providers" := by
            rintro rfl; rw [isHoistedName_providers] at this; cases this
          have hne' : (a != "providers") = true := by simp [hne]
          rw [ht', hne']
          simpa using ha
      · rw [if_neg hc] at hr ha
        rw [if_neg hc, if_neg (by simp [hp])]
        exact renameOk_of_reads g hT htp e hr ha
  | .hasAttr e a, hr, ha => by
    simp only [Expr.ofCedar] at hr ha
    rw [contextReads_hasAttr, isContext_ofCedar] at hr
    rw [contextAttrs_hasAttr, isContext_ofCedar] at ha
    simp only [renameOk]
    by_cases hc : isContextC e = true
    · rw [if_pos hc] at hr ha
      rw [if_pos hc]
      simp only [List.all_cons, List.all_nil, Bool.and_true] at ha
      have hh : isHoistedName a = false := by
        by_contra hh
        simp only [Bool.not_eq_false] at hh
        simp [hh] at hr
      have ht : g.temporal.contains a = false := by
        by_contra ht
        simp only [Bool.not_eq_false] at ht
        rw [hT a (mem_of_contains ht)] at hh; cases hh
      have hne : a ≠ "providers" := by
        rintro rfl; rw [isHoistedName_providers] at hh; cases hh
      have hne' : (a != "providers") = true := by simp [hne]
      rw [ht, hne']
      simpa using ha
    · rw [if_neg hc] at hr ha
      rw [if_neg hc]
      exact renameOk_of_reads g hT htp e hr ha
  | .extHasAttr e a as, hr, ha => by
    simp only [Expr.ofCedar] at hr ha
    rw [contextReads_extHasAttr, isContext_ofCedar] at hr
    rw [contextAttrs_extHasAttr, isContext_ofCedar] at ha
    simp only [renameOk]
    by_cases hc : isContextC e = true
    · rw [if_pos hc] at hr ha
      rw [if_pos hc]
      simp only [List.all_cons, List.all_nil, Bool.and_true] at ha
      have hh : isHoistedName a = false := by
        by_contra hh
        simp only [Bool.not_eq_false] at hh
        simp [hh] at hr
      have ht : g.temporal.contains a = false := by
        by_contra ht
        simp only [Bool.not_eq_false] at ht
        rw [hT a (mem_of_contains ht)] at hh; cases hh
      have hne : a ≠ "providers" := by
        rintro rfl; rw [isHoistedName_providers] at hh; cases hh
      have hne' : (a != "providers") = true := by simp [hne]
      rw [ht, hne']
      simpa using ha
    · rw [if_neg hc] at hr ha
      rw [if_neg hc]
      have hre := renameOk_of_reads g hT htp e hr ha
      -- The operand is not `context.providers`: the check rejects a read of it, since
      -- `providers` is not a temporal leaf's name.
      have hp : isContextProvidersC e = false := by
        cases hpe : isContextProvidersC e
        · rfl
        · exfalso
          unfold isContextProvidersC at hpe
          split at hpe
          · simp only [renameOk, isContextC, if_true, bne_self_eq_false, Bool.false_and,
              Bool.or_false] at hre
            rw [htp] at hre
            cases hre
          · cases hpe
      simp [hp, hre]
  | .var v, hr, _ => by
    cases v <;> simp_all [Expr.ofCedar, contextReads, renameOk]
  | .lit _, _, _ => rfl
  | .unaryApp _ e, hr, ha => by
    simp only [Expr.ofCedar, contextReads] at hr; simp only [Expr.ofCedar, contextAttrs] at ha
    simp only [renameOk]; exact renameOk_of_reads g hT htp e hr ha
  | .ite a b c, hr, ha => by
    simp only [Expr.ofCedar, contextReads, List.append_eq_nil_iff] at hr
    simp only [Expr.ofCedar, contextAttrs, List.all_append, Bool.and_eq_true] at ha
    simp only [renameOk, renameOk_of_reads g hT htp a hr.1.1 ha.1.1, renameOk_of_reads g hT htp b hr.1.2 ha.1.2,
      renameOk_of_reads g hT htp c hr.2 ha.2, Bool.and_self]
  | .and a b, hr, ha | .or a b, hr, ha | .binaryApp _ a b, hr, ha => by
    simp only [Expr.ofCedar, contextReads, List.append_eq_nil_iff] at hr
    simp only [Expr.ofCedar, contextAttrs, List.all_append, Bool.and_eq_true] at ha
    simp only [renameOk, renameOk_of_reads g hT htp a hr.1 ha.1, renameOk_of_reads g hT htp b hr.2 ha.2,
      Bool.and_self]
  | .set xs, hr, ha | .call _ xs, hr, ha => by
    simp only [Expr.ofCedar, contextReads] at hr; simp only [Expr.ofCedar, contextAttrs] at ha
    simp only [renameOk]; exact renameOkList_of_reads g hT htp xs hr ha
  | .record axs, hr, ha => by
    simp only [Expr.ofCedar, contextReads] at hr; simp only [Expr.ofCedar, contextAttrs] at ha
    simp only [renameOk]; exact renameOkRecord_of_reads g hT htp axs hr ha

theorem renameOkList_of_reads (g : Generated) (hT : ∀ a ∈ g.temporal, isHoistedName a = true)
    (htp : g.temporal.contains "providers" = false) :
    (ys : List Cedar.Spec.Expr) → contextReadsList g (Expr.ofCedarList ys) = [] →
      (contextAttrsList (Expr.ofCedarList ys)).all (fun a => !isSpecLeafName a) = true →
      renameOkList g.temporal g.providers isSpecLeafName ys = true
  | [], _, _ => rfl
  | y :: ys, hr, ha => by
    simp only [Expr.ofCedarList, contextReadsList, List.append_eq_nil_iff] at hr
    simp only [Expr.ofCedarList, contextAttrsList, List.all_append, Bool.and_eq_true] at ha
    simp only [renameOkList, renameOk_of_reads g hT htp y hr.1 ha.1, renameOkList_of_reads g hT htp ys hr.2 ha.2,
      Bool.and_self]

theorem renameOkRecord_of_reads (g : Generated) (hT : ∀ a ∈ g.temporal, isHoistedName a = true)
    (htp : g.temporal.contains "providers" = false) :
    (ays : List (Cedar.Spec.Attr × Cedar.Spec.Expr)) → contextReadsRecord g (Expr.ofCedarRecord ays) = [] →
      (contextAttrsRecord (Expr.ofCedarRecord ays)).all (fun a => !isSpecLeafName a) = true →
      renameOkRecord g.temporal g.providers isSpecLeafName ays = true
  | [], _, _ => rfl
  | (_, y) :: ays, hr, ha => by
    simp only [Expr.ofCedarRecord, contextReadsRecord, List.append_eq_nil_iff] at hr
    simp only [Expr.ofCedarRecord, contextAttrsRecord, List.all_append, Bool.and_eq_true] at ha
    simp only [renameOkRecord, renameOk_of_reads g hT htp y hr.1 ha.1,
      renameOkRecord_of_reads g hT htp ays hr.2 ha.2, Bool.and_self]

end

/-! ## Positions in a list without repetitions -/

theorem idxOf_cons_ne' {α : Type} [BEq α] [LawfulBEq α] {x a : α} {L : List α} (h : x ≠ a) :
    (x :: L).idxOf a = L.idxOf a + 1 := by
  rw [List.idxOf_cons]
  have : (x == a) = false := by simpa using h
  simp [this]

theorem idxOf_of_getElem? {α : Type} [BEq α] [LawfulBEq α] :
    {L : List α} → L.Nodup → {i : Nat} → {r : α} → L[i]? = some r → L.idxOf r = i
  | [], _, _, _, h => by simp at h
  | x :: L, hn, i, r, h => by
    rw [List.nodup_cons] at hn
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; exact List.idxOf_cons_self
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have hr : r ∈ L := List.mem_of_getElem? h
      have hne : x ≠ r := fun he => hn.1 (he ▸ hr)
      rw [idxOf_cons_ne' hne, idxOf_of_getElem? hn.2 h]

theorem eq_of_idxOf_eq {α : Type} [BEq α] [LawfulBEq α] :
    {L : List α} → {a b : α} → a ∈ L → b ∈ L → L.idxOf a = L.idxOf b → a = b
  | [], _, _, ha, _, _ => by cases ha
  | x :: L, a, b, ha, hb, h => by
    by_cases hxa : x = a
    · subst hxa
      by_cases hxb : x = b
      · exact hxb
      · rw [List.idxOf_cons_self, idxOf_cons_ne' hxb] at h
        cases h
    · rw [idxOf_cons_ne' hxa] at h
      by_cases hxb : x = b
      · subst hxb; rw [List.idxOf_cons_self] at h; cases h
      · rw [idxOf_cons_ne' hxb] at h
        exact eq_of_idxOf_eq ((List.mem_cons.mp ha).resolve_left (Ne.symm hxa))
          ((List.mem_cons.mp hb).resolve_left (Ne.symm hxb)) (by omega)

/-- In a list of lists without repetitions overall, an element is in at most one of them. -/
theorem index_unique_of_nodup_flatten {α : Type} {L : List (List α)} (hn : L.flatten.Nodup)
    {i j : Nat} {xs ys : List α} {a : α} (hi : L[i]? = some xs) (hj : L[j]? = some ys)
    (ha : a ∈ xs) (hb : a ∈ ys) : i = j := by
  induction L generalizing i j with
  | nil => simp at hi
  | cons z L ih =>
    simp only [List.flatten_cons] at hn
    rw [List.nodup_append] at hn
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hi hj
        subst hi
        exact absurd (List.mem_flatten.mpr ⟨ys, List.mem_of_getElem? hj, hb⟩) (fun h => hn.2.2 a ha a h rfl)
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hi hj
        subst hj
        exact absurd (List.mem_flatten.mpr ⟨xs, List.mem_of_getElem? hi, ha⟩) (fun h => hn.2.2 a hb a h rfl)
      | succ j =>
        simp only [List.getElem?_cons_succ] at hi hj
        rw [ih hn.2.1 hi hj]

/-! ## The facts the port computes for a leaf read once -/

/-- The temporal reads among the hoisted reads. -/
def temporalIds (rs : List (Bool × String)) : List String :=
  rs.filterMap fun r => if r.1 then some r.2 else none

theorem temporalIds_append (r₁ r₂ : List (Bool × String)) :
    temporalIds (r₁ ++ r₂) = temporalIds r₁ ++ temporalIds r₂ := by
  simp [temporalIds, List.filterMap_append]

mutual

/-- The leaves the facts walk records are the temporal hoisted reads, in order. -/
theorem leafFactsW_keys (tids pids : List String) (htp : tids.contains "providers" = false)
    (G : List Guard) : (x : Expr) →
    (leafFactsW (tids.contains ·) G x).map Prod.fst = temporalIds (hoistedReads tids pids x)
  | .getAttr e a => by
    have htp' : "providers" ∉ tids := by simpa using htp
    by_cases hc : isContext e = true
    · have := eq_of_isContext hc; subst this
      by_cases ha : tids.contains a = true
      · have ha2 : a ∈ tids := mem_of_contains ha
        simp [leafFactsW, hoistedReads, isContext, ha2, temporalIds]
      · have ha2 : a ∉ tids := by simpa using ha
        simp [leafFactsW, hoistedReads, isContext, isContextProviders, ha2, temporalIds]
    · have hc' : isContext e = false := Bool.eq_false_iff.mpr hc
      by_cases hp : isContextProviders e = true
      · have := eq_of_isContextProviders hp; subst this
        by_cases ha : pids.contains a = true
        · have ha2 : a ∈ pids := mem_of_contains ha
          simp [leafFactsW, hoistedReads, isContext, isContextProviders, ha2, htp', temporalIds]
        · have ha2 : a ∉ pids := by simpa using ha
          simp [leafFactsW, hoistedReads, isContext, isContextProviders, ha2, htp', temporalIds]
      · have hp' : isContextProviders e = false := Bool.eq_false_iff.mpr hp
        have h1 : leafFactsW (tids.contains ·) G (.getAttr e a) = leafFactsW (tids.contains ·) G e := by
          cases e with
          | var v => cases v <;> simp_all [isContext, leafFactsW]
          | _ => rfl
        rw [h1, leafFactsW_keys tids pids htp G e]
        simp [hoistedReads, hc', hp']
  | .lit _ | .var _ | .temporal _ | .provider _ => by
    simp [leafFactsW, hoistedReads, temporalIds]
  | .ite c t e => by
    simp only [leafFactsW, hoistedReads, List.map_append, temporalIds_append,
      leafFactsW_keys tids pids htp _ c, leafFactsW_keys tids pids htp _ t, leafFactsW_keys tids pids htp _ e]
  | .and a b | .or a b | .binaryApp _ a b => by
    simp only [leafFactsW, hoistedReads, List.map_append, temporalIds_append,
      leafFactsW_keys tids pids htp _ a, leafFactsW_keys tids pids htp _ b]
  | .unaryApp _ a | .hasAttr a _ | .extHasAttr a _ _ => by
    simp only [leafFactsW, hoistedReads, leafFactsW_keys tids pids htp _ a]
  | .set xs | .call _ xs => by
    simp only [leafFactsW, hoistedReads, leafFactsWList_keys tids pids htp G xs]
  | .record axs => by
    simp only [leafFactsW, hoistedReads, leafFactsWRecord_keys tids pids htp G axs]

theorem leafFactsWList_keys (tids pids : List String) (htp : tids.contains "providers" = false)
    (G : List Guard) : (xs : List Expr) →
    (leafFactsWList (tids.contains ·) G xs).map Prod.fst = temporalIds (hoistedReadsList tids pids xs)
  | [] => rfl
  | x :: xs => by
    simp only [leafFactsWList, hoistedReadsList, List.map_append, temporalIds_append,
      leafFactsW_keys tids pids htp G x, leafFactsWList_keys tids pids htp G xs]

theorem leafFactsWRecord_keys (tids pids : List String) (htp : tids.contains "providers" = false)
    (G : List Guard) : (axs : List (String × Expr)) →
    (leafFactsWRecord (tids.contains ·) G axs).map Prod.fst =
      temporalIds (hoistedReadsRecord tids pids axs)
  | [] => rfl
  | (_, x) :: axs => by
    simp only [leafFactsWRecord, hoistedReadsRecord, List.map_append, temporalIds_append,
      leafFactsW_keys tids pids htp G x, leafFactsWRecord_keys tids pids htp G axs]

end

/-- One step of `mergeFacts`. -/
def mstep (acc : List (String × List Guard)) : String × List Guard → List (String × List Guard)
  | (id, here) =>
    match acc.lookup id with
    | some existing =>
      acc.map fun (k, v) => if k == id then (k, existing.filter (here.contains ·)) else (k, v)
    | none => acc ++ [(id, here)]

theorem mergeFacts_eq (xs : List (String × List Guard)) : mergeFacts xs = xs.foldl mstep [] := rfl

theorem lookup_map_update {a id : String} (h : a ≠ id) (c : List Guard) :
    (acc : List (String × List Guard)) →
    (acc.map fun (k, v) => if k == id then (k, c) else (k, v)).lookup a = acc.lookup a
  | [] => rfl
  | (k, v) :: acc => by
    have ih := lookup_map_update h c acc
    show List.lookup a ((if k == id then (k, c) else (k, v)) ::
      List.map (fun (k, v) => if k == id then (k, c) else (k, v)) acc) = List.lookup a ((k, v) :: acc)
    by_cases hk : (k == id) = true
    · rw [if_pos hk]
      have hk' : k = id := by simpa using hk
      have hak : (a == k) = false := by rw [hk']; simpa using h
      simp only [List.lookup, hak]; exact ih
    · rw [if_neg hk]
      simp only [List.lookup]
      cases hak : a == k
      · exact ih
      · rfl

theorem lookup_append_ne {a id : String} (h : a ≠ id) (v : List Guard) :
    (acc : List (String × List Guard)) → (acc ++ [(id, v)]).lookup a = acc.lookup a
  | [] => by
    have : (a == id) = false := by simpa using h
    simp [List.lookup, this]
  | (k, w) :: acc => by
    by_cases hak : a = k
    · subst hak; simp [List.lookup]
    · have h1 : (a == k) = false := by simpa using hak
      simp [List.lookup, h1, lookup_append_ne h v acc]

theorem lookup_append_none {a : String} (v : List Guard) :
    (acc : List (String × List Guard)) → acc.lookup a = none → (acc ++ [(a, v)]).lookup a = some v
  | [], _ => by simp
  | (k, w) :: acc, h => by
    by_cases hak : a = k
    · subst hak; simp [List.lookup] at h
    · have h1 : (a == k) = false := by simpa using hak
      simp only [List.lookup, h1] at h
      simp only [List.cons_append, List.lookup, h1]; exact lookup_append_none v acc h

theorem mstep_lookup_ne {a : String} {x : String × List Guard} (h : a ≠ x.1)
    (acc : List (String × List Guard)) : (mstep acc x).lookup a = acc.lookup a := by
  obtain ⟨id, here⟩ := x
  simp only [mstep]
  split
  · exact lookup_map_update h _ acc
  · exact lookup_append_ne h _ acc

theorem foldl_mstep_lookup_not_mem {a : String} :
    (xs : List (String × List Guard)) → a ∉ xs.map Prod.fst → (acc : List (String × List Guard)) →
    (xs.foldl mstep acc).lookup a = acc.lookup a
  | [], _, _ => rfl
  | x :: xs, h, acc => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [List.foldl_cons, foldl_mstep_lookup_not_mem xs h.2, mstep_lookup_ne h.1]

/-- A leaf read once keeps the facts of its one position. -/
theorem mergeFacts_lookup_once {xs : List (String × List Guard)} {a : String} {G : List Guard}
    (hn : (xs.map Prod.fst).Nodup) (hm : (a, G) ∈ xs) : (mergeFacts xs).lookup a = some G := by
  obtain ⟨ys, zs, rfl⟩ := List.append_of_mem hm
  simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at hn
  have hys : a ∉ ys.map Prod.fst := fun h => hn.2.2 a h a (by simp) rfl
  have hzs : a ∉ zs.map Prod.fst := hn.2.1.1
  rw [mergeFacts_eq, List.foldl_append, List.foldl_cons, foldl_mstep_lookup_not_mem zs hzs]
  have h0 : (ys.foldl mstep []).lookup a = none := by
    rw [foldl_mstep_lookup_not_mem ys hys]; rfl
  simp only [mstep, h0]
  exact lookup_append_none G _ h0

theorem mergeFacts_lookup_not_mem {xs : List (String × List Guard)} {a : String}
    (h : a ∉ xs.map Prod.fst) : (mergeFacts xs).lookup a = none := by
  rw [mergeFacts_eq, foldl_mstep_lookup_not_mem xs h]; rfl

theorem lookup_append {β : Type} {a : String} :
    (X Y : List (String × β)) → (X ++ Y).lookup a = (X.lookup a).or (Y.lookup a)
  | [], _ => rfl
  | (k, v) :: X, Y => by
    simp only [List.cons_append, List.lookup]
    cases a == k
    · exact lookup_append X Y
    · rfl

theorem lookup_filter {β : Type} {a : String} (q : String → Bool) :
    (X : List (String × β)) → (X.filter fun x => q x.1).lookup a = if q a then X.lookup a else none
  | [] => by simp
  | (k, v) :: X => by
    have ih := lookup_filter (a := a) q X
    by_cases hak : a = k
    · subst hak
      by_cases hq : q a = true
      · rw [List.filter_cons_of_pos (p := fun x : String × β => q x.1) hq]; simp [List.lookup, hq]
      · rw [List.filter_cons_of_neg (p := fun x : String × β => q x.1) hq, ih, if_neg hq, if_neg hq]
    · have h1 : (a == k) = false := by simpa using hak
      by_cases hqk : q k = true
      · rw [List.filter_cons_of_pos (p := fun x : String × β => q x.1) hqk]
        simp only [List.lookup, h1, ih]
      · rw [List.filter_cons_of_neg (p := fun x : String × β => q x.1) hqk, ih]
        simp only [List.lookup, h1]

/-- One step of `loweredFacts`. -/
def lstep (l : Lowered) (acc : List (String × List Guard)) (k : Nat) : List (String × List Guard) :=
  match l.policies[k]? with
  | some p =>
    let here := mergeFacts (leafFactsW ((l.temporal.map (·.id)).contains ·) []
      (Dogwood.Spec.Conditions.toExpr p.condition))
    (acc.filter fun (id, _) => !(here.any (·.1 == id))) ++ here
  | none => acc

theorem loweredFacts_eq (l : Lowered) :
    loweredFacts l = (l.temporalRules.eraseDups.mergeSort (· ≤ ·)).foldl (lstep l) [] := rfl

/-- The facts of a rule's walk. -/
def ruleFacts (l : Lowered) (p : Dogwood.Spec.Policy) : List (String × List Guard) :=
  mergeFacts (leafFactsW ((l.temporal.map (·.id)).contains ·) [] (Dogwood.Spec.Conditions.toExpr p.condition))

theorem any_key_of_lookup {β : Type} {a : String} :
    (X : List (String × β)) → ((X.lookup a).isSome ↔ X.any (·.1 == a) = true)
  | [] => by simp [List.lookup]
  | (k, v) :: X => by
    by_cases hak : a = k
    · subst hak; simp [List.lookup]
    · have h1 : (a == k) = false := by simpa using hak
      have h2 : (k == a) = false := by
        rw [beq_eq_false_iff_ne]; exact fun h => hak h.symm
      simp only [List.lookup, h1, List.any_cons, h2, Bool.false_or]
      exact any_key_of_lookup X

theorem lstep_lookup (l : Lowered) {a : String} (acc : List (String × List Guard)) (k : Nat) :
    (lstep l acc k).lookup a =
      match l.policies[k]? with
      | some p => match (ruleFacts l p).lookup a with
        | some G => some G
        | none => acc.lookup a
      | none => acc.lookup a := by
  unfold lstep
  split
  · rename_i p hp
    simp only
    have hf := lookup_filter (a := a) (fun id => !((ruleFacts l p).any (·.1 == id))) acc
    simp only [ruleFacts] at hf
    rw [lookup_append, hf]
    simp only [ruleFacts]
    cases hl : (mergeFacts (leafFactsW ((l.temporal.map (·.id)).contains ·) []
        (Dogwood.Spec.Conditions.toExpr p.condition))).lookup a with
    | some G =>
      have hany := (any_key_of_lookup _).mp (by rw [hl]; rfl)
      simp only [hany]
      simp
    | none =>
      have hany : (mergeFacts (leafFactsW ((l.temporal.map (·.id)).contains ·) []
          (Dogwood.Spec.Conditions.toExpr p.condition))).any (·.1 == a) = false := by
        rw [Bool.eq_false_iff]; intro h
        have := (any_key_of_lookup _).mpr h
        rw [hl] at this; cases this
      simp only [hany]
      simp
  · rfl

theorem foldl_lstep_lookup (l : Lowered) {a : String} {k : Nat} {q : Dogwood.Spec.Policy}
    {G : List Guard} (hq : l.policies[k]? = some q) (hG : (ruleFacts l q).lookup a = some G)
    (hother : ∀ k' q', k' ≠ k → l.policies[k']? = some q' → (ruleFacts l q').lookup a = none) :
    (ks : List Nat) → (acc : List (String × List Guard)) →
      (ks.foldl (lstep l) acc).lookup a = if k ∈ ks then some G else acc.lookup a
  | [], acc => by simp
  | k' :: ks, acc => by
    rw [List.foldl_cons, foldl_lstep_lookup l hq hG hother ks]
    by_cases hk : k' = k
    · subst hk
      simp [lstep_lookup, hq, hG]
    · rw [lstep_lookup]
      cases hp : l.policies[k']? with
      | none => simp [Ne.symm hk]
      | some q' =>
        simp only [hother k' q' hk hp]
        by_cases hks : k ∈ ks
        · simp [hks]
        · simp [hks, Ne.symm hk]

/-- **The facts the port computes for a temporal leaf** are those of the leaf's rule, when only
that rule reads it. -/
theorem loweredFacts_lookup {l : Lowered} {k : Nat} {q : Dogwood.Spec.Policy} {a : String}
    {G : List Guard} (hq : l.policies[k]? = some q) (hk : k ∈ l.temporalRules)
    (hG : (ruleFacts l q).lookup a = some G)
    (hother : ∀ k' q', k' ≠ k → l.policies[k']? = some q' → (ruleFacts l q').lookup a = none) :
    (loweredFacts l).lookup a = some G := by
  rw [loweredFacts_eq, foldl_lstep_lookup l hq hG hother]
  have : k ∈ l.temporalRules.eraseDups.mergeSort (· ≤ ·) := by
    rw [List.mem_mergeSort]; exact List.mem_eraseDups.mpr hk
  simp [this]

/-! ## The projection, unfolded -/

/-- **The projection of a lowered set**, unfolded. -/
theorem toConformance_ok {l : Lowered} {c : Conformance.Lowered} (h : l.toConformance = .ok c) :
    ∃ T Pr sigs, l.leafFormulas = .ok T ∧ l.providerCalls = .ok Pr ∧
      typedSignatures l.eventSchema l.schema = .ok sigs ∧
      c.policySet =
        { policies := l.policies.map (putBackPolicy T Pr)
          schema := sigs
          actionSchema := specActionSchema l
          maxWindow := l.eventSchema.maxWindow.seconds
          maxHorizon := l.eventSchema.maxHorizon.map (·.seconds)
          providerDecls := (providerDeclsToSpec l.declarations l.schema).1
          externalTypes := CedarSchema.Resolve.externalEntityTypes l.augmentedSchema
          externalActions := CedarSchema.Resolve.externalActions l.augmentedSchema } := by
  unfold Lowered.toConformance at h
  cases hT : l.leafFormulas with
  | error e => rw [hT] at h; cases h
  | ok T =>
    cases hP : l.providerCalls with
    | error e => rw [hT, hP] at h; cases h
    | ok Pr =>
      cases hS : typedSignatures l.eventSchema l.schema with
      | error e => rw [hT, hP, hS] at h; cases h
      | ok sigs =>
        rw [hT, hP, hS] at h
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨T, Pr, sigs, rfl, rfl, rfl, rfl⟩

/-- The leaf formulas, field by field. -/
theorem leafFormulas_forall₂ {l : Lowered} {T : List (String × Formula)} (h : l.leafFormulas = .ok T) :
    List.Forall₂ (fun f p => p.1 = f.id ∧ f.condition.condition.toFormula = .ok p.2) l.temporal T := by
  unfold Lowered.leafFormulas at h
  have := List.mapM_ok_iff_forall₂.mp h
  refine Cedar.List.Forall₂.imp (fun f p hfp => ?_) this
  cases hφ : f.condition.condition.toFormula with
  | error e => rw [hφ] at hfp; cases hfp
  | ok φ =>
    rw [hφ] at hfp
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hfp
    subst hfp
    exact ⟨rfl, rfl⟩

theorem providerCalls_forall₂ {l : Lowered} {Pr : List (String × Dogwood.Spec.Provider.Call)}
    (h : l.providerCalls = .ok Pr) :
    List.Forall₂ (fun g p => p.1 = g.id ∧ g.toCall = .ok p.2) l.providers Pr := by
  unfold Lowered.providerCalls at h
  have := List.mapM_ok_iff_forall₂.mp h
  refine Cedar.List.Forall₂.imp (fun g p hgp => ?_) this
  cases hc : g.toCall with
  | error e => rw [hc] at hgp; cases hgp
  | ok c =>
    rw [hc] at hgp
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hgp
    subst hgp
    exact ⟨rfl, rfl⟩

theorem keys_of_forall₂ {α β : Type} {xs : List α} {ys : List (String × β)} {key : α → String}
    {R : α → String × β → Prop} (h : List.Forall₂ R xs ys) (hR : ∀ x y, R x y → y.1 = key x) :
    ys.map Prod.fst = xs.map key := by
  induction h with
  | nil => rfl
  | cons hxy _ ih => simp [hR _ _ hxy, ih]

/-- A key's value is the value of an element of that key. -/
theorem mem_of_lookup {β : Type} {L : List (String × β)} {a : String} {v : β}
    (h : L.lookup a = some v) : (a, v) ∈ L := by
  induction L with
  | nil => simp [List.lookup] at h
  | cons p L ih =>
    obtain ⟨k, w⟩ := p
    by_cases hk : a = k
    · subst hk; simp [List.lookup] at h; subst h; simp
    · have : (a == k) = false := by simpa using hk
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem exists_of_mem_forall₂ {α β : Type} {xs : List α} {ys : List β} {R : α → β → Prop}
    (h : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) : ∃ (i : Nat) (x : α), xs[i]? = some x ∧ ys[i]? = some y ∧ R x y := by
  induction h with
  | nil => cases hy
  | cons hxy _ ih =>
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨0, _, rfl, rfl, hxy⟩
    · obtain ⟨i, x, h₁, h₂, h₃⟩ := ih hy
      exact ⟨i + 1, x, by simpa using h₁, by simpa using h₂, h₃⟩


end Dogwood.Thm.Frontend
