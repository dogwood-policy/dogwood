import Dogwood.Thm.Frontend.Validate.Sound
import Dogwood.Thm.Frontend.Validate.CompleteInterface
import Dogwood.Frontend.Validate.Converse

/-!
# The correspondences of completeness: from the crate's leaves to the specification's

Soundness goes from each leaf of the specification's projection to the crate's leaf it puts back
(`temporal_position`, `provider_position`), and from each environment the specification types a
leaf in to one the crate checks it in (`leafEnv`). Completeness goes the other way:

* each temporal leaf of the lowered set is a temporal leaf of the projection, at a position whose
  facts are the crate's outside reserved heads, and among the crate's (`temporal_position'`);
* each provider leaf of the lowered set is a provider leaf of the projection
  (`provider_position'`);
* each request environment the crate checks a leaf in is an environment the specification types
  it in, seen alike (`specEnv_of_mem`), under `scopesExact`;
* the specification's typing context sees the crate's environment exactly (`viewExact_of`), under
  `derivedFieldsResolve`.
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.Validate
open Dogwood.Spec (Expr Leaf leafAttr PolicySet)
open Dogwood.Spec.Temporal (Formula Guard TypingCtx)
open Cedar.Validation (CedarType Schema ActionSchemaEntry RecordType QualifiedType TypeEnv)
open Cedar.Data (Map)

/-! ## Facts the put-back establishes are the crate's -/

section

variable {T : List (String × Formula)} {P : List (String × Dogwood.Spec.Provider.Call)}

theorem attrChain_of_putBack : ∀ (x : Expr) {vp : Cedar.Spec.Var × Dogwood.Spec.Path},
    (putBack T P x).attrChain? = some vp → x.attrChain? = some vp
  | .var _, _, h => by simpa [putBack] using h
  | .getAttr y a, vp, h => by
    rw [putBack_getAttr] at h
    split at h
    · simp [Expr.attrChain?] at h
    · split at h
      · simp [Expr.attrChain?] at h
      · simp only [Expr.attrChain?] at h ⊢
        cases hy : (putBack T P y).attrChain? with
        | none => rw [hy] at h; cases h
        | some vp' => rw [hy] at h; rw [attrChain_of_putBack y hy]; exact h
  | .lit _, _, h | .ite _ _ _, _, h | .and _ _, _, h | .or _ _, _, h | .unaryApp _ _, _, h
  | .binaryApp _ _ _, _, h | .hasAttr _ _, _, h | .extHasAttr _ _ _, _, h | .set _, _, h
  | .record _, _, h | .call _ _, _, h
  | .temporal _, _, h | .provider _, _, h => by simp [putBack, Expr.attrChain?] at h

/-- **The facts a put-back expression establishes are the crate's.** -/
theorem facts_of_putBack : ∀ (x : Expr), ∀ g ∈ (putBack T P x).facts, g ∈ x.facts
  | .hasAttr x a, g, hg => by
    simp only [putBack, Expr.facts] at hg ⊢
    unfold Expr.hasFact? at hg ⊢
    cases hc : (putBack T P x).attrChain? with
    | none => rw [hc] at hg; simp at hg
    | some vp => rw [hc] at hg; rw [attrChain_of_putBack x hc]; exact hg
  | .extHasAttr x a rest, g, hg => by
    simp only [putBack, Expr.facts] at hg ⊢
    cases hc : (putBack T P x).attrChain? with
    | none => rw [extHasFacts_none rest _ a hc] at hg; cases hg
    | some vp =>
      rwa [extHasFacts_congr rest (putBack T P x) x a (by rw [hc, attrChain_of_putBack x hc])] at hg
  | .and a b, g, hg => by
    simp only [putBack, Expr.facts, List.mem_append] at hg ⊢
    rcases hg with hg | hg
    · exact Or.inl (facts_of_putBack a g hg)
    · exact Or.inr (facts_of_putBack b g hg)
  | .getAttr e a, g, hg => by
    rw [putBack_getAttr] at hg
    split at hg
    · simp [Expr.facts] at hg
    · split at hg <;> simp [Expr.facts] at hg
  | .lit _, _, hg | .var _, _, hg | .ite _ _ _, _, hg | .or _ _, _, hg | .unaryApp _ _, _, hg
  | .binaryApp _ _ _, _, hg | .set _, _, hg | .record _, _, hg | .call _ _, _, hg
  | .temporal _, _, hg | .provider _, _, hg => by simp [putBack, Expr.facts] at hg

theorem sub_append {F₀ G₀ F₁ G₁ : List Guard} (h₀ : ∀ g ∈ F₀, g ∈ G₀) (h₁ : ∀ g ∈ F₁, g ∈ G₁) :
    ∀ g ∈ F₀ ++ F₁, g ∈ G₀ ++ G₁ := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact List.mem_append_left _ (h₀ g h)
  · exact List.mem_append_right _ (h₁ g h)

mutual

/-- **Each temporal read of the crate's is a temporal leaf of the put-back expression**, at a
position whose facts are the crate's outside reserved heads, and among the crate's. -/
theorem putBack_of_leafFactsW (hT : ∀ a ∈ T.map Prod.fst, isHoistedName a = true)
    (htp : (T.map Prod.fst).contains "providers" = false) :
    ∀ (x : Expr) (F₀ G₀ : List Guard), x.leaves = [] → NrSub G₀ F₀ → (∀ g ∈ F₀, g ∈ G₀) →
      ∀ a G, (a, G) ∈ leafFactsW ((T.map Prod.fst).contains ·) G₀ x →
      ∃ F, (.inl ((T.lookup a).getD default), F) ∈ (putBack T P x).leafFacts F₀ ∧ NrSub G F ∧
        ∀ g ∈ F, g ∈ G
  | .getAttr e a', F₀, G₀, hl, hG, hF, a, G, hm => by
    simp only [Expr.leaves] at hl
    rw [putBack_getAttr]
    by_cases hc : isContext e = true
    · have he := eq_of_isContext hc
      subst he
      simp only [leafFactsW] at hm
      split at hm
      · rename_i hcon
        simp only [List.mem_singleton, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        rw [if_pos (by simp only [isContext, hcon, Bool.and_self])]
        exact ⟨F₀, by simp [Expr.leafFacts], hG, hF⟩
      · cases hm
    · have hm' : (a, G) ∈ leafFactsW ((T.map Prod.fst).contains ·) G₀ e := by
        cases e with
        | var v => cases v <;> simp_all [isContext, leafFactsW]
        | _ => simp only [leafFactsW] at hm; exact hm
      rw [if_neg (by simp [hc])]
      split
      · rename_i hcp
        exfalso
        simp only [Bool.and_eq_true] at hcp
        have := eq_of_isContextProviders hcp.1
        subst this
        simp only [leafFactsW, htp, Bool.false_eq_true, if_false] at hm'
        cases hm'
      · obtain ⟨F, h₁, h₂, h₃⟩ := putBack_of_leafFactsW hT htp e F₀ G₀ hl hG hF a G hm'
        exact ⟨F, by simpa [Expr.leafFacts] using h₁, h₂, h₃⟩
  | .lit _, _, _, _, _, _, _, _, hm | .var _, _, _, _, _, _, _, _, hm => by
    simp [leafFactsW] at hm
  | .temporal _, _, _, hl, _, _, _, _, _ | .provider _, _, _, hl, _, _, _, _, _ => by
    simp [Expr.leaves] at hl
  | .ite c t e, F₀, G₀, hl, hG, hF, a, G, hm => by
    simp only [Expr.leaves, List.append_eq_nil_iff] at hl
    simp only [leafFactsW, List.mem_append] at hm
    simp only [putBack, Expr.leafFacts, List.mem_append]
    rcases hm with (hm | hm) | hm
    · obtain ⟨F, h₁, h₂, h₃⟩ := putBack_of_leafFactsW hT htp c F₀ G₀ hl.1.1 hG hF a G hm
      exact ⟨F, Or.inl (Or.inl h₁), h₂, h₃⟩
    · obtain ⟨F, h₁, h₂, h₃⟩ := putBack_of_leafFactsW hT htp t _ _ hl.1.2
        (NrSub.append hG (facts_putBack hT c)) (sub_append hF (facts_of_putBack c)) a G hm
      exact ⟨F, Or.inl (Or.inr h₁), h₂, h₃⟩
    · obtain ⟨F, h₁, h₂, h₃⟩ := putBack_of_leafFactsW hT htp e F₀ G₀ hl.2 hG hF a G hm
      exact ⟨F, Or.inr h₁, h₂, h₃⟩
  | .and x y, F₀, G₀, hl, hG, hF, a, G, hm => by
    simp only [Expr.leaves, List.append_eq_nil_iff] at hl
    simp only [leafFactsW, List.mem_append] at hm
    simp only [putBack, Expr.leafFacts, List.mem_append]
    rcases hm with hm | hm
    · obtain ⟨F, h₁, h₂, h₃⟩ := putBack_of_leafFactsW hT htp x F₀ G₀ hl.1 hG hF a G hm
      exact ⟨F, Or.inl h₁, h₂, h₃⟩
    · obtain ⟨F, h₁, h₂, h₃⟩ := putBack_of_leafFactsW hT htp y _ _ hl.2
        (NrSub.append hG (facts_putBack hT x)) (sub_append hF (facts_of_putBack x)) a G hm
      exact ⟨F, Or.inr h₁, h₂, h₃⟩
  | .or x y, F₀, G₀, hl, hG, hF, a, G, hm => by
    simp only [Expr.leaves, List.append_eq_nil_iff] at hl
    simp only [leafFactsW, List.mem_append] at hm
    simp only [putBack, Expr.leafFacts, List.mem_append]
    rcases hm with hm | hm
    · obtain ⟨F, h₁, h₂, h₃⟩ := putBack_of_leafFactsW hT htp x F₀ G₀ hl.1 hG hF a G hm
      exact ⟨F, Or.inl h₁, h₂, h₃⟩
    · obtain ⟨F, h₁, h₂, h₃⟩ := putBack_of_leafFactsW hT htp y F₀ G₀ hl.2 hG hF a G hm
      exact ⟨F, Or.inr h₁, h₂, h₃⟩
  | .binaryApp _ x y, F₀, G₀, hl, hG, hF, a, G, hm => by
    simp only [Expr.leaves, List.append_eq_nil_iff] at hl
    simp only [leafFactsW, List.mem_append] at hm
    simp only [putBack, Expr.leafFacts, List.mem_append]
    rcases hm with hm | hm
    · obtain ⟨F, h₁, h₂, h₃⟩ := putBack_of_leafFactsW hT htp x F₀ G₀ hl.1 hG hF a G hm
      exact ⟨F, Or.inl h₁, h₂, h₃⟩
    · obtain ⟨F, h₁, h₂, h₃⟩ := putBack_of_leafFactsW hT htp y F₀ G₀ hl.2 hG hF a G hm
      exact ⟨F, Or.inr h₁, h₂, h₃⟩
  | .unaryApp _ x, F₀, G₀, hl, hG, hF, a, G, hm | .hasAttr x _, F₀, G₀, hl, hG, hF, a, G, hm
  | .extHasAttr x _ _, F₀, G₀, hl, hG, hF, a, G, hm => by
    simp only [Expr.leaves] at hl
    simp only [leafFactsW] at hm
    simp only [putBack, Expr.leafFacts]
    exact putBack_of_leafFactsW hT htp x F₀ G₀ hl hG hF a G hm
  | .set xs, F₀, G₀, hl, hG, hF, a, G, hm | .call _ xs, F₀, G₀, hl, hG, hF, a, G, hm => by
    simp only [Expr.leaves] at hl
    simp only [leafFactsW] at hm
    simp only [putBack, Expr.leafFacts]
    exact putBackList_of_leafFactsW hT htp xs F₀ G₀ hl hG hF a G hm
  | .record axs, F₀, G₀, hl, hG, hF, a, G, hm => by
    simp only [Expr.leaves] at hl
    simp only [leafFactsW] at hm
    simp only [putBack, Expr.leafFacts]
    exact putBackRecord_of_leafFactsW hT htp axs F₀ G₀ hl hG hF a G hm

theorem putBackList_of_leafFactsW (hT : ∀ a ∈ T.map Prod.fst, isHoistedName a = true)
    (htp : (T.map Prod.fst).contains "providers" = false) :
    ∀ (xs : List Expr) (F₀ G₀ : List Guard), Expr.leavesList xs = [] → NrSub G₀ F₀ →
      (∀ g ∈ F₀, g ∈ G₀) →
      ∀ a G, (a, G) ∈ leafFactsWList ((T.map Prod.fst).contains ·) G₀ xs →
      ∃ F, (.inl ((T.lookup a).getD default), F) ∈ Expr.leafFactsList F₀ (putBackList T P xs) ∧
        NrSub G F ∧ ∀ g ∈ F, g ∈ G
  | [], _, _, _, _, _, _, _, hm => by simp [leafFactsWList] at hm
  | x :: xs, F₀, G₀, hl, hG, hF, a, G, hm => by
    simp only [Expr.leavesList, List.append_eq_nil_iff] at hl
    simp only [leafFactsWList, List.mem_append] at hm
    simp only [putBackList, Expr.leafFactsList, List.mem_append]
    rcases hm with hm | hm
    · obtain ⟨F, h₁, h₂, h₃⟩ := putBack_of_leafFactsW hT htp x F₀ G₀ hl.1 hG hF a G hm
      exact ⟨F, Or.inl h₁, h₂, h₃⟩
    · obtain ⟨F, h₁, h₂, h₃⟩ := putBackList_of_leafFactsW hT htp xs F₀ G₀ hl.2 hG hF a G hm
      exact ⟨F, Or.inr h₁, h₂, h₃⟩

theorem putBackRecord_of_leafFactsW (hT : ∀ a ∈ T.map Prod.fst, isHoistedName a = true)
    (htp : (T.map Prod.fst).contains "providers" = false) :
    ∀ (axs : List (String × Expr)) (F₀ G₀ : List Guard), Expr.leavesRecord axs = [] →
      NrSub G₀ F₀ → (∀ g ∈ F₀, g ∈ G₀) →
      ∀ a G, (a, G) ∈ leafFactsWRecord ((T.map Prod.fst).contains ·) G₀ axs →
      ∃ F, (.inl ((T.lookup a).getD default), F) ∈ Expr.leafFactsRecord F₀ (putBackRecord T P axs) ∧
        NrSub G F ∧ ∀ g ∈ F, g ∈ G
  | [], _, _, _, _, _, _, _, hm => by simp [leafFactsWRecord] at hm
  | (_, x) :: axs, F₀, G₀, hl, hG, hF, a, G, hm => by
    simp only [Expr.leavesRecord, List.append_eq_nil_iff] at hl
    simp only [leafFactsWRecord, List.mem_append] at hm
    simp only [putBackRecord, Expr.leafFactsRecord, List.mem_append]
    rcases hm with hm | hm
    · obtain ⟨F, h₁, h₂, h₃⟩ := putBack_of_leafFactsW hT htp x F₀ G₀ hl.1 hG hF a G hm
      exact ⟨F, Or.inl h₁, h₂, h₃⟩
    · obtain ⟨F, h₁, h₂, h₃⟩ := putBackRecord_of_leafFactsW hT htp axs F₀ G₀ hl.2 hG hF a G hm
      exact ⟨F, Or.inr h₁, h₂, h₃⟩

end

end

/-! ## The crate's leaves are the projection's -/

theorem lookup_of_getElem?_nodup {β : Type} : {L : List (String × β)} → (L.map Prod.fst).Nodup →
    {j : Nat} → {a : String} → {v : β} → L[j]? = some (a, v) → L.lookup a = some v
  | [], _, _, _, _, h => by simp at h
  | (k, w) :: L, hn, 0, a, v, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [List.lookup]
  | (k, w) :: L, hn, j + 1, a, v, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.map_cons, List.nodup_cons] at hn
    have hak : a ≠ k := by
      intro hak; subst hak
      exact hn.1 (List.mem_map.mpr ⟨(a, v), List.mem_of_getElem? h, rfl⟩)
    have : (a == k) = false := by simpa using hak
    simp only [List.lookup, this]
    exact lookup_of_getElem?_nodup hn.2 h

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} : {xs : List α} → {ys : List β} →
    List.Forall₂ R xs ys → {j : Nat} → {x : α} → xs[j]? = some x → ∃ y, ys[j]? = some y ∧ R x y
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hxy _, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; exact ⟨_, rfl, hxy⟩
  | _, _, .cons _ hr, j + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact forall₂_getElem? hr h

section

variable {l : Lowered} {T : List (String × Formula)} {Pr : List (String × Dogwood.Spec.Provider.Call)}

theorem temporalLookup (hT : l.leafFormulas = .ok T) (hids : (l.temporal.map (·.id)).Nodup)
    {j : Nat} {f : TemporalField} (hfj : l.temporal[j]? = some f) {φ : Formula}
    (hφ : f.condition.condition.toFormula = .ok φ) : T.lookup f.id = some φ := by
  obtain ⟨⟨a, φ'⟩, hy, ha, hφ'⟩ := forall₂_getElem? (leafFormulas_forall₂ hT) hfj
  simp only at ha hφ'
  rw [hφ] at hφ'
  cases hφ'
  subst ha
  apply lookup_of_getElem?_nodup _ hy
  rw [tids_eq hT]; exact hids

theorem providerLookup (hPr : l.providerCalls = .ok Pr) (hids : (l.providers.map (·.id)).Nodup)
    {j : Nat} {g : LoweredProviderField} (hgj : l.providers[j]? = some g) {c : Dogwood.Spec.Provider.Call}
    (hc : g.toCall = .ok c) : Pr.lookup g.id = some c := by
  obtain ⟨⟨a, c'⟩, hy, ha, hc'⟩ := forall₂_getElem? (providerCalls_forall₂ hPr) hgj
  simp only at ha hc'
  rw [hc] at hc'
  cases hc'
  subst ha
  apply lookup_of_getElem?_nodup _ hy
  rw [pids_eq hPr]; exact hids

theorem tidsHoisted (hT : l.leafFormulas = .ok T) (hn : namesOnce l = true) :
    ∀ a ∈ T.map Prod.fst, isHoistedName a = true := by
  obtain ⟨-, -, -, -, -, hhoist⟩ := namesOnce_spec hn
  rw [tids_eq hT]; intro a ha
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
  exact (hhoist f hf).1

theorem tidsNotProviders (hT : l.leafFormulas = .ok T) (hn : namesOnce l = true) :
    (T.map Prod.fst).contains "providers" = false := by
  obtain ⟨-, -, -, -, -, hhoist⟩ := namesOnce_spec hn
  rw [tids_eq hT]
  simp only [List.contains_eq_any_beq, List.any_map, Bool.eq_false_iff, ne_eq, List.any_eq_true,
    not_exists, not_and, Function.comp, beq_iff_eq]
  intro f hf h; exact (hhoist f hf).2 h.symm

/-- **Each temporal leaf of the lowered set is a temporal leaf of the projection**, in the
put-back of its rule, at a position whose facts are the crate's outside reserved heads, and among
the crate's. -/
theorem temporal_position' (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hl : policiesLeafless l = true) (hn : namesOnce l = true) (hids : (l.temporal.map (·.id)).Nodup)
    {j : Nat} {f : TemporalField} {k : Nat} {q : Dogwood.Spec.Policy}
    (hfj : l.temporal[j]? = some f) (hkj : l.temporalRules[j]? = some k) (hqk : l.policies[k]? = some q)
    {φ : Formula} (hφ : f.condition.condition.toFormula = .ok φ) :
    ∃ G F, (loweredFacts l).lookup f.id = some G ∧
      (.inl φ, F) ∈ (putBackPolicy T Pr q).toExpr.leafFacts [] ∧ NrSub G F ∧ ∀ g ∈ F, g ∈ G := by
  obtain ⟨-, -, hnd, htr, -, -⟩ := namesOnce_spec hn
  have hql := leafless_spec hl q (List.mem_of_getElem? hqk)
  have hTh := tidsHoisted hT hn
  have htp := tidsNotProviders hT hn
  have hrk : (ruleReads l)[k]? =
      some (hoistedReads (l.temporal.map (·.id)) (l.providers.map (·.id)) q.toExpr) := by
    simp [ruleReads, hqk]
  have hread := htr j f k hfj hkj
  rw [hrk, Option.getD_some] at hread
  have hin : f.id ∈ (leafFactsW ((T.map Prod.fst).contains ·) [] q.toExpr).map Prod.fst := by
    rw [leafFactsW_keys (T.map Prod.fst) (Pr.map Prod.fst) htp [] q.toExpr, mem_temporalIds,
      tids_eq hT, pids_eq hPr]
    exact hread
  obtain ⟨⟨a, G⟩, hG, ha⟩ := List.mem_map.mp hin
  simp only at ha
  subst ha
  obtain ⟨F, hF, hsub, hsub'⟩ := putBack_of_leafFactsW hTh htp q.toExpr [] [] hql
    (fun _ h _ => by cases h) (fun _ h => by cases h) _ G hG
  rw [temporalLookup hT hids hfj hφ, Option.getD_some] at hF
  refine ⟨G, F, ?_, by rw [putBackPolicy_toExpr]; exact hF, hsub, hsub'⟩
  have hWk : leafFactsW ((l.temporal.map (·.id)).contains ·) [] (Dogwood.Spec.Conditions.toExpr q.condition) =
      leafFactsW ((T.map Prod.fst).contains ·) [] q.toExpr := by
    rw [leafFactsW_policy, tids_eq hT]
  apply loweredFacts_lookup hqk (List.mem_of_getElem? hkj)
  · unfold ruleFacts
    rw [hWk]
    apply mergeFacts_lookup_once _ hG
    rw [leafFactsW_keys (T.map Prod.fst) (Pr.map Prod.fst) htp []]
    apply temporalIds_nodup
    rw [tids_eq hT, pids_eq hPr]
    exact nodup_of_getElem?_flatten hnd hrk
  · intro k'' q'' hne hq''
    unfold ruleFacts
    apply mergeFacts_lookup_not_mem
    rw [← leafFactsW_policy, ← tids_eq hT,
      leafFactsW_keys (T.map Prod.fst) (Pr.map Prod.fst) htp [] q''.toExpr, mem_temporalIds]
    intro hin'
    have hr'' : (ruleReads l)[k'']? =
        some (hoistedReads (l.temporal.map (·.id)) (l.providers.map (·.id)) q''.toExpr) := by
      simp [ruleReads, hq'']
    rw [tids_eq hT, pids_eq hPr] at hin'
    exact hne (index_unique_of_nodup_flatten hnd hr'' hrk hin' hread)

/-- **Each provider leaf of the lowered set is a provider leaf of the projection**, in the
put-back of its rule. -/
theorem provider_position' (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hl : policiesLeafless l = true) (hn : namesOnce l = true) (hids : (l.providers.map (·.id)).Nodup)
    {j : Nat} {g : LoweredProviderField} {k : Nat} {q : Dogwood.Spec.Policy}
    (hgj : l.providers[j]? = some g) (hkj : l.providerRules[j]? = some k) (hqk : l.policies[k]? = some q)
    {c : Dogwood.Spec.Provider.Call} (hc : g.toCall = .ok c) :
    ∃ F, (.inr c, F) ∈ (putBackPolicy T Pr q).toExpr.leafFacts [] := by
  obtain ⟨-, -, -, -, hpr, -⟩ := namesOnce_spec hn
  have hql := leafless_spec hl q (List.mem_of_getElem? hqk)
  have hrk : (ruleReads l)[k]? =
      some (hoistedReads (l.temporal.map (·.id)) (l.providers.map (·.id)) q.toExpr) := by
    simp [ruleReads, hqk]
  have hread := hpr j g k hgj hkj
  rw [hrk, Option.getD_some] at hread
  have hlv : Sum.inr c ∈ (putBackPolicy T Pr q).toExpr.leaves := by
    rw [putBackPolicy_toExpr, leaves_putBack _ _ _ hql]
    refine List.mem_map.mpr ⟨(false, g.id), by rw [tids_eq hT, pids_eq hPr]; exact hread, ?_⟩
    simp only [readLeaf]
    rw [providerLookup hPr hids hgj hc, Option.getD_some]
  rw [← Dogwood.Thm.leafFacts_fst []] at hlv
  obtain ⟨⟨lf, F⟩, hm, hlf⟩ := List.mem_map.mp hlv
  simp only at hlf
  subst hlf
  exact ⟨F, hm⟩

/-! ## The crate's environments are the specification's -/

/-- **A request environment the crate checks a leaf in is one the specification types it in**,
seen alike, when the leaf's metadata stays within its rule's scope. -/
theorem specEnv_of_mem (hwf : l.schema.validateWellFormed = .ok ()) (hn : namesOnce l = true)
    (happ : appliesToDeclared l = true) {targets : List (String × String)} {pc rc : ScopeConstraint}
    {q : Dogwood.Spec.Policy} (hw : withinScope l q targets pc rc = true) {e : ReqEnv}
    (he : e ∈ (targets.filterMap fun x => action? l.schema x.1 x.2).flatMap (fun x =>
      (admittedTypes l.schema x.2 .principal pc).flatMap fun p =>
        (admittedTypes l.schema x.2 .resource rc).map fun r => (⟨x.1, x.2, p, r⟩ : ReqEnv))) :
    ∃ env ∈ (specActionSchema l).environments, q.admits (specActionSchema l) env = true ∧
      ∀ C' : TypingCtx, C'.env = env → EnvView C' l.schema e := by
  obtain ⟨⟨uid, entry⟩, hx, hm⟩ := List.mem_flatMap.mp he
  obtain ⟨t, ht, hact⟩ := List.mem_filterMap.mp hx
  simp only [action?, Option.map_eq_some_iff, Prod.mk.injEq] at hact
  obtain ⟨entry', hfind, rfl, rfl⟩ := hact
  obtain ⟨p, hp, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
  simp only [admittedTypes, List.mem_filter, appliesTo] at hp hr
  have hmem : (actionUidOf t.1 t.2, entry') ∈ l.schema.acts.toList := Map.find?_mem_toList hfind
  have hne : l.schema.environments ≠ [] := by
    intro hnil
    have := Dogwood.Thm.mem_environments.mpr ⟨_, _, p, r, hmem, hp.1, hr.1, rfl⟩
    rw [hnil] at this; cases this
  obtain ⟨env, henv, hea, hep, her⟩ : ∃ env ∈ (specActionSchema l).environments,
      env.reqty.action = actionUidOf t.1 t.2 ∧ env.reqty.principal = p ∧ env.reqty.resource = r :=
    ⟨_, (mem_specEnvironments hwf hne).mpr ⟨_, _, p, r, hmem, hp.1, hr.1, rfl⟩, rfl, rfl, rfl⟩
  refine ⟨env, henv, ?_, ?_⟩
  · unfold withinScope at hw
    rw [List.all_eq_true] at hw
    have := hw env henv
    have hany : (targets.any fun (ns, id) => actionUidOf ns id == env.reqty.action) = true :=
      List.any_eq_true.mpr ⟨t, ht, by rw [hea]; exact beq_self_eq_true _⟩
    rw [hany, hep, her, hp.2, hr.2] at this
    simpa using this
  · obtain ⟨a, e', pt, rt, hfind', -, -, ha, hpt, hrt, hview⟩ := envView_of_mem hwf hne hn happ henv
    rw [hea] at ha
    rw [hep] at hpt
    rw [her] at hrt
    subst ha hpt hrt
    rw [hfind] at hfind'
    cases hfind'
    exact hview

/-! ## The specification sees the crate's environment exactly -/

theorem find?_isSome_forall₂ {α β : Type} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) (hpq : ∀ x y, R x y → p x = q y)
    (hy : (ys.find? q).isSome = true) : (xs.find? p).isSome = true := by
  rw [List.find?_isSome] at hy ⊢
  obtain ⟨y, hy, hqy⟩ := hy
  obtain ⟨x, hx, hR⟩ := forall₂_mem_right h hy
  exact ⟨x, hx, by rw [hpq x y hR]; exact hqy⟩

/-- **The specification's typing context sees the crate's environment exactly**: as `ViewAgrees`,
with the specification's facts among the crate's, when derivation finds every leaf field by its
path. -/
theorem viewExact_of {C : LeafCtx} {e : ReqEnv} {C' : TypingCtx} (hv : ViewAgrees C' C e)
    (hF : ∀ g ∈ C'.facts, g ∈ C.facts) (hS : typedSignatures C.events C.schema = .ok C'.events)
    (hres : ∀ ev ∈ C.events.events, ev.leafFields.all (fun x => lookupPath ev x.1 == .leaf) = true) :
    ViewExact C' C e := by
  have hf : List.Forall₂ (fun ev y => EventSignature.toSpec C.schema ev.signature = .ok y)
      C.events.events C'.events := by
    unfold typedSignatures at hS
    exact forall₂_map_left (List.mapM_ok_iff_forall₂.mp hS)
  refine ⟨hv, hF, ?_, ?_⟩
  · intro a k ev hev sig hsig p hp
    obtain ⟨sig', hsig', hag⟩ := hv.events a k ev hev
    rw [hsig] at hsig'
    cases hsig'
    have hft := hag.fields p
    obtain ⟨fd, hfd⟩ := Option.isSome_iff_exists.mp hp
    rw [hfd] at hft
    unfold fieldType? at hft
    simp only [Option.map_some] at hft
    obtain ⟨x, hx, -⟩ := Option.map_eq_some_iff.mp hft
    have hxm := List.mem_of_find?_eq_some hx
    have hxp := List.find?_some hx
    simp only [beq_iff_eq] at hxp
    rw [eventFields_eq] at hxm
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hxm
    rw [ef_fst] at hxp
    have hmem := List.mem_of_find?_eq_some hev
    unfold eventOf? at hev
    have := hres ev (List.mem_of_find?_eq_some hev)
    rw [List.all_eq_true] at this
    have := this y hy
    rw [hxp] at this
    simpa using this
  · intro a k hs
    unfold eventOf?
    unfold Dogwood.Spec.EventSchema.signature? at hs
    exact find?_isSome_forall₂ hf (fun ev s hes => by
      obtain ⟨h1, h2, -, -⟩ := toSpec_ok hes
      simp only [DerivedEvent.signature] at h1 h2
      simp [h1, h2]) hs

end

/-! ## Context reads -/

section

variable {T : List (String × Formula)} {P : List (String × Dogwood.Spec.Provider.Call)}
  {R : List Cedar.Spec.Attr}

theorem isContext_putBack' {e : Expr} (h : isContext e = false) :
    (putBack T P e).isContext = false := by
  rw [isContext_eq_isContext]
  exact isContext_putBack (T := T) (P := P) h

mutual

/-- **A rule whose put-back reads the request context only through its attributes reads it whole
nowhere** in the crate's lowering. -/
theorem notWhole_of_readsContext (g : Generated) :
    (x : Expr) → (putBack T P x).ReadsContext R → ∀ r ∈ contextReads g x, r.1 = false
  | .var v, h, r, hr => by
    simp only [putBack, Expr.ReadsContext] at h
    cases v <;> simp_all [contextReads]
  | .getAttr e a, h, r, hr => by
    rw [contextReads_getAttr] at hr
    split at hr
    · split at hr <;> simp_all
    · split at hr
      · split at hr <;> simp_all
      · rename_i hcp hce
        rw [putBack_getAttr, if_neg (by simp [hce]), if_neg (by simp [hcp])] at h
        simp only [Expr.ReadsContext, isContext_putBack' (Bool.eq_false_iff.mpr hce),
          Bool.false_eq_true, if_false] at h
        exact notWhole_of_readsContext g e h r hr
  | .hasAttr e a, h, r, hr => by
    rw [contextReads_hasAttr] at hr
    split at hr
    · split at hr <;> simp_all
    · rename_i hce
      simp only [putBack, Expr.ReadsContext, isContext_putBack' (Bool.eq_false_iff.mpr hce),
        Bool.false_eq_true, if_false] at h
      exact notWhole_of_readsContext g e h r hr
  | .extHasAttr e a rest, h, r, hr => by
    rw [contextReads_extHasAttr] at hr
    split at hr
    · split at hr <;> simp_all
    · rename_i hce
      simp only [putBack, Expr.ReadsContext, isContext_putBack' (Bool.eq_false_iff.mpr hce),
        Bool.false_eq_true, if_false] at h
      exact notWhole_of_readsContext g e h r hr
  | .lit _, _, r, hr | .temporal _, _, r, hr | .provider _, _, r, hr => by simp [contextReads] at hr
  | .unaryApp _ x, h, r, hr => by
    simp only [putBack, Expr.ReadsContext] at h
    simp only [contextReads] at hr
    exact notWhole_of_readsContext g x h r hr
  | .ite a b c, h, r, hr => by
    simp only [putBack, Expr.ReadsContext] at h
    simp only [contextReads, List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact notWhole_of_readsContext g a h.1 r hr
    · exact notWhole_of_readsContext g b h.2.1 r hr
    · exact notWhole_of_readsContext g c h.2.2 r hr
  | .and a b, h, r, hr | .or a b, h, r, hr | .binaryApp _ a b, h, r, hr => by
    simp only [putBack, Expr.ReadsContext] at h
    simp only [contextReads, List.mem_append] at hr
    rcases hr with hr | hr
    · exact notWhole_of_readsContext g a h.1 r hr
    · exact notWhole_of_readsContext g b h.2 r hr
  | .set xs, h, r, hr | .call _ xs, h, r, hr => by
    simp only [putBack, Expr.ReadsContext] at h
    simp only [contextReads] at hr
    exact notWholeList_of_readsContext g xs h r hr
  | .record axs, h, r, hr => by
    simp only [putBack, Expr.ReadsContext] at h
    simp only [contextReads] at hr
    exact notWholeRecord_of_readsContext g axs h r hr

theorem notWholeList_of_readsContext (g : Generated) :
    (xs : List Expr) → Expr.ReadsContextList R (putBackList T P xs) →
      ∀ r ∈ contextReadsList g xs, r.1 = false
  | [], _, r, hr => by simp [contextReadsList] at hr
  | x :: xs, h, r, hr => by
    simp only [putBackList, Expr.ReadsContextList] at h
    simp only [contextReadsList, List.mem_append] at hr
    rcases hr with hr | hr
    · exact notWhole_of_readsContext g x h.1 r hr
    · exact notWholeList_of_readsContext g xs h.2 r hr

theorem notWholeRecord_of_readsContext (g : Generated) :
    (axs : List (String × Expr)) → Expr.ReadsContextRecord R (putBackRecord T P axs) →
      ∀ r ∈ contextReadsRecord g axs, r.1 = false
  | [], _, r, hr => by simp [contextReadsRecord] at hr
  | (_, x) :: axs, h, r, hr => by
    simp only [putBackRecord, Expr.ReadsContextRecord] at h
    simp only [contextReadsRecord, List.mem_append] at hr
    rcases hr with hr | hr
    · exact notWhole_of_readsContext g x h.1 r hr
    · exact notWholeRecord_of_readsContext g axs h.2 r hr

end

end

section

variable {l : Lowered} {T : List (String × Formula)} {Pr : List (String × Dogwood.Spec.Provider.Call)}
  {sigs : Dogwood.Spec.EventSchema}

theorem leafList_ne_of_hasLeaves (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hA : Assumptions l) (h : hasLeaves l = true) : (projected l T Pr sigs).leafList ≠ [] := by
  rw [projected_leafList hT hPr hA.leafless]
  unfold hasLeaves at h
  simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  intro hnil
  have hr : ∀ r, r ∉ allReads l := fun r hr =>
    List.eq_nil_iff_forall_not_mem.mp hnil _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
  rcases h with h | h
  · obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ h
    exact hr _ (read_of_id (b := true) hA (by simpa using List.mem_map.mpr ⟨f, hf, rfl⟩))
  · obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil _ h
    exact hr _ (read_of_id (b := false) hA (by simpa using List.mem_map.mpr ⟨g, hg, rfl⟩))

/-- **The context part**: the port reports no context read, when the specification's rules read
the context only through its attributes, no rule reads a name lowering reserves, and the
authored rules the crate recorded reads of make none, nor read the context whole in a set with a
leaf. -/
theorem contextFindings_nil (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hA : Assumptions l)
    (hrc : (projected l T Pr sigs).leafList ≠ [] → ∀ p ∈ (projected l T Pr sigs).policies,
      p.toExpr.ReadsContext (projected l T Pr sigs).hoistedNames)
    (hres : ∀ r ∈ loweredReads l, r.1 = true)
    (hrec : ∀ r ∈ l.contextReads, r.1 = true ∧ hasLeaves l = false) : contextFindings l = [] := by
  unfold contextFindings
  apply List.filterMap_eq_nil_iff.mpr
  intro ⟨w, a⟩ hr'
  rcases mem_validate_allReads.mp hr' with hr | hr
  case inr =>
    obtain ⟨hw, hlv⟩ := hrec _ hr
    simp only at hw
    subst hw
    simp [hlv]
  have hw := hres _ hr
  simp only at hw
  subst hw
  by_cases hlv : hasLeaves l = true
  · exfalso
    unfold loweredReads at hr
    obtain ⟨q, hq, hm⟩ := List.mem_flatMap.mp hr
    have hrq := hrc (leafList_ne_of_hasLeaves hT hPr hA hlv) (putBackPolicy T Pr q)
      (List.mem_map.mpr ⟨q, hq, rfl⟩)
    rw [putBackPolicy_toExpr] at hrq
    have := notWhole_of_readsContext _ q.toExpr hrq _ hm
    cases this
  · simp [hlv]

/-! ## The port's parts -/

theorem mapM_ok_of_forall {α β ε : Type} {f : α → Except ε β} :
    {xs : List α} → (∀ x ∈ xs, ∃ y, f x = .ok y) → ∃ ys, xs.mapM f = .ok ys
  | [], _ => ⟨[], rfl⟩
  | x :: xs, h => by
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := mapM_ok_of_forall (xs := xs) (fun x' hx' => h x' (by simp [hx']))
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys, bind, Except.bind, pure, Except.pure]⟩

/-- The port finds every leaf's specification form when the projection does. -/
theorem leafFormulas_ok (hT : l.leafFormulas = .ok T) : ∃ leaves, leafFormulas l = .ok leaves := by
  unfold leafFormulas
  apply mapM_ok_of_forall
  intro f hf
  obtain ⟨p, -, -, hφ⟩ := forall₂_mem_left (leafFormulas_forall₂ hT) hf
  rw [hφ]
  exact ⟨(f, p.2), rfl⟩

theorem mem_leafFormulas {leaves : List (TemporalField × Formula)} (hL : leafFormulas l = .ok leaves)
    {x : TemporalField × Formula} (hx : x ∈ leaves) :
    x.1 ∈ l.temporal ∧ x.1.condition.condition.toFormula = .ok x.2 := by
  unfold leafFormulas at hL
  obtain ⟨f, hf, hfx⟩ := forall₂_mem_right (List.mapM_ok_iff_forall₂.mp hL) hx
  cases hφ : f.condition.condition.toFormula with
  | error e => rw [hφ] at hfx; cases hfx
  | ok φ =>
    rw [hφ] at hfx
    simp only [pure, Except.pure, Except.ok.injEq] at hfx
    subst hfx
    exact ⟨hf, hφ⟩

/-- Dropping repeated keys keeps elements of the list. -/
theorem mem_of_mem_firstOccurrencesBy {α : Type} {key : α → String} {x : α} :
    ∀ {xs acc : List α}, x ∈ xs.foldl (fun acc y => if acc.any (key · == key y) then acc else acc ++ [y]) acc →
      x ∈ acc ∨ x ∈ xs
  | [], _, h => Or.inl h
  | y :: ys, acc, h => by
    simp only [List.foldl_cons] at h
    rcases mem_of_mem_firstOccurrencesBy h with h | h
    · split at h
      · exact Or.inl h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · simp only [List.mem_singleton] at h; subst h; exact Or.inr (by simp)
    · exact Or.inr (by simp [h])

/-- The provider dialect's fallback findings are warnings. -/
theorem providerWarnings_warning {l : Lowered} :
    ∀ f ∈ providerWarnings l, f.warning = true := by
  intro f hf
  unfold providerWarnings providerWarningsLocated at hf
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hf
  obtain ⟨_, _, hm⟩ := List.mem_flatMap.mp hx
  unfold firstOccurrencesBy at hm
  rcases mem_of_mem_firstOccurrencesBy hm with hm | hm
  · cases hm
  · obtain ⟨_, _, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hm
    rfl

/-- **The port accepts when each of its parts reports nothing**: only the warnings (of a
provider type that falls back to `String`, and of arithmetic) may remain. -/
theorem validate_of_parts {leaves : List (TemporalField × Formula)} (hL : leafFormulas l = .ok leaves)
    (hcedar : cedarFindings l = []) (hschema : schemaFindings l = []) (hctx : contextFindings l = [])
    (htemp : ∀ x ∈ leaves, leafFindings (leafCtx l (loweredFacts l) x.1) x.2 = [])
    (hprovs : ∀ g ∈ l.providers, providerLeafFindings l.schema g = []) :
    ∃ fs, validate l = .ok fs ∧ ∀ f ∈ fs, f.warning = true := by
  unfold validate
  rw [hL]
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, exists_eq_left']
  intro f hf
  simp only [hcedar, hschema, hctx, List.nil_append, List.mem_append, List.mem_flatMap] at hf
  rcases hf with (⟨x, hx, hm⟩ | ⟨g, hg, hm⟩) | hm
  · rw [htemp x hx] at hm; cases hm
  · rw [hprovs g hg] at hm; cases hm
  · rcases hm with hm | hm
    · exact providerWarnings_warning f hm
    · split at hm
      · simp only [List.mem_singleton] at hm; subst hm; rfl
      · cases hm

end

end Dogwood.Thm.Frontend
