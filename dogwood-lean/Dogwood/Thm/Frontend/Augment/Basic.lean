import Dogwood.Frontend.Augment

/-!
# Lemmas about the fragment edits of augmentation

How a lookup in a key-ordered list sees `insertKey`, how `getNs`, `actionAt` and `contextAt` see
`setNs` and `setAction`, and an induction principle for `List.foldlM` in `Except`.
-/

namespace Dogwood.Frontend.Augment

open CedarSchema

/-! ## Key-ordered lists -/

theorem lookup_cons_ite {α β : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (k k' : α) (v : β)
    (l : List (α × β)) : ((k, v) :: l).lookup k' = if k' = k then some v else l.lookup k' := by
  by_cases h : k' = k
  · subst h; simp [List.lookup]
  · have hb : (k' == k) = false := by simp [h]
    simp [List.lookup, hb, h]

theorem lookup_cons_eq {α : Type} (k k' : String) (v : α) (l : List (String × α)) :
    ((k, v) :: l).lookup k' = if k' = k then some v else l.lookup k' :=
  lookup_cons_ite k k' v l

/-- A lookup after `insertKey` finds the inserted value at its key, and the old value elsewhere. -/
theorem lookup_insertKey {α : Type} (k k' : String) (v : α) (l : List (String × α)) :
    (insertKey k v l).lookup k' = if k' = k then some v else l.lookup k' := by
  induction l with
  | nil => simp [insertKey, lookup_cons_eq]
  | cons hd tl ih =>
    obtain ⟨k1, v1⟩ := hd
    unfold insertKey
    by_cases hlt : k < k1
    · simp only [hlt, if_true, lookup_cons_eq]
    · simp only [hlt, if_false]
      by_cases heq : k = k1
      · subst heq
        simp only [beq_self_eq_true, if_true, lookup_cons_eq]
        by_cases h : k' = k <;> simp [h]
      · have hne : (k == k1) = false := by simp [heq]
        simp only [hne, Bool.false_eq_true, if_false, lookup_cons_eq, ih]
        by_cases h1 : k' = k1
        · subst h1
          have : ¬ k' = k := fun h => heq h.symm
          simp [this]
        · simp [h1]

theorem lookup_insertKey_self {α : Type} (k : String) (v : α) (l : List (String × α)) :
    (insertKey k v l).lookup k = some v := by
  simp [lookup_insertKey]

theorem lookup_insertKey_ne {α : Type} {k k' : String} (v : α) (l : List (String × α))
    (h : k' ≠ k) : (insertKey k v l).lookup k' = l.lookup k' := by
  simp [lookup_insertKey, h]

/-! ## Namespaces and actions -/

theorem lookup_setNs (f : Fragment) (k k' : Option String) (nd : NamespaceDef) :
    (setNs f k nd).lookup k' =
      if k' = k then (if (f.lookup k).isSome then some nd else none) else f.lookup k' := by
  induction f with
  | nil => simp [setNs, List.lookup]
  | cons hd tl ih =>
    obtain ⟨k1, nd1⟩ := hd
    simp only [setNs, List.map_cons, beq_iff_eq] at ih ⊢
    have e1 : ∀ (tl' : List (Option String × NamespaceDef)),
        ((if k1 = k then (k1, nd) else (k1, nd1)) :: tl') = ((k1, if k1 = k then nd else nd1) :: tl') := by
      intro tl'; split <;> rfl
    rw [e1, lookup_cons_ite, lookup_cons_ite, lookup_cons_ite, ih]
    by_cases h1 : k1 = k
    · subst h1
      by_cases h2 : k' = k1
      · subst h2; simp
      · simp [h2]
    · by_cases h2 : k' = k
      · have h3 : ¬ k' = k1 := fun h => h1 (h.symm.trans h2)
        have h4 : ¬ k = k1 := fun h => h1 h.symm
        rw [if_neg h3, if_pos h2, if_pos h2, if_neg h4]
      · by_cases h3 : k' = k1
        · subst h3; simp [h1]
        · simp [h2, h3]

theorem getNs_setNs (f : Fragment) (k k' : Option String) (nd : NamespaceDef) :
    getNs (setNs f k nd) k' =
      if k' = k then (if (getNs f k).isSome then some nd else none) else getNs f k' :=
  lookup_setNs f k k' nd

theorem getNs_setNs_self {f : Fragment} {k : Option String} {nd nd₀ : NamespaceDef}
    (h : getNs f k = some nd₀) : getNs (setNs f k nd) k = some nd := by
  simp [getNs_setNs, h]

theorem getNs_setNs_ne {f : Fragment} {k k' : Option String} (nd : NamespaceDef) (h : k' ≠ k) :
    getNs (setNs f k nd) k' = getNs f k' := by
  simp [getNs_setNs, h]

theorem actionAt_setAction {f : Fragment} {k : Option String} {id : String} {a : ActionDef}
    {nd : NamespaceDef} (h : getNs f k = some nd) (k' : Option String) (id' : String) :
    actionAt (setAction f k id a) k' id' =
      if k' = k ∧ id' = id then some a else actionAt f k' id' := by
  simp only [setAction, h, actionAt]
  by_cases hk : k' = k
  · subst hk
    rw [getNs_setNs_self h, h]
    by_cases hi : id' = id
    · subst hi; simp [lookup_insertKey]
    · simp [lookup_insertKey, hi]
  · rw [getNs_setNs_ne _ hk]
    simp [hk]

theorem contextAt_setAction {f : Fragment} {k : Option String} {id : String} {a : ActionDef}
    {nd : NamespaceDef} (h : getNs f k = some nd) (k' : Option String) (id' : String) :
    contextAt (setAction f k id a) k' id' =
      if k' = k ∧ id' = id then a.appliesTo.map (·.context) else contextAt f k' id' := by
  simp only [contextAt, actionAt_setAction h]
  split <;> simp

/-- Replacing a namespace by one with the same actions keeps every action. -/
theorem actionAt_setNs_of_actions {f : Fragment} {k : Option String} {nd nd' : NamespaceDef}
    (h : getNs f k = some nd) (ha : nd'.actions = nd.actions) (k' : Option String) (id : String) :
    actionAt (setNs f k nd') k' id = actionAt f k' id := by
  simp only [actionAt]
  by_cases hk : k' = k
  · subst hk; rw [getNs_setNs_self h, h]; simp [ha]
  · rw [getNs_setNs_ne _ hk]

theorem contextAt_setNs_of_actions {f : Fragment} {k : Option String} {nd nd' : NamespaceDef}
    (h : getNs f k = some nd) (ha : nd'.actions = nd.actions) (k' : Option String) (id : String) :
    contextAt (setNs f k nd') k' id = contextAt f k' id := by
  simp only [contextAt, actionAt_setNs_of_actions h ha]

/-! ## Folds in `Except` -/

/-- An invariant of a successful `foldlM`, indexed by the elements folded so far. -/
theorem foldlM_ok_induction {α β ε : Type} {step : β → α → Except ε β} {P : β → List α → Prop}
    (xs : List α) {init r : β} (h0 : P init [])
    (hstep : ∀ acc pre x acc', P acc pre → step acc x = .ok acc' → P acc' (pre ++ [x]))
    (h : xs.foldlM step init = .ok r) : P r xs := by
  suffices ∀ (ys pre : List α) (acc : β), P acc pre → ys.foldlM step acc = .ok r → P r (pre ++ ys) by
    simpa using this xs [] init h0 h
  intro ys
  induction ys with
  | nil => intro pre acc hP h; simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; simpa using hP
  | cons y ys ih =>
    intro pre acc hP h
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · exact absurd h (by simp)
    · rename_i acc' hacc
      have := ih (pre ++ [y]) acc' (hstep acc pre y acc' hP hacc) h
      simpa using this

/-- An invariant that every step of a successful `foldlM` preserves holds of its result. -/
theorem foldlM_ok_invariant {α β ε : Type} {step : β → α → Except ε β} {P : β → Prop}
    (xs : List α) {init r : β} (h0 : P init)
    (hstep : ∀ acc x acc', x ∈ xs → P acc → step acc x = .ok acc' → P acc')
    (h : xs.foldlM step init = .ok r) : P r := by
  have := foldlM_ok_induction (P := fun b pre => (∃ ys, pre ++ ys = xs) → P b) xs
    (fun _ => h0)
    (fun acc pre x acc' hP hs ⟨ys, hys⟩ => hstep acc x acc' (by rw [← hys]; simp)
      (hP ⟨x :: ys, by rw [← hys]; simp⟩) hs) h
  exact this ⟨[], by simp⟩

theorem bind_eq_ok {α β ε : Type} {x : Except ε α} {k : α → Except ε β} {r : β} :
    (x >>= k) = .ok r ↔ ∃ a, x = .ok a ∧ k a = .ok r := by
  cases x <;> simp [bind, Except.bind]

end Dogwood.Frontend.Augment
