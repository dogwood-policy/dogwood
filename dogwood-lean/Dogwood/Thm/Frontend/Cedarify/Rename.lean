import Dogwood.Thm.Frontend.Cedarify.Names

/-!
# The renaming, as a function on lowered rules

`cedarifyFull_lowered_rename` says that the crate's rules and the specification's lowering are
the same lowering with different references for the leaves. When the rules read the context
only through attributes other than the specification's leaf attributes (the `readsContext`
clause of `PolicySet.Valid`), the crate's rules are a function of the specification's lowering:
replace each access `context.leafAttr j` by the crate's `j`-th reference
(`cedarifyFull_relabel`). Without the clause the renaming would also rewrite a `context.leafAttr j`
the rule itself reads.
-/

namespace Dogwood.Thm.Frontend.Cedarify

open Dogwood.Spec
open Dogwood.Frontend
open Dogwood.Frontend.Cedarify
open Cedar.Spec (Attr)

mutual

/-- Replace each attribute access `context.a` with `ρ a`, where it is defined. -/
def relabel (ρ : Attr → Option Cedar.Spec.Expr) : Cedar.Spec.Expr → Cedar.Spec.Expr
  | .lit p => .lit p
  | .var v => .var v
  | .ite a b c => .ite (relabel ρ a) (relabel ρ b) (relabel ρ c)
  | .and a b => .and (relabel ρ a) (relabel ρ b)
  | .or a b => .or (relabel ρ a) (relabel ρ b)
  | .unaryApp op a => .unaryApp op (relabel ρ a)
  | .binaryApp op a b => .binaryApp op (relabel ρ a) (relabel ρ b)
  | .getAttr e a =>
    match e with
    | .var .context => (ρ a).getD (.getAttr (.var .context) a)
    | e => .getAttr (relabel ρ e) a
  | .hasAttr e a => .hasAttr (relabel ρ e) a
  | .extHasAttr e a as => .extHasAttr (relabel ρ e) a as
  | .set xs => .set (relabelList ρ xs)
  | .record axs => .record (relabelRecord ρ axs)
  | .call f xs => .call f (relabelList ρ xs)

def relabelList (ρ : Attr → Option Cedar.Spec.Expr) : List Cedar.Spec.Expr → List Cedar.Spec.Expr
  | [] => []
  | x :: xs => relabel ρ x :: relabelList ρ xs

def relabelRecord (ρ : Attr → Option Cedar.Spec.Expr) :
    List (Attr × Cedar.Spec.Expr) → List (Attr × Cedar.Spec.Expr)
  | [] => []
  | (a, x) :: axs => (a, relabel ρ x) :: relabelRecord ρ axs

end

/-- `relabel`, on a policy's conditions. -/
def relabelPolicy (ρ : Attr → Option Cedar.Spec.Expr) (p : Cedar.Spec.Policy) : Cedar.Spec.Policy :=
  { p with condition := p.condition.map fun c => ⟨c.kind, relabel ρ c.body⟩ }

/-- The renaming from the specification's leaf attributes, numbered below `n`, to the references
`r`. -/
def leafRenaming (n : Nat) (r : Nat → Cedar.Spec.Expr) (a : Attr) : Option Cedar.Spec.Expr :=
  ((List.range n).find? fun j => leafAttr j == a).map r

theorem leafRenaming_leafAttr {n j : Nat} (r : Nat → Cedar.Spec.Expr) (hj : j < n) :
    leafRenaming n r (leafAttr j) = some (r j) := by
  simp only [leafRenaming]
  cases h : (List.range n).find? fun i => leafAttr i == leafAttr j with
  | none =>
    have := List.find?_eq_none.mp h j (List.mem_range.mpr hj)
    simp at this
  | some i =>
    have := List.find?_some h
    simp only [beq_iff_eq] at this
    rw [leafAttr_inj this]
    rfl

theorem leafRenaming_none {n : Nat} {a : Attr} (r : Nat → Cedar.Spec.Expr)
    (ha : a ∉ (List.range n).map leafAttr) : leafRenaming n r a = none := by
  simp only [leafRenaming, Option.map_eq_none_iff, List.find?_eq_none, beq_iff_eq]
  intro j hj he
  exact ha (List.mem_map.mpr ⟨j, hj, he⟩)

/-! ## Lowering's numbering -/

mutual

theorem lowerVia_snd (r : Nat → Cedar.Spec.Expr) :
    (x : Expr) → (k : Nat) → (x.lowerVia r k).2 = k + x.leaves.length
  | .lit _, k | .var _, k => by simp [Expr.lowerVia, Expr.leaves]
  | .ite a b c, k => by
    simp only [Expr.lowerVia, Expr.leaves, List.length_append, lowerVia_snd r c, lowerVia_snd r b,
      lowerVia_snd r a]
    omega
  | .and a b, k | .or a b, k | .binaryApp _ a b, k => by
    simp only [Expr.lowerVia, Expr.leaves, List.length_append, lowerVia_snd r b, lowerVia_snd r a]
    omega
  | .unaryApp _ a, k | .getAttr a _, k | .hasAttr a _, k | .extHasAttr a _ _, k => by
    simp only [Expr.lowerVia, Expr.leaves, lowerVia_snd r a]
  | .set xs, k | .call _ xs, k => by simp only [Expr.lowerVia, Expr.leaves, lowerListVia_snd r xs]
  | .record axs, k => by simp only [Expr.lowerVia, Expr.leaves, lowerRecordVia_snd r axs]
  | .temporal _, k | .provider _, k => by simp [Expr.lowerVia, Expr.leaves]

theorem lowerListVia_snd (r : Nat → Cedar.Spec.Expr) : (xs : List Expr) → (k : Nat) →
    (Expr.lowerListVia r k xs).2 = k + (Expr.leavesList xs).length
  | [], k => by simp [Expr.lowerListVia, Expr.leavesList]
  | x :: xs, k => by
    simp only [Expr.lowerListVia, Expr.leavesList, List.length_append, lowerListVia_snd r xs,
      lowerVia_snd r x]
    omega

theorem lowerRecordVia_snd (r : Nat → Cedar.Spec.Expr) : (axs : List (Attr × Expr)) → (k : Nat) →
    (Expr.lowerRecordVia r k axs).2 = k + (Expr.leavesRecord axs).length
  | [], k => by simp [Expr.lowerRecordVia, Expr.leavesRecord]
  | (_, x) :: axs, k => by
    simp only [Expr.lowerRecordVia, Expr.leavesRecord, List.length_append,
      lowerRecordVia_snd r axs, lowerVia_snd r x]
    omega

end

/-- A lowered expression is the variable `context` only when the expression is: no reference is
a variable. -/
theorem lowerVia_fst_var {r : Nat → Cedar.Spec.Expr} (hr : ∀ j v, r j ≠ .var v) {v : Cedar.Spec.Var} :
    (x : Expr) → (k : Nat) → (x.lowerVia r k).1 = .var v → x = .var v
  | .var _, _, h => by simpa [Expr.lowerVia] using h
  | .temporal _, k, h | .provider _, k, h => absurd h (by simpa [Expr.lowerVia] using hr k v)
  | .lit _, _, h | .ite _ _ _, _, h | .and _ _, _, h | .or _ _, _, h | .unaryApp _ _, _, h
  | .binaryApp _ _ _, _, h | .getAttr _ _, _, h | .hasAttr _ _, _, h | .extHasAttr _ _ _, _, h
  | .set _, _, h | .record _, _, h | .call _ _, _, h => by simp [Expr.lowerVia] at h

theorem specRef_ne_var (j : Nat) (v : Cedar.Spec.Var) : specRef j ≠ .var v := by
  simp [specRef]

/-! ## Renaming the specification's lowering -/

variable {n : Nat} {r : Nat → Cedar.Spec.Expr}

mutual

theorem relabel_lowerVia (hr : ∀ j v, r j ≠ .var v) :
    (x : Expr) → (k : Nat) → x.ReadsContext ((List.range n).map leafAttr) →
    k + x.leaves.length ≤ n →
    relabel (leafRenaming n r) (x.lowerVia specRef k).1 = (x.lowerVia r k).1
  | .lit _, _, _, _ => rfl
  | .var _, _, _, _ => rfl
  | .ite a b c, k, h, hn => by
    simp only [Expr.ReadsContext] at h
    simp only [Expr.leaves, List.length_append] at hn
    simp only [Expr.lowerVia, relabel, lowerVia_snd]
    rw [relabel_lowerVia hr a k h.1 (by omega), relabel_lowerVia hr b _ h.2.1 (by omega),
      relabel_lowerVia hr c _ h.2.2 (by omega)]
  | .and a b, k, h, hn => by
    simp only [Expr.ReadsContext] at h
    simp only [Expr.leaves, List.length_append] at hn
    simp only [Expr.lowerVia, relabel, lowerVia_snd]
    rw [relabel_lowerVia hr a k h.1 (by omega), relabel_lowerVia hr b _ h.2 (by omega)]
  | .or a b, k, h, hn => by
    simp only [Expr.ReadsContext] at h
    simp only [Expr.leaves, List.length_append] at hn
    simp only [Expr.lowerVia, relabel, lowerVia_snd]
    rw [relabel_lowerVia hr a k h.1 (by omega), relabel_lowerVia hr b _ h.2 (by omega)]
  | .binaryApp _ a b, k, h, hn => by
    simp only [Expr.ReadsContext] at h
    simp only [Expr.leaves, List.length_append] at hn
    simp only [Expr.lowerVia, relabel, lowerVia_snd]
    rw [relabel_lowerVia hr a k h.1 (by omega), relabel_lowerVia hr b _ h.2 (by omega)]
  | .unaryApp _ a, k, h, hn => by
    simp only [Expr.ReadsContext] at h
    simp only [Expr.leaves] at hn
    simp only [Expr.lowerVia, relabel]
    rw [relabel_lowerVia hr a k h hn]
  | .hasAttr a x, k, h, hn => by
    simp only [Expr.leaves] at hn
    simp only [Expr.lowerVia, relabel]
    by_cases hc : a.isContext
    · cases a <;> simp [Expr.isContext] at hc
      next v => cases v <;> simp at hc; rfl
    · simp only [Expr.ReadsContext, hc, Bool.false_eq_true, ↓reduceIte] at h
      rw [relabel_lowerVia hr a k h hn]
  | .extHasAttr a x xs, k, h, hn => by
    simp only [Expr.leaves] at hn
    simp only [Expr.lowerVia, relabel]
    by_cases hc : a.isContext
    · cases a <;> simp [Expr.isContext] at hc
      next v => cases v <;> simp at hc; rfl
    · simp only [Expr.ReadsContext, hc, Bool.false_eq_true, ↓reduceIte] at h
      rw [relabel_lowerVia hr a k h hn]
  | .getAttr a x, k, h, hn => by
    simp only [Expr.leaves] at hn
    simp only [Expr.lowerVia]
    by_cases hc : a.isContext
    · cases a <;> simp [Expr.isContext] at hc
      next v =>
        cases v <;> simp at hc
        simp only [Expr.ReadsContext, Expr.isContext, ↓reduceIte] at h
        simp [Expr.lowerVia, relabel, leafRenaming_none r h]
    · simp only [Expr.ReadsContext, hc, Bool.false_eq_true, ↓reduceIte] at h
      have ih := relabel_lowerVia hr a k h hn
      cases ha : (a.lowerVia specRef k).1 with
      | var v =>
        have := lowerVia_fst_var specRef_ne_var a k ha
        subst this
        cases v <;> simp_all [Expr.isContext, Expr.lowerVia] <;> rfl
      | _ => simp_all [relabel]
  | .set xs, k, h, hn => by
    simp only [Expr.ReadsContext] at h
    simp only [Expr.leaves] at hn
    simp only [Expr.lowerVia, relabel]
    rw [relabelList_lowerVia hr xs k h hn]
  | .call _ xs, k, h, hn => by
    simp only [Expr.ReadsContext] at h
    simp only [Expr.leaves] at hn
    simp only [Expr.lowerVia, relabel]
    rw [relabelList_lowerVia hr xs k h hn]
  | .record axs, k, h, hn => by
    simp only [Expr.ReadsContext] at h
    simp only [Expr.leaves] at hn
    simp only [Expr.lowerVia, relabel]
    rw [relabelRecord_lowerVia hr axs k h hn]
  | .temporal _, k, _, hn | .provider _, k, _, hn => by
    simp only [Expr.leaves, List.length_singleton] at hn
    simp [Expr.lowerVia, specRef, relabel, leafRenaming_leafAttr r (show k < n by omega)]

theorem relabelList_lowerVia (hr : ∀ j v, r j ≠ .var v) :
    (xs : List Expr) → (k : Nat) → Expr.ReadsContextList ((List.range n).map leafAttr) xs →
    k + (Expr.leavesList xs).length ≤ n →
    relabelList (leafRenaming n r) (Expr.lowerListVia specRef k xs).1 = (Expr.lowerListVia r k xs).1
  | [], _, _, _ => rfl
  | x :: xs, k, h, hn => by
    simp only [Expr.ReadsContextList] at h
    simp only [Expr.leavesList, List.length_append] at hn
    simp only [Expr.lowerListVia, relabelList, lowerVia_snd]
    rw [relabel_lowerVia hr x k h.1 (by omega), relabelList_lowerVia hr xs _ h.2 (by omega)]

theorem relabelRecord_lowerVia (hr : ∀ j v, r j ≠ .var v) :
    (axs : List (Attr × Expr)) → (k : Nat) →
    Expr.ReadsContextRecord ((List.range n).map leafAttr) axs →
    k + (Expr.leavesRecord axs).length ≤ n →
    relabelRecord (leafRenaming n r) (Expr.lowerRecordVia specRef k axs).1 =
      (Expr.lowerRecordVia r k axs).1
  | [], _, _, _ => rfl
  | (_, x) :: axs, k, h, hn => by
    simp only [Expr.ReadsContextRecord] at h
    simp only [Expr.leavesRecord, List.length_append] at hn
    simp only [Expr.lowerRecordVia, relabelRecord, lowerVia_snd]
    rw [relabel_lowerVia hr x k h.1 (by omega), relabelRecord_lowerVia hr axs _ h.2 (by omega)]

end

/-! ## Rules -/

theorem condition_leaves (c : Condition) : c.toExpr.leaves = c.body.leaves := by
  obtain ⟨kind, body⟩ := c
  cases kind <;> simp [Condition.toExpr, Expr.leaves]

theorem conditions_leaves : (cs : Conditions) →
    (Conditions.toExpr cs).leaves = cs.flatMap (·.body.leaves)
  | [] => by simp [Conditions.toExpr, Expr.leaves]
  | [c] => by
    rw [show Conditions.toExpr [c] = c.toExpr from rfl, condition_leaves]
    simp
  | c :: d :: cs => by
    rw [conditions_toExpr_cons c (d :: cs) (by simp)]
    simp only [Expr.leaves, condition_leaves, conditions_leaves (d :: cs), List.flatMap_cons]

theorem conditions_readsContext {R : List Attr} : (cs : Conditions) →
    (Conditions.toExpr cs).ReadsContext R → ∀ c ∈ cs, c.body.ReadsContext R
  | [], _, c, hc => by simp at hc
  | [c], h, c', hc' => by
    simp only [List.mem_singleton] at hc'
    subst hc'
    rw [show Conditions.toExpr [c'] = c'.toExpr from rfl] at h
    obtain ⟨kind, body⟩ := c'
    cases kind
    · exact h
    · simpa [Condition.toExpr, Expr.ReadsContext] using h
  | c :: d :: cs, h, c', hc' => by
    rw [conditions_toExpr_cons c (d :: cs) (by simp)] at h
    simp only [Expr.ReadsContext] at h
    rcases List.mem_cons.mp hc' with rfl | hc'
    · obtain ⟨kind, body⟩ := c'
      cases kind
      · exact h.1
      · simpa [Condition.toExpr, Expr.ReadsContext] using h.1
    · exact conditions_readsContext (d :: cs) h.2 c' hc'

theorem policy_leaves (p : Policy) : p.toExpr.leaves = p.condition.flatMap (·.body.leaves) := by
  simp [Policy.toExpr, Expr.leaves, leaves_ofCedar, conditions_leaves]

theorem relabelConditions_lowerVia (hr : ∀ j v, r j ≠ .var v) : (cs : Conditions) → (k : Nat) →
    (∀ c ∈ cs, c.body.ReadsContext ((List.range n).map leafAttr)) →
    k + (cs.flatMap (·.body.leaves)).length ≤ n →
    (Conditions.lowerVia specRef k cs).1.map (fun c => ⟨c.kind, relabel (leafRenaming n r) c.body⟩) =
      (Conditions.lowerVia r k cs).1
  | [], _, _, _ => rfl
  | c :: cs, k, h, hn => by
    simp only [List.flatMap_cons, List.length_append] at hn
    simp only [Conditions.lowerVia, List.map_cons, lowerVia_snd]
    rw [relabel_lowerVia hr c.body k (h c (by simp)) (by omega),
      relabelConditions_lowerVia hr cs _ (fun c' hc' => h c' (by simp [hc'])) (by omega)]

theorem conditions_lowerVia_snd (r : Nat → Cedar.Spec.Expr) : (cs : Conditions) → (k : Nat) →
    (Conditions.lowerVia r k cs).2 = k + (cs.flatMap (·.body.leaves)).length
  | [], k => by simp [Conditions.lowerVia]
  | c :: cs, k => by
    simp only [Conditions.lowerVia, conditions_lowerVia_snd r cs, lowerVia_snd, List.flatMap_cons,
      List.length_append]
    omega

theorem relabelPolicies_lowerVia (hr : ∀ j v, r j ≠ .var v) : (ps : Policies) → (k : Nat) →
    (∀ p ∈ ps, p.toExpr.ReadsContext ((List.range n).map leafAttr)) →
    k + (ps.flatMap (·.toExpr.leaves)).length ≤ n →
    (Policies.lowerVia specRef k ps).1.map (relabelPolicy (leafRenaming n r)) =
      (Policies.lowerVia r k ps).1
  | [], _, _, _ => rfl
  | p :: ps, k, h, hn => by
    simp only [List.flatMap_cons, List.length_append, policy_leaves] at hn
    have hp := h p (by simp)
    simp only [Policy.toExpr, Expr.ReadsContext] at hp
    simp only [Policies.lowerVia, List.map_cons, Policy.lowerVia, relabelPolicy,
      conditions_lowerVia_snd]
    rw [relabelConditions_lowerVia hr p.condition k (conditions_readsContext _ hp.2.2.2) (by omega)]
    have := relabelPolicies_lowerVia hr ps (k + (p.condition.flatMap (·.body.leaves)).length)
      (fun q hq => h q (by simp [hq])) (by simp only [policy_leaves] at hn ⊢; omega)
    rw [this]

theorem leafRef_ne_var {w : WithSpec} {l : Leaf} {ref : Cedar.Spec.Expr} (h : leafRef w l ref)
    (v : Cedar.Spec.Var) : ref ≠ .var v := by
  cases l with
  | inl _ => obtain ⟨f, -, rfl, -⟩ := h; simp [temporalRef]
  | inr _ => obtain ⟨f, -, rfl, -⟩ := h; simp [providerRef]

/-- **The renaming.** When the rules in the specification's form read the context only through
attributes other than their leaves' (the `readsContext` clause of `PolicySet.Valid`), the crate's
Cedar policies are the specification's lowering with each access `context.leafAttr j` replaced by
the crate's reference to the `j`-th leaf. -/
theorem cedarifyFull_relabel {ps : Surface.PolicySet} {frag : CedarSchema.Fragment}
    {decls : Option ProviderDecls.Declarations} {d : Option String} {ids : Option (List String)}
    {w : WithSpec} (h : cedarifyFull ps frag decls d ids = .ok w) (P : PolicySet)
    (hP : P.policies = w.spec) (hr : ∀ p ∈ P.policies, p.toExpr.ReadsContext P.hoistedNames) :
    w.cedar = P.lowered.map (relabelPolicy (leafRenaming P.leafList.length (refAt w.refs))) := by
  have hl := cedarifyFull_lowered h
  have hne : ∀ j v, refAt w.refs j ≠ .var v := by
    intro j v
    simp only [refAt]
    cases hj : w.refs[j]? with
    | none => simp [List.getD_eq_getElem?_getD, hj]
    | some ref =>
      simp only [List.getD_eq_getElem?_getD, hj, Option.getD_some]
      obtain ⟨l, -, hlr⟩ := Zips.mem hl.2.1 ref (List.mem_of_getElem? hj)
      exact leafRef_ne_var hlr v
  rw [lowered_eq_lowerVia, hP]
  rw [hP] at hr
  have := relabelPolicies_lowerVia (n := P.leafList.length) hne w.spec 0
    (by simpa [PolicySet.hoistedNames] using hr)
    (by simp [PolicySet.leafList, hP])
  rw [this, hl.1]

end Dogwood.Thm.Frontend.Cedarify
