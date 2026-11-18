import Dogwood.Thm.Frontend.Cedarify.Hoisting
import Dogwood.Thm.Conservative

/-!
# Cedarify's rules are the specification's lowering of its rules in the specification's form

`cedarifyFull_lowered`: the crate's Cedar policies are `Policies.lowerVia` of the rules in the
specification's form, with the crate's references (`WithSpec.refs`) for the leaves, numbered over
the whole set as the specification numbers them; each reference is the crate's reference to a
hoisted field of the leaf's kind; and the crate-named policies cedarify returns are those Cedar
policies. With `lowered_eq_lowerVia`, the crate's policies are the specification's lowering
(`PolicySet.lowered`) with the reference to the `j`-th leaf, `context.leafAttr j`, replaced by the
crate's `j`-th reference (`cedarifyFull_lowered_rename`). When every leaf has a form in the
specification (`cedarifyWithSpec`), each reference's field holds that leaf
(`cedarifyWithSpec_leaves`).
-/

namespace Dogwood.Thm.Frontend.Cedarify

open Dogwood.Spec
open Dogwood.Frontend
open Dogwood.Frontend.Cedarify

/-! ## Clauses and rules -/

theorem lowerClauses_lowers (env : Env) : (cs : List Surface.Cond) → (s : St) → (os : List Out) →
    (s' : St) → lowerClauses env cs s = .ok (os, s') →
    Hoists env s s' ∧ ∀ o ∈ os, LowersTo (LeafOK s') o.spec o.cedar o.refs
  | [], s, os, s', h => by
    simp only [lowerClauses, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.refl _, by simp⟩
  | c :: cs, s, os, s', h => by
    simp only [lowerClauses] at h
    cases hc : lowerExpr env c.body s with
    | error _ => simp [hc, bind, Except.bind] at h
    | ok p =>
      obtain ⟨o₁, s₁⟩ := p
      cases hcs : lowerClauses env cs s₁ with
      | error _ => simp [hc, hcs, bind, Except.bind] at h
      | ok q =>
        obtain ⟨os₂, s₂⟩ := q
        simp [hc, hcs, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hs₁, hl₁⟩ := lowerExpr_lowers env c.body s o₁ s₁ hc
        obtain ⟨hs₂, hl₂⟩ := lowerClauses_lowers env cs s₁ os₂ s₂ hcs
        refine ⟨hs₁.trans hs₂, ?_⟩
        intro o ho
        rcases List.mem_cons.mp ho with rfl | ho
        · have hl := hl₁.mono (LeafOK.grow hs₂.fieldsGrow)
          cases c.keyword
          · exact hl
          · exact hl.unaryApp .not
        · exact hl₂ o ho

theorem conjoin_lowers {Q : Leaf → Cedar.Spec.Expr → Prop} (hQ : NoBoolRef Q) :
    (os : List Out) → (∀ o ∈ os, LowersTo Q o.spec o.cedar o.refs) →
    LowersTo Q (conjoin os).spec (conjoin os).cedar (conjoin os).refs
  | [], _ => lowersTo_lit _
  | o :: os, h => by
    simp only [conjoin]
    exact balancedFold_induct andOut (fun o => LowersTo Q o.spec o.cedar o.refs)
      (fun a b ha hb => ha.andS hb hQ) o os h

/-- A lowered rule lowers: its Cedar policy is its specification's form lowered with its
references, and each leaf and its reference are related by `Q`. -/
structure RuleLowers (Q : Leaf → Cedar.Spec.Expr → Prop) (ro : RuleOut) : Prop where
  lower : ∀ r k, RefsAt r k ro.refs → ro.spec.lowerVia r k = (ro.cedar, k + ro.refs.length)
  leaves : Zips Q ro.spec.toExpr.leaves ro.refs

theorem RuleLowers.mono {Q Q' : Leaf → Cedar.Spec.Expr → Prop} (hQ : ∀ a b, Q a b → Q' a b)
    {ro : RuleOut} (h : RuleLowers Q ro) : RuleLowers Q' ro :=
  ⟨h.lower, h.leaves.mono hQ⟩

/-- The leaves of a rule of one `when` clause are those of its body. -/
theorem policy_toExpr_leaves (p : Policy) (b : Expr) (h : p.condition = [⟨.when, b⟩]) :
    p.toExpr.leaves = b.leaves := by
  simp [Policy.toExpr, Expr.leaves, leaves_ofCedar, h, Conditions.toExpr, Condition.toExpr]

theorem lowerPolicy_lowers {decls : Option ProviderDecls.Declarations}
    {enumNames : List (String × String)} {key id : String} {p : Surface.Policy} {s : St}
    {ro : RuleOut} {s' : St} (h : lowerPolicy decls enumNames key id p s = .ok (ro, s')) :
    Hoists (ruleEnv decls enumNames p) { s with key, ordinal := 0 } s' ∧ FieldsGrow s s' ∧
      RuleLowers (LeafOK s') ro := by
  simp only [lowerPolicy] at h
  cases hc : lowerClauses (ruleEnv decls enumNames p) p.conditions { s with key, ordinal := 0 } with
  | error _ => simp [hc, bind, Except.bind] at h
  | ok q =>
    obtain ⟨os, s₁⟩ := q
    simp only [hc, bind, Except.bind] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hs, hl⟩ := lowerClauses_lowers _ p.conditions _ os s₁ hc
      have hc := conjoin_lowers (leafOK_noBoolRef _) os hl
      refine ⟨hs, FieldsGrow.trans (s₂ := { s with key, ordinal := 0 })
        ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩ hs.fieldsGrow,
        ⟨fun r k hr => ?_, ?_⟩⟩
      · simp [Policy.lowerVia, Conditions.lowerVia, hc.lower r k hr]
      · rw [policy_toExpr_leaves _ _ rfl]
        exact hc.leaves

/-! ## The policy set -/

theorem lowerPoliciesFrom_lowers {decls : Option ProviderDecls.Declarations}
    {enumNames : List (String × String)} {d : Option String} {ids : Option (List String)} :
    (i : Nat) → (ps : List Surface.Policy) → (acc res : Rules) →
    lowerPoliciesFrom decls enumNames d ids i ps acc = .ok res →
    (∀ ro ∈ acc.rules, RuleLowers (LeafOK acc.st) ro) →
    FieldsGrow acc.st res.st ∧ ∀ ro ∈ res.rules, RuleLowers (LeafOK res.st) ro
  | _, [], acc, res, h, hacc => by
    simp only [lowerPoliciesFrom, Except.ok.injEq] at h
    subst h
    exact ⟨FieldsGrow.refl _, hacc⟩
  | i, p :: ps, acc, res, h, hacc => by
    simp only [lowerPoliciesFrom] at h
    cases hp : lowerPolicy decls enumNames (ruleKey d i) (ruleId d ids i) p acc.st with
    | error _ => simp [hp, bind, Except.bind] at h
    | ok q =>
      obtain ⟨ro, s₁⟩ := q
      simp only [hp, bind, Except.bind] at h
      split at h
      · simp at h
      · obtain ⟨-, hg₁, hro⟩ := lowerPolicy_lowers hp
        have := lowerPoliciesFrom_lowers (i + 1) ps _ res h (by
          intro ro' hro'
          simp only [List.mem_append, List.mem_singleton] at hro'
          rcases hro' with hro' | rfl
          · exact (hacc ro' hro').mono (LeafOK.grow hg₁)
          · exact hro)
        exact ⟨hg₁.trans this.1, this.2⟩

/-- The rules lower, one after the other: the Cedar policies are the rules' specification's forms
lowered with their references, numbered from `k`. -/
theorem policies_lowerVia {Q : Leaf → Cedar.Spec.Expr → Prop} :
    (rs : List RuleOut) → (∀ ro ∈ rs, RuleLowers Q ro) →
    (∀ r k, RefsAt r k (rs.map (·.refs)).flatten →
      Policies.lowerVia r k (rs.map (·.spec)) = (rs.map (·.cedar), k + ((rs.map (·.refs)).flatten).length)) ∧
    Zips Q ((rs.map (·.spec)).flatMap (·.toExpr.leaves)) (rs.map (·.refs)).flatten
  | [], _ => ⟨fun _ _ _ => rfl, by simp [Zips]⟩
  | ro :: rs, h => by
    have ih := policies_lowerVia rs fun ro' h' => h ro' (List.mem_cons_of_mem _ h')
    have hro := h ro (by simp)
    refine ⟨fun r k hr => ?_, ?_⟩
    · simp only [List.map_cons, List.flatten_cons] at hr ⊢
      simp [Policies.lowerVia, hro.lower r k hr.left, ih.1 r _ hr.right, Nat.add_assoc]
    · simpa using hro.leaves.append ih.2

/-- The crate's references stand for leaves in a cedarified set: each is the crate's reference to
a hoisted field of the leaf's kind, whose leaf is the specification's when every leaf has a form
in the specification. -/
def leafRef (w : WithSpec) : Leaf → Cedar.Spec.Expr → Prop
  | .inl φ, ref => ∃ f ∈ w.cedarified.contextFields, ref = temporalRef f.fieldName ∧
      (f.temporal.condition.toFormula = .ok φ ∨ w.specErrors ≠ [])
  | .inr c, ref => ∃ f ∈ w.cedarified.providerFields, ref = providerRef f.fieldName ∧
      (callOf f.invocation f.methods = .ok c ∨ w.specErrors ≠ [])

/-- The crate's `j`-th reference, as a function. -/
def refAt (refs : List Cedar.Spec.Expr) (j : Nat) : Cedar.Spec.Expr := refs.getD j (.lit (.bool true))

theorem refsAt_refAt (refs : List Cedar.Spec.Expr) : RefsAt (refAt refs) 0 refs := by
  intro j hj
  simp [refAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem lowerPolicies_lowers {decls : Option ProviderDecls.Declarations}
    {enumNames : List (String × String)} {d : Option String} {ids : Option (List String)}
    {ps : List Surface.Policy} {res : Rules}
    (h : lowerPolicies decls enumNames d ids ps = .ok res) :
    ∀ ro ∈ res.rules, RuleLowers (LeafOK res.st) ro :=
  (lowerPoliciesFrom_lowers 0 ps _ res h (by simp)).2

/-- **Cedarify lowers as the specification does.** The crate's Cedar policies are the rules in the
specification's form lowered with the crate's references for their leaves (numbered over the
set, as the specification numbers them); each reference is the crate's reference to a field of
the leaf's kind; and the crate-named rules cedarify returns are those policies. -/
theorem cedarifyFull_lowered {ps : Surface.PolicySet} {frag : CedarSchema.Fragment}
    {decls : Option ProviderDecls.Declarations} {d : Option String} {ids : Option (List String)}
    {w : WithSpec} (h : cedarifyFull ps frag decls d ids = .ok w) :
    Policies.lowerVia (refAt w.refs) 0 w.spec = (w.cedar, w.refs.length) ∧
    Zips (leafRef w) (w.spec.flatMap (·.toExpr.leaves)) w.refs ∧
    w.cedarified.policies = w.cedar.map Policy.ofCedar := by
  simp only [cedarifyFull] at h
  cases hf : lowerPolicies decls [] d ids ps.policies with
  | error _ => simp [hf, bind, Except.bind] at h
  | ok first =>
    simp only [hf, bind, Except.bind] at h
    generalize enumsOf frag decls first.st.providerFields = q at h
    obtain ⟨referenced, enumNames⟩ := q
    -- The rules, from the first lowering or the second.
    obtain ⟨rules, hrules, hw⟩ : ∃ rules : Rules,
        (∀ ro ∈ rules.rules, RuleLowers (LeafOK rules.st) ro) ∧
        w = assemble frag referenced enumNames rules := by
      simp only at h
      split at h
      · simp [pure, Except.pure] at h
        exact ⟨first, lowerPolicies_lowers hf, h.symm⟩
      · cases hs : lowerPolicies decls enumNames d ids ps.policies with
        | error _ => simp [hs] at h
        | ok second =>
          simp [hs, pure, Except.pure] at h
          exact ⟨second, lowerPolicies_lowers hs, h.symm⟩
    subst hw
    have hl := policies_lowerVia rules.rules hrules
    refine ⟨?_, ?_, rfl⟩
    · simpa [assemble] using hl.1 _ 0 (refsAt_refAt _)
    · refine hl.2.mono ?_
      intro l ref hok
      cases l with
      | inl φ =>
        obtain ⟨f, hf, hr, hφ⟩ := hok
        exact ⟨_, List.mem_map_of_mem hf, hr, hφ⟩
      | inr c =>
        obtain ⟨f, hf, hr, hc⟩ := hok
        exact ⟨_, List.mem_map_of_mem hf, hr, hc⟩

/-- **Up to renaming.** The crate's Cedar policies are the specification's lowering of a policy
set whose rules are cedarify's rules in the specification's form, with the reference to the
specification's `j`-th leaf, `context.leafAttr j`, replaced by the crate's `j`-th reference. -/
theorem cedarifyFull_lowered_rename {ps : Surface.PolicySet} {frag : CedarSchema.Fragment}
    {decls : Option ProviderDecls.Declarations} {d : Option String} {ids : Option (List String)}
    {w : WithSpec} (h : cedarifyFull ps frag decls d ids = .ok w) (P : PolicySet)
    (hP : P.policies = w.spec) :
    P.lowered = (Policies.lowerVia specRef 0 w.spec).1 ∧
    w.cedar = (Policies.lowerVia (refAt w.refs) 0 w.spec).1 ∧
    w.refs.length = P.leafList.length := by
  have hl := cedarifyFull_lowered h
  refine ⟨by rw [lowered_eq_lowerVia, hP], by rw [hl.1], ?_⟩
  rw [PolicySet.leafList, hP]
  exact (Zips.length_eq hl.2.1).symm

/-- **The leaves.** When every leaf has a form in the specification, the crate's `j`-th reference
is `context.<f>` for a hoisted temporal field `f` whose block is the specification's `j`-th leaf
(a temporal one), or `context.providers.<f>` for a hoisted provider field whose call is that leaf
(a provider one). -/
theorem cedarifyWithSpec_leaves {ps : Surface.PolicySet} {frag : CedarSchema.Fragment}
    {decls : Option ProviderDecls.Declarations} {d : Option String} {ids : Option (List String)}
    {w : WithSpec} (h : cedarifyWithSpec ps frag decls d ids = .ok w) :
    w.specErrors = [] ∧
    Zips (fun l ref => match l with
        | .inl φ => ∃ f ∈ w.cedarified.contextFields, ref = temporalRef f.fieldName ∧
            f.temporal.condition.toFormula = .ok φ
        | .inr c => ∃ f ∈ w.cedarified.providerFields, ref = providerRef f.fieldName ∧
            callOf f.invocation f.methods = .ok c)
      (w.spec.flatMap (·.toExpr.leaves)) w.refs := by
  simp only [cedarifyWithSpec] at h
  cases hf : cedarifyFull ps frag decls d ids with
  | error _ => simp [hf, bind, Except.bind] at h
  | ok w' =>
    simp only [hf, bind, Except.bind] at h
    split at h
    · next he =>
      simp [pure, Except.pure] at h
      subst h
      refine ⟨he, (cedarifyFull_lowered hf).2.1.mono ?_⟩
      intro l ref hok
      cases l with
      | inl φ =>
        obtain ⟨f, hf, hr, hφ⟩ := hok
        exact ⟨f, hf, hr, hφ.resolve_right (by simp [he])⟩
      | inr c =>
        obtain ⟨f, hf, hr, hc⟩ := hok
        exact ⟨f, hf, hr, hc.resolve_right (by simp [he])⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The rules, one per source rule -/

theorem lowerPoliciesFrom_zips {decls : Option ProviderDecls.Declarations}
    {enumNames : List (String × String)} {d : Option String} {ids : Option (List String)}
    {P : Surface.Policy → RuleOut → Prop}
    (hP : ∀ {key id p s ro s'}, lowerPolicy decls enumNames key id p s = .ok (ro, s') → P p ro) :
    (i : Nat) → (ps : List Surface.Policy) → (acc res : Rules) →
    lowerPoliciesFrom decls enumNames d ids i ps acc = .ok res →
    ∃ L, res.rules = acc.rules ++ L ∧ Zips P ps L
  | _, [], acc, res, h => by
    simp only [lowerPoliciesFrom, Except.ok.injEq] at h
    subst h
    exact ⟨[], by simp, trivial⟩
  | i, p :: ps, acc, res, h => by
    simp only [lowerPoliciesFrom] at h
    cases hp : lowerPolicy decls enumNames (ruleKey d i) (ruleId d ids i) p acc.st with
    | error _ => simp [hp, bind, Except.bind] at h
    | ok q =>
      obtain ⟨ro, s₁⟩ := q
      simp only [hp, bind, Except.bind] at h
      split at h
      · simp at h
      · obtain ⟨L, hL, hz⟩ := lowerPoliciesFrom_zips hP (i + 1) ps _ res h
        exact ⟨ro :: L, by simp [hL], hP hp, hz⟩

theorem zips_map {α β γ : Type} {Q : α → γ → Prop} {f : β → γ} :
    ∀ {xs : List α} {ys : List β}, Zips (fun a b => Q a (f b)) xs ys → Zips Q xs (ys.map f)
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨h.1, zips_map h.2⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem assemble_spec (frag : CedarSchema.Fragment) (referenced : List String)
    (enumNames : List (String × String)) (rules : Rules) :
    (assemble frag referenced enumNames rules).spec = rules.rules.map (·.spec) := rfl

/-- A property every lowered rule has of its source rule holds of cedarify's rules in the
specification's form, rule by rule. -/
theorem cedarifyFull_zips {ps : Surface.PolicySet} {frag : CedarSchema.Fragment}
    {decls : Option ProviderDecls.Declarations} {d : Option String} {ids : Option (List String)}
    {w : WithSpec} {Q : Surface.Policy → Policy → Prop}
    (hQ : ∀ {enumNames key id p s ro s'}, lowerPolicy decls enumNames key id p s = .ok (ro, s') →
      Q p ro.spec)
    (h : cedarifyFull ps frag decls d ids = .ok w) : Zips Q ps.policies w.spec := by
  simp only [cedarifyFull] at h
  have hz : ∀ {enumNames rules}, lowerPolicies decls enumNames d ids ps.policies = .ok rules →
      Zips Q ps.policies (rules.rules.map (·.spec)) := by
    intro enumNames rules hr
    obtain ⟨L, hL, hz⟩ := lowerPoliciesFrom_zips (P := fun p ro => Q p ro.spec) hQ 0 ps.policies _ rules hr
    simp only [List.nil_append] at hL
    rw [hL]
    exact zips_map hz
  cases hf : lowerPolicies decls [] d ids ps.policies with
  | error _ => simp [hf, bind, Except.bind] at h
  | ok first =>
    simp only [hf, bind, Except.bind] at h
    generalize enumsOf frag decls first.st.providerFields = q at h
    obtain ⟨referenced, enumNames⟩ := q
    simp only at h
    split at h
    · simp [pure, Except.pure] at h
      rw [← h, assemble_spec]
      exact hz hf
    · cases hs : lowerPolicies decls enumNames d ids ps.policies with
      | error _ => simp [hs] at h
      | ok second =>
        simp [hs, pure, Except.pure] at h
        rw [← h, assemble_spec]
        exact hz hs

/-- Cedarify's result comes from lowering the rules once or twice, with the provider enums'
names. -/
theorem cedarifyFull_rules {ps : Surface.PolicySet} {frag : CedarSchema.Fragment}
    {decls : Option ProviderDecls.Declarations} {d : Option String} {ids : Option (List String)}
    {w : WithSpec} (h : cedarifyFull ps frag decls d ids = .ok w) :
    ∃ enumNames referenced rules, lowerPolicies decls enumNames d ids ps.policies = .ok rules ∧
      w = assemble frag referenced enumNames rules := by
  simp only [cedarifyFull] at h
  cases hf : lowerPolicies decls [] d ids ps.policies with
  | error _ => simp [hf, bind, Except.bind] at h
  | ok first =>
    simp only [hf, bind, Except.bind] at h
    generalize enumsOf frag decls first.st.providerFields = q at h
    obtain ⟨referenced, enumNames⟩ := q
    simp only at h
    split at h
    · next he =>
      have : enumNames = [] := List.isEmpty_iff.mp he
      subst this
      simp [pure, Except.pure] at h
      exact ⟨[], referenced, first, hf, h.symm⟩
    · cases hs : lowerPolicies decls enumNames d ids ps.policies with
      | error _ => simp [hs] at h
      | ok second =>
        simp [hs, pure, Except.pure] at h
        exact ⟨enumNames, referenced, second, hs, h.symm⟩

/-- `cedarify` is `cedarifyFull` without the specification's form. -/
theorem cedarify_eq_ok {ps : Surface.PolicySet} {frag : CedarSchema.Fragment}
    {decls : Option ProviderDecls.Declarations} {d : Option String} {ids : Option (List String)}
    {c : Cedarified} (h : cedarify ps frag decls d ids = .ok c) :
    ∃ w, cedarifyFull ps frag decls d ids = .ok w ∧ w.cedarified = c := by
  simp only [cedarify] at h
  cases hw : cedarifyFull ps frag decls d ids with
  | error _ => simp [hw, Except.map] at h
  | ok w => exact ⟨w, rfl, by simpa [hw, Except.map] using h⟩

end Dogwood.Thm.Frontend.Cedarify
