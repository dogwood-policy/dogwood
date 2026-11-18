import Dogwood.Thm.AugmentBasics
import Dogwood.Spec.SequentialLowering
import Dogwood.Thm.ContextReads
import Dogwood.Thm.ScopeTyping
import Dogwood.Thm.SchemaWellFormed
import Dogwood.Thm.Frontend.Augment.Typecheck

/-!
# The augmented schema is action-selective, and adding more changes nothing

Validity checks the lowered rules against the action schema with each leaf's attribute added to
the contexts of the actions its rule's action scope admits (`PolicySet.augmentedSchema`), as the
crate does (`scope_target_actions`). This module proves that it is *safe* to add the attributes
to more actions: validation against any augmentation that adds each leaf's attribute at least to
those actions, and adds only leaf attributes (`PolicySet.Covers`), gives the same verdict.

* **Cedar's verdict** (`validate_augmentWith_agree`, for any schema; `validate_covers_iff`, for a
  policy set): a rule reads, at an action its action scope admits, only declared attributes and
  its own leaves' attributes, and those agree in the two schemas; at an action its scope does not
  admit, Cedar types its scope as `False`, or fails to type it, without reading the context
  (`actionScope_ff_or_error`).
* **Well-formedness** (`wellFormed_of_covers`): every leaf's attribute is in some context of a
  schema that validates the lowered rules, since Cedar's validator rejects a rule its scope keeps
  out of every environment; so the leaves' types are checked by either schema's check.
* **Enumerated ancestors** (`standardAncestors_augmentWith`): the check reads no context.

So validity, stated with the selective schema, is validity stated with the schema that adds every
attribute to every action (`valid_iff_validAll`), which the proofs about a valid set's decisions
use: a decision's request context holds every leaf's value.
-/

namespace Dogwood.Thm

open Dogwood.Spec
open Cedar.Spec (Attr EntityUID)
open Cedar.Data (Map)
open Cedar.Validation (Schema QualifiedType TypeEnv ActionSchemaEntry CedarType ActionSchema)
open Dogwood.Frontend.Augment.Typecheck (ReadsOnly SameSkeleton SkelRel ScopeExcludes
  typecheckPolicyWithEnvironments_agree forall₂_map_same)

/-! ## Augmenting each action's context -/

theorem augment_eq_augmentWith (A : Schema) (H : List (Attr × QualifiedType)) :
    Schema.augment A H = Schema.augmentWith A (fun _ => H) := rfl

theorem augmentWith_ets (A : Schema) (Hsel : EntityUID → List (Attr × QualifiedType)) :
    (Schema.augmentWith A Hsel).ets = A.ets := rfl

theorem augmentWith_acts_toList (A : Schema) (Hsel : EntityUID → List (Attr × QualifiedType)) :
    (Schema.augmentWith A Hsel).acts.toList =
      A.acts.toList.map fun q => (q.1, augmentEntry (Hsel q.1) q.2) := rfl

theorem augmentWith_keys (A : Schema) (Hsel : EntityUID → List (Attr × QualifiedType)) :
    (Schema.augmentWith A Hsel).acts.toList.map Prod.fst = A.acts.toList.map Prod.fst := by
  rw [augmentWith_acts_toList, List.map_map]
  rfl

theorem find?_eq_find?_toList {α β : Type} [BEq α] (m : Map α β) (k : α) :
    m.find? k = (m.toList.find? (·.1 == k)).map (·.2) := by
  unfold Map.find?
  cases m.toList.find? (fun x => x.1 == k) with
  | none => rfl
  | some p => rfl

theorem augmentWith_find? (A : Schema) (Hsel : EntityUID → List (Attr × QualifiedType))
    (uid : EntityUID) :
    (Schema.augmentWith A Hsel).acts.find? uid =
      (A.acts.find? uid).map (augmentEntry (Hsel uid)) := by
  rw [find?_eq_find?_toList, find?_eq_find?_toList, augmentWith_acts_toList, List.find?_map]
  cases h : A.acts.toList.find? (fun x => x.1 == uid) with
  | none =>
    have : List.find? ((fun x : EntityUID × ActionSchemaEntry => x.1 == uid) ∘
        fun q => (q.1, augmentEntry (Hsel q.1) q.2)) A.acts.toList = none := by
      simpa [Function.comp_def] using h
    simp [this]
  | some q =>
    have : List.find? ((fun x : EntityUID × ActionSchemaEntry => x.1 == uid) ∘
        fun q => (q.1, augmentEntry (Hsel q.1) q.2)) A.acts.toList = some q := by
      simpa [Function.comp_def] using h
    have hq : q.1 = uid := by simpa using List.find?_some h
    simp [this, hq]

theorem augmentWith_contains (A : Schema) (Hsel : EntityUID → List (Attr × QualifiedType))
    (uid : EntityUID) :
    (Schema.augmentWith A Hsel).acts.contains uid = A.acts.contains uid := by
  unfold ActionSchema.contains
  rw [augmentWith_find?, Option.isSome_map]

theorem augmentWith_descendentOf (A : Schema) (Hsel : EntityUID → List (Attr × QualifiedType))
    (a b : EntityUID) :
    (Schema.augmentWith A Hsel).acts.descendentOf a b = A.acts.descendentOf a b := by
  unfold ActionSchema.descendentOf
  rw [augmentWith_find?]
  cases A.acts.find? a <;> rfl

/-- The type a list of attributes gives an attribute: its first entry's. -/
def attrType? (L : List (Attr × QualifiedType)) (a : Attr) : Option QualifiedType :=
  (L.find? (·.1 == a)).map (·.2)

/-- The context of an augmented action at one attribute: the declared attribute, else the
added one. -/
theorem find?_augmentEntry (ctx : Map Attr QualifiedType) (H : List (Attr × QualifiedType))
    (a : Attr) : (Map.make (ctx.toList ++ H)).find? a = (ctx.find? a).or (attrType? H a) := by
  rw [make_append_find?, map_find?_eq, attrType?]
  cases ctx.toList.find? (·.1 == a) <;> simp

theorem sameSkeleton_augmentWith (A : Schema) (H₁ H₂ : EntityUID → List (Attr × QualifiedType)) :
    SameSkeleton (Schema.augmentWith A H₁) (Schema.augmentWith A H₂) where
  ets := rfl
  acts := by
    rw [augmentWith_acts_toList, augmentWith_acts_toList]
    exact forall₂_map_same fun q _ => ⟨rfl, rfl⟩

theorem contains_of_mem_toList {A : Schema} {uid : EntityUID} {e : ActionSchemaEntry}
    (h : (uid, e) ∈ A.acts.toList) : A.acts.contains uid = true := by
  unfold ActionSchema.contains
  rw [find?_eq_find?_toList, Option.isSome_map]
  cases hf : A.acts.toList.find? (fun x => x.1 == uid) with
  | some _ => rfl
  | none =>
    have := List.find?_eq_none.mp hf (uid, e) h
    simp at this

/-- **A rule its action scope keeps out of an action is excluded there**, in every environment
of an augmentation of the schema. -/
theorem scopeExcludes_of_not_admits {A : Schema} {Hsel : EntityUID → List (Attr × QualifiedType)}
    {p : Cedar.Spec.Policy} {uid : EntityUID} {e : ActionSchemaEntry}
    (hmem : (uid, e) ∈ A.acts.toList) (hna : actionScopeAdmits A uid p.actionScope = false)
    {env : TypeEnv} (hacts : env.acts = (Schema.augmentWith A Hsel).acts) (hact : env.reqty.action = uid) :
    ScopeExcludes p env := by
  intro c
  rw [substituteAction_eq]
  have hdesc : ∀ a b, env.acts.descendentOf a b = A.acts.descendentOf a b := by
    intro a b; rw [hacts, augmentWith_descendentOf]
  have hc : env.acts.contains env.reqty.action = true := by
    rw [hacts, augmentWith_contains, hact]; exact contains_of_mem_toList hmem
  exact actionScope_ff_or_error hdesc hc (by rw [hact]; exact hna) c

theorem value_unique' {L : List (EntityUID × ActionSchemaEntry)} (hnd : (L.map Prod.fst).Nodup) :
    ∀ {uid : EntityUID} {e e' : ActionSchemaEntry}, (uid, e) ∈ L → (uid, e') ∈ L → e = e' := by
  induction L with
  | nil => intro _ _ _ h; simp at h
  | cons q L ih =>
    intro uid e e' h₁ h₂
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨hnot, hnd⟩ := hnd
    rcases List.mem_cons.mp h₁ with h₁ | h₁
    · rcases List.mem_cons.mp h₂ with h₂ | h₂
      · rw [← h₁] at h₂; simp only [Prod.mk.injEq] at h₂; exact h₂.2.symm
      · exact absurd ⟨_, h₂, by rw [← h₁]⟩ hnot
    · rcases List.mem_cons.mp h₂ with h₂ | h₂
      · exact absurd ⟨_, h₁, by rw [← h₂]⟩ hnot
      · exact ih hnd h₁ h₂

/-- **Two augmentations of a schema give a rule the same Cedar verdict**, when at every action
its action scope admits, the rule reads the context only at attributes the action declares or
at which the two augmentations agree. -/
theorem typecheck_augmentWith_agree (A : Schema) (H₁ H₂ : EntityUID → List (Attr × QualifiedType))
    (p : Cedar.Spec.Policy) (hnd : (A.acts.toList.map Prod.fst).Nodup)
    (hp : ∀ uid e, (uid, e) ∈ A.acts.toList → actionScopeAdmits A uid p.actionScope = true →
      ∃ R, ReadsOnly R p.toExpr ∧
        ∀ a ∈ R, (e.context.find? a).isSome ∨ attrType? (H₁ uid) a = attrType? (H₂ uid) a) :
    (Cedar.Validation.typecheckPolicyWithEnvironments Cedar.Validation.typecheckPolicy p
        (Schema.augmentWith A H₁)).toBool =
      (Cedar.Validation.typecheckPolicyWithEnvironments Cedar.Validation.typecheckPolicy p
        (Schema.augmentWith A H₂)).toBool := by
  refine typecheckPolicyWithEnvironments_agree (sameSkeleton_augmentWith A H₁ H₂) p ?_
  intro q₁ hq₁ q₂ hq₂ hrel
  rw [augmentWith_acts_toList, List.mem_map] at hq₁ hq₂
  obtain ⟨⟨uid, e⟩, he, rfl⟩ := hq₁
  obtain ⟨⟨uid', e'⟩, he', rfl⟩ := hq₂
  obtain ⟨huid, _⟩ := hrel
  simp only at huid
  subst huid
  have hee : e = e' := value_unique' hnd he he'
  subst hee
  cases hadm : actionScopeAdmits A uid p.actionScope with
  | true =>
    obtain ⟨R, hR, hctx⟩ := hp uid e he hadm
    refine .inl ⟨R, hR, fun a ha => ?_⟩
    show (Map.make (e.context.toList ++ H₁ uid)).find? a = (Map.make (e.context.toList ++ H₂ uid)).find? a
    rw [find?_augmentEntry, find?_augmentEntry]
    rcases hctx a ha with hdecl | hsame
    · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hdecl
      simp [hq]
    · rw [hsame]
  | false =>
    exact .inr fun env hacts _ hact => scopeExcludes_of_not_admits he hadm hacts hact

/-- **The same verdict for a set of rules.** -/
theorem validate_augmentWith_agree (A : Schema) (H₁ H₂ : EntityUID → List (Attr × QualifiedType))
    (ps : Cedar.Spec.Policies) (hnd : (A.acts.toList.map Prod.fst).Nodup)
    (hp : ∀ p ∈ ps, ∀ uid e, (uid, e) ∈ A.acts.toList → actionScopeAdmits A uid p.actionScope = true →
      ∃ R, ReadsOnly R p.toExpr ∧
        ∀ a ∈ R, (e.context.find? a).isSome ∨ attrType? (H₁ uid) a = attrType? (H₂ uid) a) :
    Cedar.Validation.validate ps (Schema.augmentWith A H₁) = .ok () ↔
      Cedar.Validation.validate ps (Schema.augmentWith A H₂) = .ok () := by
  unfold Cedar.Validation.validate
  induction ps with
  | nil => exact Iff.rfl
  | cons p ps ih =>
    have h₁ := typecheck_augmentWith_agree A H₁ H₂ p hnd (hp p (List.mem_cons_self ..))
    have ih := ih fun q hq => hp q (List.mem_cons_of_mem _ hq)
    simp only [List.forM]
    cases hs : Cedar.Validation.typecheckPolicyWithEnvironments Cedar.Validation.typecheckPolicy p
        (Schema.augmentWith A H₁) <;>
      cases ha : Cedar.Validation.typecheckPolicyWithEnvironments Cedar.Validation.typecheckPolicy p
        (Schema.augmentWith A H₂) <;>
      rw [hs, ha] at h₁ <;> simp_all [Except.toBool, bind, Except.bind]

/-! ## The augmentations of a policy set -/

/-- **`Hsel` covers the leaves' attributes `H`**: it adds each leaf's attribute at least to the
actions its rule's action scope admits (`PolicySet.targetedAt`), and adds only attributes of
`H`. The selective augmentation covers them (`covers_targetedAt`), and so does adding every
attribute to every action (`covers_all`). -/
structure _root_.Dogwood.Spec.PolicySet.Covers (P : PolicySet) (H : List (Attr × QualifiedType))
    (Hsel : EntityUID → List (Attr × QualifiedType)) : Prop where
  sub : ∀ uid, ∀ x ∈ Hsel uid, x ∈ H
  cover : ∀ uid, ∀ x ∈ P.targetedAt H uid, x ∈ Hsel uid

theorem targetedAt_sub {P : PolicySet} {H : List (Attr × QualifiedType)} {uid : EntityUID}
    {x : Attr × QualifiedType} (h : x ∈ P.targetedAt H uid) : x ∈ H := by
  unfold PolicySet.targetedAt at h
  obtain ⟨⟨y, s⟩, hy, rfl⟩ := List.mem_map.mp h
  exact (List.of_mem_zip (List.mem_filter.mp hy).1).1

theorem covers_targetedAt (P : PolicySet) (H : List (Attr × QualifiedType)) :
    P.Covers H (P.targetedAt H) :=
  ⟨fun _ _ h => targetedAt_sub h, fun _ _ h => h⟩

theorem covers_all (P : PolicySet) (H : List (Attr × QualifiedType)) :
    P.Covers H (fun _ => H) :=
  ⟨fun _ _ h => h, fun _ _ h => targetedAt_sub h⟩

theorem leafScopes_length (P : PolicySet) : P.leafScopes.length = P.leafList.length := by
  simp [PolicySet.leafScopes, PolicySet.leafList, List.length_flatMap]

/-- A leaf whose rule's action scope admits the action has its attribute added there. -/
theorem mem_targetedAt {P : PolicySet} {H : List (Attr × QualifiedType)} {uid : EntityUID}
    {i : Nat} (hi : i < H.length) {s : Cedar.Spec.ActionScope} (hs : P.leafScopes[i]? = some s)
    (had : actionScopeAdmits P.actionSchema uid s = true) : H[i] ∈ P.targetedAt H uid := by
  unfold PolicySet.targetedAt
  refine List.mem_map.mpr ⟨(H[i], s), List.mem_filter.mpr ⟨?_, by simpa using had⟩, rfl⟩
  rw [List.mem_iff_getElem?]
  exact ⟨i, by simp [List.getElem?_zip_eq_some, hs, hi]⟩

/-- The rules of a list, lowered from an offset, each with the action scopes of its leaves. -/
theorem lowerFrom_mem_scopes : ∀ (ps : Policies) (k : Nat) (q : Cedar.Spec.Policy),
    q ∈ (Policies.lowerFrom k ps).1 → ∃ p ∈ ps, ∃ j, q = (p.lowerFrom (k + j)).1 ∧
      ∀ i < p.toExpr.leaves.length,
        (ps.flatMap fun p => p.toExpr.leaves.map fun _ => p.actionScope)[j + i]? = some p.actionScope
  | [], _, _, h => by cases h
  | p :: ps, k, q, h => by
    simp only [Policies.lowerFrom, List.mem_cons] at h
    rcases h with rfl | h
    · refine ⟨p, List.mem_cons_self .., 0, by simp, fun i hi => ?_⟩
      rw [List.flatMap_cons, List.getElem?_append_left (by simpa using hi)]
      simp [hi]
    · obtain ⟨p', hp', j, rfl, hj⟩ := lowerFrom_mem_scopes ps _ q h
      rw [policy_lowerFrom_snd] at *
      refine ⟨p', List.mem_cons_of_mem _ hp', p.toExpr.leaves.length + j,
        by rw [Nat.add_assoc], fun i hi => ?_⟩
      rw [List.flatMap_cons, List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map, Nat.add_assoc, Nat.add_sub_cancel_left]
      exact hj i hi

/-- **What a lowered rule reads of the context**: attributes that are no leaf's, and the
attributes of its own leaves, whose rule's action scope is its own. -/
theorem loweredFrom_reads {P : PolicySet} {k : Nat}
    (hrc : ∀ p ∈ P.policies, p.toExpr.ReadsContext (P.hoistedNamesFrom k)) :
    ∀ q ∈ P.loweredFrom k, ∃ R, ReadsOnly R q.toExpr ∧ ∀ a ∈ R, a ∉ P.hoistedNamesFrom k ∨
      ∃ i, P.leafScopes[i]? = some q.actionScope ∧ a = leafAttr (k + i) := by
  intro q hq
  obtain ⟨p, hp, j, rfl, hj⟩ := lowerFrom_mem_scopes P.policies k q hq
  let own := (List.range' (k + j) p.toExpr.leaves.length).map leafAttr
  let N := (P.hoistedNamesFrom k).filter fun a => !own.contains a
  have hN : p.toExpr.ReadsContext N :=
    readsContext_mono (fun a ha => (List.mem_filter.mp ha).1) _ (hrc p hp)
  have havoid : CtxAvoids N (p.toExpr.lowerFrom (k + j)).1 := by
    refine ctxAvoids_lowerFrom p.toExpr (k + j) hN fun i h₁ h₂ hm => ?_
    have := (List.mem_filter.mp hm).2
    have hmem : leafAttr i ∈ own := List.mem_map.mpr ⟨i, List.mem_range'_1.mpr ⟨h₁, h₂⟩, rfl⟩
    simp [List.elem_eq_mem, hmem] at this
  refine ⟨ctxReads (p.toExpr.lowerFrom (k + j)).1, ?_, fun a ha => ?_⟩
  · rw [policy_lowerFrom]
    exact readsOnly_of_ctxAvoids _ havoid fun a ha => ha
  · have hnot := ctxReads_not_mem _ havoid a ha
    by_cases hh : a ∈ P.hoistedNamesFrom k
    · right
      have hown : a ∈ own := by
        by_contra hno
        exact hnot (List.mem_filter.mpr ⟨hh, by simpa using hno⟩)
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hown
      obtain ⟨hm₁, hm₂⟩ := List.mem_range'_1.mp hm
      refine ⟨m - k, ?_, by rw [show k + (m - k) = m by omega]⟩
      have := hj (m - k - j) (by omega)
      rw [show j + (m - k - j) = m - k by omega] at this
      exact this
    · exact .inl hh

/-! ## Attribute types in lists that cover the leaves -/

theorem attrType?_none {L : List (Attr × QualifiedType)} {a : Attr} (h : ∀ x ∈ L, x.1 ≠ a) :
    attrType? L a = none := by
  unfold attrType?
  rw [List.find?_eq_none.mpr fun x hx hk => h x hx (by simpa using hk)]
  rfl

theorem attrType?_of_mem {H L : List (Attr × QualifiedType)} (hnd : (H.map (·.1)).Nodup)
    (hsub : ∀ x ∈ L, x ∈ H) {x : Attr × QualifiedType} (hx : x ∈ L) :
    attrType? L x.1 = some x.2 := by
  unfold attrType?
  cases hf : L.find? (·.1 == x.1) with
  | none =>
    have := List.find?_eq_none.mp hf x hx
    simp at this
  | some y =>
    have hy := List.mem_of_find?_eq_some hf
    have hyk : y.1 = x.1 := by simpa using List.find?_some hf
    have := eq_of_mem_of_key hnd (hsub y hy) (hsub x hx) hyk
    simp [this]

/-- **Two augmentations that cover the leaves agree** at every attribute a lowered rule reads, at
an action its action scope admits. -/
theorem key_of_hoistedNamesFrom {P : PolicySet} {k : Nat} {H : List (Attr × QualifiedType)}
    (hkeys : H.map (·.1) = P.hoistedNamesFrom k) {i : Nat} (hi : i < H.length) :
    H[i].1 = leafAttr (k + i) := by
  have : (H.map (·.1))[i]'(by simpa using hi) = (P.hoistedNamesFrom k)[i]'(by
    rw [← hkeys]; simpa using hi) := by simp only [hkeys]
  simpa [PolicySet.hoistedNamesFrom] using this

theorem keys_hoistedTypesFrom {P : PolicySet} {k : Nat} {H : List (Attr × QualifiedType)}
    (h : P.hoistedTypesFrom? k = some H) : H.map Prod.fst = P.hoistedNamesFrom k := by
  unfold PolicySet.hoistedTypesFrom? at h
  obtain ⟨h₁, h₂⟩ := mapM_option_eq_map h
  rw [h₁, List.map_map]
  unfold PolicySet.hoistedNamesFrom
  clear h₁ h
  generalize P.leafList = l at h₂ ⊢
  induction l generalizing k with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.length_cons, List.range'_succ]
    congr 1
    · have := h₂ (x, k) (by simp)
      cases hty : P.leafType? x <;> simp_all
    · exact ih (fun y hy => h₂ y (by simp [List.zipIdx_cons, hy]))

theorem hoistedNamesFrom_zero (P : PolicySet) : P.hoistedNamesFrom 0 = P.hoistedNames := by
  simp only [PolicySet.hoistedNamesFrom, PolicySet.hoistedNames, List.range_eq_range']

theorem hoistedTypesFrom_zero (P : PolicySet) : P.hoistedTypesFrom? 0 = P.hoistedTypes? := rfl

theorem loweredFrom_zero (P : PolicySet) : P.loweredFrom 0 = P.lowered := rfl

theorem attrType?_covers_agree {P : PolicySet} {k : Nat} {H : List (Attr × QualifiedType)}
    (hkeys : H.map (·.1) = P.hoistedNamesFrom k) (hnd : (P.hoistedNamesFrom k).Nodup)
    {H₁ H₂ : EntityUID → List (Attr × QualifiedType)} (h₁ : P.Covers H H₁) (h₂ : P.Covers H H₂)
    {uid : EntityUID} {s : Cedar.Spec.ActionScope}
    (had : actionScopeAdmits P.actionSchema uid s = true) {a : Attr}
    (ha : a ∉ P.hoistedNamesFrom k ∨ ∃ i, P.leafScopes[i]? = some s ∧ a = leafAttr (k + i)) :
    attrType? (H₁ uid) a = attrType? (H₂ uid) a := by
  have hnd' : (H.map (·.1)).Nodup := by rw [hkeys]; exact hnd
  rcases ha with ha | ⟨i, hs, rfl⟩
  · have hnone : ∀ Hk : EntityUID → List (Attr × QualifiedType), P.Covers H Hk →
        attrType? (Hk uid) a = none := by
      intro Hk hk
      refine attrType?_none fun x hx hxa => ha ?_
      rw [← hkeys, ← hxa]
      exact List.mem_map.mpr ⟨x, hk.sub uid x hx, rfl⟩
    rw [hnone H₁ h₁, hnone H₂ h₂]
  · have hiS : i < P.leafScopes.length := by
      rcases Nat.lt_or_ge i P.leafScopes.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hs; cases hs
    have hlen : H.length = P.leafList.length := by
      rw [← List.length_map (f := (·.1)), hkeys, PolicySet.hoistedNamesFrom, List.length_map,
        List.length_range']
    have hi : i < H.length := by rw [hlen, ← leafScopes_length]; exact hiS
    have hkey : H[i].1 = leafAttr (k + i) := key_of_hoistedNamesFrom hkeys hi
    have hmem := mem_targetedAt hi hs had
    rw [← hkey, attrType?_of_mem hnd' (h₁.sub uid) (h₁.cover uid _ hmem),
      attrType?_of_mem hnd' (h₂.sub uid) (h₂.cover uid _ hmem)]

/-- **Cedar's verdict is the same against two augmentations that cover the leaves**, for a policy
set whose leaves' attributes are distinct, whose rules read the context only through other
attributes, and whose action schema declares each action once. -/
theorem validate_covers_iff {P : PolicySet} {k : Nat} {H : List (Attr × QualifiedType)}
    (hH : P.hoistedTypesFrom? k = some H) (hnd : (P.hoistedNamesFrom k).Nodup)
    (hrc : P.leafList ≠ [] → ∀ p ∈ P.policies, p.toExpr.ReadsContext (P.hoistedNamesFrom k))
    (hacts : (P.actionSchema.acts.toList.map Prod.fst).Nodup)
    {H₁ H₂ : EntityUID → List (Attr × QualifiedType)} (h₁ : P.Covers H H₁) (h₂ : P.Covers H H₂) :
    Cedar.Validation.validate (P.loweredFrom k) (Schema.augmentWith P.actionSchema H₁) = .ok () ↔
      Cedar.Validation.validate (P.loweredFrom k) (Schema.augmentWith P.actionSchema H₂) =
        .ok () := by
  have hkeys := keys_hoistedTypesFrom hH
  by_cases hL : P.leafList = []
  · have hH0 : H = [] := by
      have : H.map Prod.fst = [] := by rw [hkeys]; simp [PolicySet.hoistedNamesFrom, hL]
      exact List.map_eq_nil_iff.mp this
    have hnil : ∀ Hk : EntityUID → List (Attr × QualifiedType), P.Covers H Hk → Hk = fun _ => [] := by
      intro Hk hk
      funext uid
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      have := hk.sub uid x hx
      rw [hH0] at this
      cases this
    rw [hnil H₁ h₁, hnil H₂ h₂]
  refine validate_augmentWith_agree _ H₁ H₂ _ hacts fun q hq uid e _ had => ?_
  obtain ⟨R, hR, hreads⟩ := loweredFrom_reads (hrc hL) q hq
  exact ⟨R, hR, fun a ha => .inr (attrType?_covers_agree hkeys hnd h₁ h₂ had (hreads a ha))⟩

/-! ## Well-formedness of two augmentations -/

section

open Cedar.Validation (EnvironmentValidationError)
open Frontend (forM_map_eq bind_unit_ok_iff actionSchemaEntry_validateWellFormed_transfer)

/-- The entries of `L`, each changed by `g`, as an action schema. -/
abbrev actsWith (L : List (EntityUID × ActionSchemaEntry))
    (g : EntityUID → ActionSchemaEntry → ActionSchemaEntry) : ActionSchema :=
  Map.mk (L.map fun q => (q.1, g q.1 q.2))

theorem actsWith_keys (L : List (EntityUID × ActionSchemaEntry))
    (g : EntityUID → ActionSchemaEntry → ActionSchemaEntry) :
    (actsWith L g).toList.map Prod.fst = L.map Prod.fst := by
  simp [actsWith, Map.toList_mk_id, List.map_map, Function.comp_def]

theorem wellFormed_actsWith (L : List (EntityUID × ActionSchemaEntry))
    (g₁ g₂ : EntityUID → ActionSchemaEntry → ActionSchemaEntry) :
    (actsWith L g₂).wellFormed = (actsWith L g₁).wellFormed := by
  rw [Bool.eq_iff_iff, Map.wellFormed_correct, Map.wellFormed_correct, Map.wf_iff_sorted,
    Map.wf_iff_sorted]
  apply List.map_eq_implies_sortedBy
  rw [actsWith_keys, actsWith_keys]

theorem acyclic_actsWith {L : List (EntityUID × ActionSchemaEntry)}
    {g₁ g₂ : EntityUID → ActionSchemaEntry → ActionSchemaEntry}
    (hg : ∀ u e, (g₂ u e).ancestors = (g₁ u e).ancestors) :
    ActionSchema.validateAcyclicActionHierarchy (actsWith L g₂) =
      ActionSchema.validateAcyclicActionHierarchy (actsWith L g₁) := by
  simp only [ActionSchema.validateAcyclicActionHierarchy, actsWith, Map.toList_mk_id, forM_map_eq]
  congr 1
  funext x
  simp only [Function.comp, hg]

theorem transitive_actsWith {L : List (EntityUID × ActionSchemaEntry)}
    {g₁ g₂ : EntityUID → ActionSchemaEntry → ActionSchemaEntry}
    (hg : ∀ u e, (g₂ u e).ancestors = (g₁ u e).ancestors) :
    ActionSchema.validateTransitiveActionHierarchy (actsWith L g₂) =
      ActionSchema.validateTransitiveActionHierarchy (actsWith L g₁) := by
  simp only [ActionSchema.validateTransitiveActionHierarchy, actsWith, Map.toList_mk_id,
    forM_map_eq]
  congr 1
  funext x
  simp only [Function.comp, hg]
  congr 1
  funext y
  simp only [Function.comp, hg]

/-- **The check of an action schema, transferred entry by entry**: to an environment with the same
entity types and action names, and from the entries `g₁ uid e` to the entries `g₂ uid e`, with the
same `appliesTo` sets and ancestors and a context that passes the checks the first's does. -/
theorem actionSchema_validateWellFormed_actsWith {env env' : TypeEnv}
    {L : List (EntityUID × ActionSchemaEntry)}
    {g₁ g₂ : EntityUID → ActionSchemaEntry → ActionSchemaEntry} (hets : env'.ets = env.ets)
    (hkeys : env'.acts.toList.map Prod.fst = env.acts.toList.map Prod.fst)
    (hcontains : ∀ uid, env'.acts.contains uid = env.acts.contains uid)
    (hg : ∀ u e, (g₂ u e).appliesToPrincipal = (g₁ u e).appliesToPrincipal ∧
      (g₂ u e).appliesToResource = (g₁ u e).appliesToResource ∧
      (g₂ u e).ancestors = (g₁ u e).ancestors)
    (hctx : ∀ u e, (u, e) ∈ L →
      (CedarType.record (g₁ u e).context).validateWellFormed env = .ok () →
      (CedarType.record (g₁ u e).context).validateLifted = .ok () →
      (CedarType.record (g₂ u e).context).validateWellFormed env' = .ok () ∧
        (CedarType.record (g₂ u e).context).validateLifted = .ok ())
    (h : (actsWith L g₁).validateWellFormed env = .ok ()) :
    ActionSchema.validateWellFormed env' (actsWith L g₂) = .ok () := by
  revert h
  simp only [ActionSchema.validateWellFormed, wellFormed_actsWith L g₁ g₂,
    acyclic_actsWith (fun u e => (hg u e).2.2), transitive_actsWith (fun u e => (hg u e).2.2)]
  cases Map.wellFormed (actsWith L g₁) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.bind_ok, Except.bind_err, reduceCtorEq,
      imp_self, bind_unit_ok_iff]
  rintro ⟨hall, hrest⟩
  refine ⟨?_, hrest⟩
  simp only [actsWith, Map.toList_mk_id, forM_map_eq] at hall ⊢
  apply List.all_ok_implies_forM_ok
  intro ⟨uid, e⟩ hmem
  have := List.forM_ok_implies_all_ok _ _ hall (uid, e) hmem
  simp only [Function.comp, hets] at this ⊢
  revert this
  cases env.ets.contains uid.ty <;>
    simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, imp_self]
  exact actionSchemaEntry_validateWellFormed_transfer hets hkeys hcontains (hg uid e).1
    (hg uid e).2.1 (hg uid e).2.2 (hctx uid e hmem)

end

/-! ## Every leaf's attribute is in a validated context -/

section

open Cedar.Validation (typeOf TypedExpr Capabilities substituteAction)
open Frontend (bind_unit_ok_iff)

/-- Each leaf is a leaf of a lowered rule with its action scope. -/
theorem lowerFrom_scope_of_index : ∀ (ps : Policies) (k i : Nat),
    i < (ps.flatMap fun p => p.toExpr.leaves.map fun _ => p.actionScope).length →
    ∃ q ∈ (Policies.lowerFrom k ps).1,
      (ps.flatMap fun p => p.toExpr.leaves.map fun _ => p.actionScope)[i]? = some q.actionScope
  | [], _, _, h => by simp at h
  | p :: ps, k, i, h => by
    rw [List.flatMap_cons, List.length_append, List.length_map] at h
    by_cases hi : i < p.toExpr.leaves.length
    · refine ⟨(p.lowerFrom k).1, by simp [Policies.lowerFrom], ?_⟩
      rw [List.flatMap_cons, List.getElem?_append_left (by simpa using hi)]
      simp [hi, Policy.lowerFrom]
    · obtain ⟨q, hq, hs⟩ := lowerFrom_scope_of_index ps (p.lowerFrom k).2
        (i - p.toExpr.leaves.length) (by omega)
      refine ⟨q, by simp [Policies.lowerFrom, hq], ?_⟩
      rw [List.flatMap_cons, List.getElem?_append_right (by simp; omega)]
      simpa using hs

theorem leafScope_of_index {P : PolicySet} {k i : Nat} (hi : i < P.leafScopes.length) :
    ∃ q ∈ P.loweredFrom k, P.leafScopes[i]? = some q.actionScope :=
  lowerFrom_scope_of_index P.policies k i hi

theorem and_first_nonff {x y : Cedar.Spec.Expr} {c : Capabilities} {env : TypeEnv}
    {t : TypedExpr} {ct : Capabilities} (h : typeOf (.and x y) c env = .ok (t, ct))
    (hne : t.typeOf ≠ .bool .ff) :
    ∃ tx cx, typeOf x c env = .ok (tx, cx) ∧ tx.typeOf ≠ .bool .ff := by
  rw [typeOf] at h
  cases hx : typeOf x c env with
  | error e => rw [hx] at h; cases h
  | ok r =>
    obtain ⟨tx, cx⟩ := r
    refine ⟨tx, cx, rfl, fun hff => ?_⟩
    rw [hx] at h
    simp only [Except.bind_ok] at h
    unfold Cedar.Validation.typeOfAnd at h
    rw [hff] at h
    simp only [Cedar.Validation.ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hne hff

/-- **A rule Cedar does not type as `False` in an environment admits its action.** -/
theorem actionScopeAdmits_of_policy {A : Schema} {env : TypeEnv}
    (hdesc : ∀ a b, env.acts.descendentOf a b = A.acts.descendentOf a b)
    (hact : env.acts.contains env.reqty.action = true) {q : Cedar.Spec.Policy} {tx : TypedExpr}
    {c : Capabilities} (h : typeOf (substituteAction env.reqty.action q.toExpr) ∅ env = .ok (tx, c))
    (hne : tx.typeOf ≠ .bool .ff) : actionScopeAdmits A env.reqty.action q.actionScope = true := by
  rw [substituteAction_eq] at h
  simp only [Cedar.Spec.Policy.toExpr, Cedar.Validation.mapOnVars] at h
  obtain ⟨t₁, c₁, h₁, hn₁⟩ := and_first_nonff h hne
  obtain ⟨t₂, c₂, h₂, hn₂⟩ := and_second_nonff h hne h₁ hn₁
  obtain ⟨t₃, c₃, h₃, hn₃⟩ := and_first_nonff h₂ hn₂
  exact actionScopeAdmits_of_typeOf hdesc hact h₃ hn₃

/-- **Cedar's validator accepts a rule only if some environment types it other than `False`.** -/
theorem nonff_of_typecheck {q : Cedar.Spec.Policy} {S : Schema}
    (h : Cedar.Validation.typecheckPolicyWithEnvironments Cedar.Validation.typecheckPolicy q S =
      .ok ()) :
    ∃ env ∈ S.environments, ∃ tx c,
      typeOf (substituteAction env.reqty.action q.toExpr) ∅ env = .ok (tx, c) ∧
        tx.typeOf ≠ .bool .ff := by
  unfold Cedar.Validation.typecheckPolicyWithEnvironments at h
  cases hce : (Cedar.Validation.checkEntities S q.toExpr).mapError
      (Cedar.Validation.ValidationError.typeError q.id) with
  | error e => rw [hce] at h; cases h
  | ok u =>
    rw [hce] at h
    cases hm : S.environments.mapM (Cedar.Validation.typecheckPolicy q) with
    | error e => simp [hm, bind, Except.bind] at h
    | ok txs =>
      simp only [hm, bind, Except.bind] at h
      split at h
      · cases h
      · rename_i hnf
        simp only [Cedar.Validation.allFalse, List.all_eq_true] at hnf
        obtain ⟨tx, htx, hne⟩ : ∃ tx ∈ txs, ¬ (tx.typeOf == .bool .ff) = true := by
          by_contra hc
          exact hnf fun x hx => by
            by_contra h'
            exact hc ⟨x, hx, h'⟩
        obtain ⟨env, henv, htc⟩ := List.mapM_ok_implies_all_from_ok hm tx htx
        cases hty : typeOf (substituteAction env.reqty.action q.toExpr) ∅ env with
        | error e => simp only [Cedar.Validation.typecheckPolicy] at htc; rw [hty] at htc; cases htc
        | ok r =>
          obtain ⟨tx', c⟩ := r
          simp only [Cedar.Validation.typecheckPolicy] at htc
          rw [hty] at htc
          simp only at htc
          split at htc
          · cases htc
            exact ⟨env, henv, _, c, hty, by simpa using hne⟩
          · cases htc

theorem mem_augmentWith_toList {A : Schema} {Hsel : EntityUID → List (Attr × QualifiedType)}
    {a : EntityUID} {e' : ActionSchemaEntry} (h : (a, e') ∈ (Schema.augmentWith A Hsel).acts.toList) :
    ∃ e, (a, e) ∈ A.acts.toList ∧ e' = augmentEntry (Hsel a) e := by
  rw [augmentWith_acts_toList, List.mem_map] at h
  obtain ⟨⟨a', e⟩, hmem, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨e, hmem, rfl⟩

theorem entry_context_ok {env : TypeEnv} {entry : ActionSchemaEntry}
    (h : entry.validateWellFormed env = .ok ()) :
    (CedarType.record entry.context).validateWellFormed env = .ok () ∧
      (CedarType.record entry.context).validateLifted = .ok () := by
  revert h
  simp only [ActionSchemaEntry.validateWellFormed]
  cases entry.appliesToPrincipal.wellFormed <;> cases entry.appliesToResource.wellFormed <;>
    cases entry.ancestors.wellFormed <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.bind_ok, Except.bind_err, reduceCtorEq,
      false_implies, bind_unit_ok_iff]
  intro h
  exact ⟨h.2.2.2.1, h.2.2.2.2⟩

/-- The entries of a well-formed action schema are well-formed. -/
theorem entry_ok_of_acts {env : TypeEnv} {acts : ActionSchema} (h : acts.validateWellFormed env = .ok ())
    {uid : EntityUID} {entry : ActionSchemaEntry} (hmem : (uid, entry) ∈ acts.toList) :
    entry.validateWellFormed env = .ok () := by
  revert h
  simp only [ActionSchema.validateWellFormed]
  cases Map.wellFormed acts <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.bind_ok, Except.bind_err, reduceCtorEq,
      false_implies, bind_unit_ok_iff]
  intro h
  have := List.forM_ok_implies_all_ok _ _ h.1 (uid, entry) hmem
  simp only at this
  split at this
  · simp at this
  · simpa using this

theorem acts_ok_of_env {env : TypeEnv} (h : env.validateWellFormed = .ok ()) :
    env.acts.validateWellFormed env = .ok () := by
  simp only [TypeEnv.validateWellFormed, bind_unit_ok_iff] at h
  exact h.2.1

/-- **Every leaf's type is well-formed and lifted**, when Cedar's validator accepts the lowered
rules against a well-formed augmentation that covers the leaves: each leaf's rule is typed other
than `False` in some environment, whose action its scope admits, and whose context, which the
augmentation gives the leaf's attribute, is checked. -/
theorem leafTypes_ok_of_covers {P : PolicySet} {k : Nat} {H : List (Attr × QualifiedType)}
    (hH : P.hoistedTypesFrom? k = some H) (hnd : (P.hoistedNamesFrom k).Nodup)
    (hfresh : ∀ act ∈ P.actionSchema.acts.toList, ∀ a ∈ P.hoistedNamesFrom k,
      act.2.context.find? a = none)
    {Hk : EntityUID → List (Attr × QualifiedType)} (hk : P.Covers H Hk)
    (hval : Cedar.Validation.validate (P.loweredFrom k) (Schema.augmentWith P.actionSchema Hk) =
      .ok ())
    (hwf : (Schema.augmentWith P.actionSchema Hk).validateWellFormed = .ok ()) :
    ∀ x ∈ H, ∀ env : TypeEnv, env.ets = P.actionSchema.ets →
      env.acts.toList.map Prod.fst = P.actionSchema.acts.toList.map Prod.fst →
      x.2.getType.validateWellFormed env = .ok () ∧ x.2.getType.validateLifted = .ok () := by
  intro x hx env hets hkeys
  have hHkeys : H.map (·.1) = P.hoistedNamesFrom k := keys_hoistedTypesFrom hH
  have hnd' : (H.map (·.1)).Nodup := by rw [hHkeys]; exact hnd
  have hlen : H.length = P.leafScopes.length := by
    rw [leafScopes_length, ← List.length_map (f := (·.1)), hHkeys, PolicySet.hoistedNamesFrom,
      List.length_map, List.length_range']
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨q, hq, hs⟩ := leafScope_of_index (k := k) (hlen ▸ hi)
  have htc := List.forM_ok_implies_all_ok _ _ hval q hq
  obtain ⟨env₁, henv₁, tx, c, hty, hne⟩ := nonff_of_typecheck htc
  obtain ⟨a, entry, pr, rs, hmem, -, -, henv⟩ := mem_environments.mp henv₁
  have hacts₁ : env₁.acts = (Schema.augmentWith P.actionSchema Hk).acts := by rw [henv]
  have hets₁ : env₁.ets = P.actionSchema.ets := by rw [henv]; rfl
  have hact₁ : env₁.reqty.action = a := by rw [henv]
  obtain ⟨e, he, rfl⟩ := mem_augmentWith_toList hmem
  have had := actionScopeAdmits_of_policy (A := P.actionSchema)
    (fun x y => by rw [hacts₁, augmentWith_descendentOf])
    (by rw [hacts₁, augmentWith_contains, hact₁]; exact contains_of_mem_toList he) hty hne
  rw [hact₁] at had
  have hin : H[i] ∈ Hk a := hk.cover a _ (mem_targetedAt hi hs had)
  -- The leaf's attribute is in the action's augmented context.
  have hname : H[i].1 ∈ P.hoistedNamesFrom k := by
    rw [← hHkeys]; exact List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩
  have hfind : (Map.make (e.context.toList ++ Hk a)).find? H[i].1 = some H[i].2 := by
    rw [find?_augmentEntry, hfresh (a, e) he _ hname, attrType?_of_mem hnd' (hk.sub a) hin]
    rfl
  have hA := acts_ok_of_env (List.forM_ok_implies_all_ok _ _ hwf _ henv₁)
  rw [hacts₁] at hA
  obtain ⟨hw, hl⟩ := entry_context_ok (entry_ok_of_acts hA hmem)
  have hmemc : (H[i].1, H[i].2) ∈ (Map.make (e.context.toList ++ Hk a)).toList :=
    Map.find?_mem_toList hfind
  rw [Frontend.record_validateWellFormed_ok_iff] at hw
  rw [Frontend.record_validateLifted_ok_iff] at hl
  refine ⟨?_, hl _ hmemc⟩
  have := hw.2 _ hmemc
  rw [Frontend.qualifiedType_validateWellFormed_getType] at this
  rw [Frontend.cedarType_validateWellFormed_congr (env := env₁) (env' := env)
    (by rw [hets, hets₁]) (by rw [hkeys, hacts₁, augmentWith_keys])]
  exact this

end

/-! ## The well-formedness and ancestor checks of two augmentations -/

section

open Frontend (bind_unit_ok_iff)

theorem augmentWith_acts (A : Schema) (Hk : EntityUID → List (Attr × QualifiedType)) :
    (Schema.augmentWith A Hk).acts = actsWith A.acts.toList fun u e => augmentEntry (Hk u) e := rfl

/-- **A well-formed augmentation that validates the lowered rules makes every augmentation that
covers the leaves well-formed.** -/
theorem wellFormed_of_covers {P : PolicySet} {k : Nat} {H : List (Attr × QualifiedType)}
    (hH : P.hoistedTypesFrom? k = some H) (hnd : (P.hoistedNamesFrom k).Nodup)
    (hfresh : ∀ act ∈ P.actionSchema.acts.toList, ∀ a ∈ P.hoistedNamesFrom k,
      act.2.context.find? a = none)
    {H₁ H₂ : EntityUID → List (Attr × QualifiedType)} (h₁ : P.Covers H H₁) (h₂ : P.Covers H H₂)
    (hval : Cedar.Validation.validate (P.loweredFrom k) (Schema.augmentWith P.actionSchema H₁) =
      .ok ())
    (hwf : (Schema.augmentWith P.actionSchema H₁).validateWellFormed = .ok ()) :
    (Schema.augmentWith P.actionSchema H₂).validateWellFormed = .ok () := by
  have hok := leafTypes_ok_of_covers hH hnd hfresh h₁ hval hwf
  unfold Schema.validateWellFormed
  apply List.all_ok_implies_forM_ok
  intro envX henvX
  obtain ⟨a, e₂, pr, rs, hmem₂, hp, hr, rfl⟩ := mem_environments.mp henvX
  obtain ⟨e, he, rfl⟩ := mem_augmentWith_toList hmem₂
  let env₁ : TypeEnv := ⟨(Schema.augmentWith P.actionSchema H₁).ets,
    (Schema.augmentWith P.actionSchema H₁).acts, ⟨pr, a, rs, (augmentEntry (H₁ a) e).context⟩⟩
  let env₂ : TypeEnv := ⟨(Schema.augmentWith P.actionSchema H₂).ets,
    (Schema.augmentWith P.actionSchema H₂).acts, ⟨pr, a, rs, (augmentEntry (H₂ a) e).context⟩⟩
  show env₂.validateWellFormed = .ok ()
  have henv₁ : env₁ ∈ (Schema.augmentWith P.actionSchema H₁).environments :=
    mem_environments.mpr ⟨a, augmentEntry (H₁ a) e, pr, rs,
      (by rw [augmentWith_acts_toList]; exact List.mem_map.mpr ⟨(a, e), he, rfl⟩), hp, hr, rfl⟩
  have hw₁ := List.forM_ok_implies_all_ok _ _ hwf _ henv₁
  simp only [TypeEnv.validateWellFormed, bind_unit_ok_iff] at hw₁ ⊢
  obtain ⟨hE, hA, -⟩ := hw₁
  have hkeys : env₂.acts.toList.map Prod.fst = env₁.acts.toList.map Prod.fst := by
    show (Schema.augmentWith P.actionSchema H₂).acts.toList.map Prod.fst =
      (Schema.augmentWith P.actionSchema H₁).acts.toList.map Prod.fst
    rw [augmentWith_keys, augmentWith_keys]
  have hcont : ∀ u, env₂.acts.contains u = env₁.acts.contains u := fun u => by
    show (Schema.augmentWith P.actionSchema H₂).acts.contains u =
      (Schema.augmentWith P.actionSchema H₁).acts.contains u
    rw [augmentWith_contains, augmentWith_contains]
  refine ⟨?_, ?_, ?_⟩
  · exact (Frontend.entitySchema_validateWellFormed_congr (env := env₁) (env' := env₂) rfl hkeys
      _).trans hE
  · have hA' : ActionSchema.validateWellFormed env₁
        (actsWith P.actionSchema.acts.toList fun u e => augmentEntry (H₁ u) e) = .ok () := hA
    show ActionSchema.validateWellFormed env₂
      (actsWith P.actionSchema.acts.toList fun u e => augmentEntry (H₂ u) e) = .ok ()
    refine actionSchema_validateWellFormed_actsWith (env := env₁) (env' := env₂)
      (L := P.actionSchema.acts.toList) (g₁ := fun u e => augmentEntry (H₁ u) e)
      (g₂ := fun u e => augmentEntry (H₂ u) e) rfl hkeys hcont
      (fun _ _ => ⟨rfl, rfl, rfl⟩) ?_ hA'
    intro u e' hu hc hl
    rw [Frontend.record_validateWellFormed_ok_iff] at hc ⊢
    rw [Frontend.record_validateLifted_ok_iff] at hl ⊢
    -- Each attribute of the second context is declared, so in the first context too, or added.
    have hsrc : ∀ q ∈ (Map.make (e'.context.toList ++ H₂ u)).toList,
        q ∈ (Map.make (e'.context.toList ++ H₁ u)).toList ∨ q ∈ H := by
      intro q hq
      have hf := Map.mem_toList_find? (Map.make_wf _) hq
      rw [find?_augmentEntry] at hf
      cases hc' : e'.context.find? q.1 with
      | some v =>
        rw [hc'] at hf
        simp only [Option.some_or, Option.some.injEq] at hf
        left
        have : (Map.make (e'.context.toList ++ H₁ u)).find? q.1 = some q.2 := by
          rw [find?_augmentEntry, hc', hf]; rfl
        exact Map.find?_mem_toList this
      | none =>
        rw [hc'] at hf
        simp only [Option.none_or] at hf
        right
        unfold attrType? at hf
        cases hy : (H₂ u).find? (·.1 == q.1) with
        | none => rw [hy] at hf; cases hf
        | some y =>
          rw [hy] at hf
          simp only [Option.map_some, Option.some.injEq] at hf
          have hyk : y.1 = q.1 := by simpa using List.find?_some hy
          have : y = q := Prod.ext hyk hf
          rw [← this]
          exact h₂.sub u y (List.mem_of_find?_eq_some hy)
    have henvs : ∀ env' : TypeEnv, env'.ets = P.actionSchema.ets →
        env'.acts.toList.map Prod.fst = P.actionSchema.acts.toList.map Prod.fst →
        ∀ q ∈ H, q.2.validateWellFormed env' = .ok () := by
      intro env' h₁' h₂' q hq
      rw [Frontend.qualifiedType_validateWellFormed_getType]
      exact (hok q hq env' h₁' h₂').1
    refine ⟨⟨(Map.wellFormed_correct.mpr (Map.make_wf _) : Map.wellFormed (Map.make (e'.context.toList ++ H₂ u)) = true), fun q hq => ?_⟩, fun q hq => ?_⟩
    · rcases hsrc q hq with hq' | hq'
      · rw [Frontend.qualifiedType_validateWellFormed_congr (env := env₁) (env' := env₂) rfl hkeys]
        exact hc.2 q hq'
      · exact henvs _ rfl (augmentWith_keys _ _) q hq'
    · rcases hsrc q hq with hq' | hq'
      · exact hl q hq'
      · exact (hok q hq' { ets := P.actionSchema.ets, acts := P.actionSchema.acts, reqty := default }
          rfl rfl).2
  · -- The request type: the action's entry, found in a well-formed action schema.
    have hwfm : Map.WellFormed P.actionSchema.acts := by
      have hm := hA
      simp only [ActionSchema.validateWellFormed] at hm
      have hb : Map.wellFormed (Schema.augmentWith P.actionSchema H₁).acts = true := by
        cases hb : Map.wellFormed (Schema.augmentWith P.actionSchema H₁).acts
        · rw [hb] at hm; simp at hm
        · rfl
      rw [Map.wellFormed_correct, Map.wf_iff_sorted] at hb
      rw [Map.wf_iff_sorted]
      exact (List.map_eq_implies_sortedBy (augmentWith_keys _ _)).mp hb
    have hfind : (Schema.augmentWith P.actionSchema H₂).acts.find? a =
        some (augmentEntry (H₂ a) e) := by
      rw [augmentWith_find?, Map.mem_toList_find? hwfm he]
      rfl
    have hpc : (augmentEntry (H₂ a) e).appliesToPrincipal.contains pr = true :=
      Cedar.Data.Set.contains_prop_bool_equiv.mpr ((Cedar.Data.Set.mem_elts_iff_mem_set _ _).mp hp)
    have hrc : (augmentEntry (H₂ a) e).appliesToResource.contains rs = true :=
      Cedar.Data.Set.contains_prop_bool_equiv.mpr ((Cedar.Data.Set.mem_elts_iff_mem_set _ _).mp hr)
    simp only [env₂, Cedar.Validation.RequestType.validateWellFormed, hfind, hpc, hrc,
      beq_self_eq_true, ↓reduceIte, Except.bind_ok]

/-- A schema's ancestor check reads its entity types only, when it has an environment. -/
theorem standardAncestors_eq (S : Schema) :
    S.standardAncestors = (S.environments.isEmpty || S.ets.toList.all fun (_, e) =>
      e.ancestors.toList.all fun anc => (S.ets.find? anc).all (·.isStandard)) := by
  unfold Cedar.Validation.Schema.standardAncestors
  cases hE : S.environments with
  | nil => rfl
  | cons env envs =>
    simp only [List.isEmpty_cons, Bool.false_or]
    have hets : ∀ env' ∈ S.environments, env'.ets = S.ets := by
      intro env' h
      obtain ⟨_, _, _, _, _, _, _, rfl⟩ := mem_environments.mp h
      rfl
    rw [hE] at hets
    rw [Bool.eq_iff_iff, List.all_eq_true]
    constructor
    · intro h
      have := h env List.mem_cons_self
      rwa [hets env List.mem_cons_self] at this
    · intro h env' henv'
      rwa [hets env' henv']

theorem forall₂_length {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : l₁.length = l₂.length := by
  induction h <;> simp_all

/-- **Two augmentations have the same ancestor check.** -/
theorem standardAncestors_augmentWith (A : Schema) (H₁ H₂ : EntityUID → List (Attr × QualifiedType)) :
    (Schema.augmentWith A H₁).standardAncestors = (Schema.augmentWith A H₂).standardAncestors := by
  rw [standardAncestors_eq, standardAncestors_eq]
  have hlen := forall₂_length (Frontend.Augment.Typecheck.environments_pair
    (sameSkeleton_augmentWith A H₁ H₂))
  have : (Schema.augmentWith A H₁).environments.isEmpty =
      (Schema.augmentWith A H₂).environments.isEmpty := by
    rcases h1 : (Schema.augmentWith A H₁).environments with _ | ⟨x, xs⟩ <;>
      rcases h2 : (Schema.augmentWith A H₂).environments with _ | ⟨y, ys⟩ <;>
      rw [h1, h2] at hlen <;> simp_all
  rw [this]
  rfl

end

/-! ## Validity, against the selective schema and against the all-action one -/

/-- **Validity with every leaf's attribute added to every action**: `PolicySet.Valid`, with the
schema checks and Cedar's validation stated against `PolicySet.allAugmentedSchema`. It is
validity (`valid_iff_validAll`); the proofs about a valid set's decisions use this form. -/
structure _root_.Dogwood.Spec.PolicySet.ValidAll (P : PolicySet) : Prop where
  leafTypes : P.hoistedTypes?.isSome = true
  namesNodup : P.hoistedNames.Nodup
  namesFresh : ∀ act ∈ P.actionSchema.acts.toList, ∀ a ∈ P.hoistedNames,
    act.2.context.find? a = none
  readsContext : P.leafList ≠ [] → ∀ p ∈ P.policies, p.toExpr.ReadsContext P.hoistedNames
  wellFormed : P.allAugmentedSchema.validateWellFormed = .ok ()
  standardAncestors : P.allAugmentedSchema.standardAncestors = true
  complete : P.policies ≠ [] → P.externalTypes = [] ∧ P.externalActions = []
  cedar : Cedar.Validation.validate P.lowered P.allAugmentedSchema = .ok ()
  temporal : ∀ p ∈ P.policies, ∀ φ F, (.inl φ, F) ∈ p.toExpr.leafFacts [] → P.LeafValid p F φ
  providers : ∀ p ∈ P.policies, ∀ c F, (.inr c, F) ∈ p.toExpr.leafFacts [] →
    c.Declared P.providerDecls ∧ ∀ env ∈ P.envsOf p, c.TypedIn (P.typingCtx env F) P.providerDecls
  horizon : ∀ H, P.maxHorizon = some H → ∀ φ ∈ P.temporalLeaves, φ.horizon .seconds ≤ H

private theorem nodup_of_sortedBy' {α β : Type} [LT α] [Cedar.Data.StrictLT α] :
    ∀ {l : List (α × β)}, l.SortedBy Prod.fst → (l.map Prod.fst).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_of_sortedBy' (List.tail_sortedBy h)⟩
    obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hm
    have := List.sortedBy_implies_head_lt_tail h y hy
    rw [hxy] at this
    exact Cedar.Data.StrictLT.irreflexive _ this

/-- Cedar's validator accepts rules only against a schema with a request environment. -/
theorem environments_ne_nil_of_validate {ps : Cedar.Spec.Policies} {S : Schema} (hne : ps ≠ [])
    (h : Cedar.Validation.validate ps S = .ok ()) : S.environments ≠ [] := by
  intro he
  cases ps with
  | nil => exact hne rfl
  | cons p ps =>
    unfold Cedar.Validation.validate at h
    simp only [List.forM, Cedar.Validation.typecheckPolicyWithEnvironments, he,
      List.mapM_nil] at h
    revert h
    cases (Cedar.Validation.checkEntities S p.toExpr).mapError
        (Cedar.Validation.ValidationError.typeError p.id) <;>
      simp [bind, Except.bind, Cedar.Validation.allFalse, pure, Except.pure]

/-- A well-formed augmentation with a request environment declares each action once. -/
theorem acts_nodup_of_wellFormed {A : Schema} {Hk : EntityUID → List (Attr × QualifiedType)}
    (hwf : (Schema.augmentWith A Hk).validateWellFormed = .ok ())
    (hne : (Schema.augmentWith A Hk).environments ≠ []) : (A.acts.toList.map Prod.fst).Nodup := by
  obtain ⟨env, henv⟩ := List.exists_mem_of_ne_nil _ hne
  have h := acts_ok_of_env (List.forM_ok_implies_all_ok _ _ hwf env henv)
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := mem_environments.mp henv
  simp only [ActionSchema.validateWellFormed] at h
  have hb : Map.wellFormed (Schema.augmentWith A Hk).acts = true := by
    cases hb : Map.wellFormed (Schema.augmentWith A Hk).acts
    · rw [hb] at h; simp at h
    · rfl
  rw [Map.wellFormed_correct, Map.wf_iff_sorted] at hb
  rw [← augmentWith_keys A Hk]
  exact nodup_of_sortedBy' hb

theorem augmentedSchema_eq_augmentWith {P : PolicySet} {H : List (Attr × QualifiedType)}
    (hH : P.hoistedTypes? = some H) :
    P.augmentedSchema = Schema.augmentWith P.actionSchema (P.targetedAt H) := by
  unfold PolicySet.augmentedSchema PolicySet.selectiveAugment
  rw [hH]; rfl

theorem allAugmentedSchema_eq_augmentWith {P : PolicySet} {H : List (Attr × QualifiedType)}
    (hH : P.hoistedTypes? = some H) :
    P.allAugmentedSchema = Schema.augmentWith P.actionSchema (fun _ => H) := by
  unfold PolicySet.allAugmentedSchema
  rw [hH]; rfl

/-- The Cedar part of validity, against one augmentation that covers the leaves, carries to
another. -/
theorem cedarPart_covers {P : PolicySet} {k : Nat} {H : List (Attr × QualifiedType)}
    (hH : P.hoistedTypesFrom? k = some H) (hnd : (P.hoistedNamesFrom k).Nodup)
    (hfresh : ∀ act ∈ P.actionSchema.acts.toList, ∀ a ∈ P.hoistedNamesFrom k,
      act.2.context.find? a = none)
    (hrc : P.leafList ≠ [] → ∀ p ∈ P.policies, p.toExpr.ReadsContext (P.hoistedNamesFrom k))
    {H₁ H₂ : EntityUID → List (Attr × QualifiedType)} (h₁ : P.Covers H H₁) (h₂ : P.Covers H H₂)
    (hwf : (Schema.augmentWith P.actionSchema H₁).validateWellFormed = .ok ())
    (hval : Cedar.Validation.validate (P.loweredFrom k) (Schema.augmentWith P.actionSchema H₁) =
      .ok ()) :
    (Schema.augmentWith P.actionSchema H₂).validateWellFormed = .ok () ∧
      (Schema.augmentWith P.actionSchema H₂).standardAncestors =
        (Schema.augmentWith P.actionSchema H₁).standardAncestors ∧
      Cedar.Validation.validate (P.loweredFrom k) (Schema.augmentWith P.actionSchema H₂) =
        .ok () := by
  refine ⟨wellFormed_of_covers hH hnd hfresh h₁ h₂ hval hwf,
    standardAncestors_augmentWith _ _ _, ?_⟩
  by_cases hl : P.loweredFrom k = []
  · rw [hl]; rfl
  have hacts := acts_nodup_of_wellFormed hwf (environments_ne_nil_of_validate hl hval)
  exact (validate_covers_iff hH hnd hrc hacts h₁ h₂).mp hval

/-- **Validity is validity against the all-action schema**: adding every leaf's attribute to every
action, rather than only to the actions its rule's action scope admits, changes no verdict. -/
theorem valid_iff_validAll {P : PolicySet} : P.Valid ↔ P.ValidAll := by
  constructor
  · intro hv
    obtain ⟨H, hH⟩ := Option.isSome_iff_exists.mp hv.leafTypes
    have hwf := hv.wellFormed
    have hval := hv.cedar
    have hstd := hv.standardAncestors
    rw [augmentedSchema_eq_augmentWith hH] at hwf hval hstd
    obtain ⟨h₁, h₂, h₃⟩ := cedarPart_covers (k := 0) hH (by rw [hoistedNamesFrom_zero]; exact hv.namesNodup)
      (by rw [hoistedNamesFrom_zero]; exact hv.namesFresh)
      (by rw [hoistedNamesFrom_zero]; exact hv.readsContext)
      (covers_targetedAt P H) (covers_all P H) hwf hval
    exact ⟨hv.leafTypes, hv.namesNodup, hv.namesFresh, hv.readsContext,
      by rw [allAugmentedSchema_eq_augmentWith hH]; exact h₁,
      by rw [allAugmentedSchema_eq_augmentWith hH, h₂]; exact hstd, hv.complete,
      by rw [allAugmentedSchema_eq_augmentWith hH]; exact h₃, hv.temporal, hv.providers, hv.horizon⟩
  · intro hv
    obtain ⟨H, hH⟩ := Option.isSome_iff_exists.mp hv.leafTypes
    have hwf := hv.wellFormed
    have hval := hv.cedar
    have hstd := hv.standardAncestors
    rw [allAugmentedSchema_eq_augmentWith hH] at hwf hval hstd
    obtain ⟨h₁, h₂, h₃⟩ := cedarPart_covers (k := 0) hH (by rw [hoistedNamesFrom_zero]; exact hv.namesNodup)
      (by rw [hoistedNamesFrom_zero]; exact hv.namesFresh)
      (by rw [hoistedNamesFrom_zero]; exact hv.readsContext)
      (covers_all P H) (covers_targetedAt P H) hwf hval
    exact ⟨hv.leafTypes, hv.namesNodup, hv.namesFresh, hv.readsContext,
      by rw [augmentedSchema_eq_augmentWith hH]; exact h₁,
      by rw [augmentedSchema_eq_augmentWith hH, h₂]; exact hstd, hv.complete,
      by rw [augmentedSchema_eq_augmentWith hH]; exact h₃, hv.temporal, hv.providers, hv.horizon⟩

theorem _root_.Dogwood.Spec.PolicySet.Valid.toAll {P : PolicySet} (hv : P.Valid) : P.ValidAll :=
  valid_iff_validAll.mp hv

theorem _root_.Dogwood.Spec.PolicySet.ValidAll.toValid {P : PolicySet} (hv : P.ValidAll) :
    P.Valid :=
  valid_iff_validAll.mpr hv

/-- **Validation against any augmentation that covers the leaves** gives validity's verdict: the
general form of "adding the attributes to more actions is safe". -/
theorem valid_iff_covers {P : PolicySet} {H : List (Attr × QualifiedType)}
    (hH : P.hoistedTypes? = some H) {Hk : EntityUID → List (Attr × QualifiedType)}
    (hk : P.Covers H Hk) :
    P.Valid ↔ P.hoistedNames.Nodup ∧
      (∀ act ∈ P.actionSchema.acts.toList, ∀ a ∈ P.hoistedNames, act.2.context.find? a = none) ∧
      (P.leafList ≠ [] → ∀ p ∈ P.policies, p.toExpr.ReadsContext P.hoistedNames) ∧
      (Schema.augmentWith P.actionSchema Hk).validateWellFormed = .ok () ∧
      (Schema.augmentWith P.actionSchema Hk).standardAncestors = true ∧
      (P.policies ≠ [] → P.externalTypes = [] ∧ P.externalActions = []) ∧
      Cedar.Validation.validate P.lowered (Schema.augmentWith P.actionSchema Hk) = .ok () ∧
      (∀ p ∈ P.policies, ∀ φ F, (.inl φ, F) ∈ p.toExpr.leafFacts [] → P.LeafValid p F φ) ∧
      (∀ p ∈ P.policies, ∀ c F, (.inr c, F) ∈ p.toExpr.leafFacts [] →
        c.Declared P.providerDecls ∧ ∀ env ∈ P.envsOf p, c.TypedIn (P.typingCtx env F) P.providerDecls) ∧
      (∀ H, P.maxHorizon = some H → ∀ φ ∈ P.temporalLeaves, φ.horizon .seconds ≤ H) := by
  have hsome : P.hoistedTypes?.isSome = true := by rw [hH]; rfl
  constructor
  · intro hv
    have hwf := hv.wellFormed
    have hval := hv.cedar
    have hstd := hv.standardAncestors
    rw [augmentedSchema_eq_augmentWith hH] at hwf hval hstd
    obtain ⟨h₁, h₂, h₃⟩ := cedarPart_covers (k := 0) hH (by rw [hoistedNamesFrom_zero]; exact hv.namesNodup)
      (by rw [hoistedNamesFrom_zero]; exact hv.namesFresh)
      (by rw [hoistedNamesFrom_zero]; exact hv.readsContext)
      (covers_targetedAt P H) hk hwf hval
    exact ⟨hv.namesNodup, hv.namesFresh, hv.readsContext, h₁, by rw [h₂]; exact hstd, hv.complete,
      h₃, hv.temporal, hv.providers, hv.horizon⟩
  · rintro ⟨hnd, hfresh, hrc, hwf, hstd, hcomp, hval, htemp, hprov, hhor⟩
    obtain ⟨h₁, h₂, h₃⟩ := cedarPart_covers (k := 0) hH (by rw [hoistedNamesFrom_zero]; exact hnd)
      (by rw [hoistedNamesFrom_zero]; exact hfresh) (by rw [hoistedNamesFrom_zero]; exact hrc)
      hk (covers_targetedAt P H) hwf hval
    exact ⟨hsome, hnd, hfresh, hrc, by rw [augmentedSchema_eq_augmentWith hH]; exact h₁,
      by rw [augmentedSchema_eq_augmentWith hH, h₂]; exact hstd, hcomp,
      by rw [augmentedSchema_eq_augmentWith hH]; exact h₃, htemp, hprov, hhor⟩

/-! ## Validity of a lowering from an offset -/

/-- `PolicySet.ValidFrom`, with the schema checks and Cedar's validation stated against the schema
that adds every attribute of the lowering to every action (`allAugmentedSchemaFrom`). -/
structure _root_.Dogwood.Spec.PolicySet.ValidFromAll (P : PolicySet) (k : Nat) : Prop where
  leafTypes : (P.hoistedTypesFrom? k).isSome = true
  namesNodup : (P.hoistedNamesFrom k).Nodup
  namesFresh : ∀ act ∈ P.actionSchema.acts.toList, ∀ a ∈ P.hoistedNamesFrom k,
    act.2.context.find? a = none
  readsContext : P.leafList ≠ [] → ∀ p ∈ P.policies, p.toExpr.ReadsContext (P.hoistedNamesFrom k)
  wellFormed : (P.allAugmentedSchemaFrom k).validateWellFormed = .ok ()
  standardAncestors : (P.allAugmentedSchemaFrom k).standardAncestors = true
  complete : P.policies ≠ [] → P.externalTypes = [] ∧ P.externalActions = []
  cedar : Cedar.Validation.validate (P.loweredFrom k) (P.allAugmentedSchemaFrom k) = .ok ()
  temporal : ∀ p ∈ P.policies, ∀ φ F, (.inl φ, F) ∈ p.toExpr.leafFacts [] → P.LeafValid p F φ
  providers : ∀ p ∈ P.policies, ∀ c F, (.inr c, F) ∈ p.toExpr.leafFacts [] →
    c.Declared P.providerDecls ∧ ∀ env ∈ P.envsOf p, c.TypedIn (P.typingCtx env F) P.providerDecls
  horizon : ∀ H, P.maxHorizon = some H → ∀ φ ∈ P.temporalLeaves, φ.horizon .seconds ≤ H

theorem augmentedSchemaFrom_eq_augmentWith {P : PolicySet} {k : Nat}
    {H : List (Attr × QualifiedType)} (hH : P.hoistedTypesFrom? k = some H) :
    P.augmentedSchemaFrom k = Schema.augmentWith P.actionSchema (P.targetedAt H) := by
  unfold PolicySet.augmentedSchemaFrom PolicySet.selectiveAugment
  rw [hH]; rfl

theorem allAugmentedSchemaFrom_eq_augmentWith {P : PolicySet} {k : Nat}
    {H : List (Attr × QualifiedType)} (hH : P.hoistedTypesFrom? k = some H) :
    P.allAugmentedSchemaFrom k = Schema.augmentWith P.actionSchema (fun _ => H) := by
  unfold PolicySet.allAugmentedSchemaFrom
  rw [hH]; rfl

/-- **Validity of a lowering from an offset is validity against the all-action schema.** -/
theorem validFrom_iff_validFromAll {P : PolicySet} {k : Nat} : P.ValidFrom k ↔ P.ValidFromAll k := by
  constructor
  · intro hv
    obtain ⟨H, hH⟩ := Option.isSome_iff_exists.mp hv.leafTypes
    have hwf := hv.wellFormed
    have hval := hv.cedar
    have hstd := hv.standardAncestors
    rw [augmentedSchemaFrom_eq_augmentWith hH] at hwf hval hstd
    obtain ⟨h₁, h₂, h₃⟩ := cedarPart_covers hH hv.namesNodup hv.namesFresh hv.readsContext
      (covers_targetedAt P H) (covers_all P H) hwf hval
    exact ⟨hv.leafTypes, hv.namesNodup, hv.namesFresh, hv.readsContext,
      by rw [allAugmentedSchemaFrom_eq_augmentWith hH]; exact h₁,
      by rw [allAugmentedSchemaFrom_eq_augmentWith hH, h₂]; exact hstd, hv.complete,
      by rw [allAugmentedSchemaFrom_eq_augmentWith hH]; exact h₃, hv.temporal, hv.providers, hv.horizon⟩
  · intro hv
    obtain ⟨H, hH⟩ := Option.isSome_iff_exists.mp hv.leafTypes
    have hwf := hv.wellFormed
    have hval := hv.cedar
    have hstd := hv.standardAncestors
    rw [allAugmentedSchemaFrom_eq_augmentWith hH] at hwf hval hstd
    obtain ⟨h₁, h₂, h₃⟩ := cedarPart_covers hH hv.namesNodup hv.namesFresh hv.readsContext
      (covers_all P H) (covers_targetedAt P H) hwf hval
    exact ⟨hv.leafTypes, hv.namesNodup, hv.namesFresh, hv.readsContext,
      by rw [augmentedSchemaFrom_eq_augmentWith hH]; exact h₁,
      by rw [augmentedSchemaFrom_eq_augmentWith hH, h₂]; exact hstd, hv.complete,
      by rw [augmentedSchemaFrom_eq_augmentWith hH]; exact h₃, hv.temporal, hv.providers, hv.horizon⟩

/-- **Every leaf's attribute is in the context of an action of the schema**, in an augmentation
that covers the leaves and validates the lowered rules: the leaf's rule is typed other than
`False` at some action, which its action scope therefore admits. -/
theorem leaf_targeted {P : PolicySet} {k : Nat} {H : List (Attr × QualifiedType)}
    (hH : P.hoistedTypesFrom? k = some H) {Hk : EntityUID → List (Attr × QualifiedType)}
    (hk : P.Covers H Hk)
    (hval : Cedar.Validation.validate (P.loweredFrom k) (Schema.augmentWith P.actionSchema Hk) =
      .ok ())
    {i : Nat} (hi : i < H.length) :
    ∃ a e, (a, e) ∈ P.actionSchema.acts.toList ∧ H[i] ∈ Hk a := by
  have hHkeys : H.map (·.1) = P.hoistedNamesFrom k := keys_hoistedTypesFrom hH
  have hlen : H.length = P.leafScopes.length := by
    rw [leafScopes_length, ← List.length_map (f := (·.1)), hHkeys, PolicySet.hoistedNamesFrom,
      List.length_map, List.length_range']
  obtain ⟨q, hq, hs⟩ := leafScope_of_index (k := k) (hlen ▸ hi)
  have htc := List.forM_ok_implies_all_ok _ _ hval q hq
  obtain ⟨env₁, henv₁, tx, c, hty, hne⟩ := nonff_of_typecheck htc
  obtain ⟨a, entry, pr, rs, hmem, -, -, henv⟩ := mem_environments.mp henv₁
  have hacts₁ : env₁.acts = (Schema.augmentWith P.actionSchema Hk).acts := by rw [henv]
  have hact₁ : env₁.reqty.action = a := by rw [henv]
  obtain ⟨e, he, rfl⟩ := mem_augmentWith_toList hmem
  have had := actionScopeAdmits_of_policy (A := P.actionSchema)
    (fun x y => by rw [hacts₁, augmentWith_descendentOf])
    (by rw [hacts₁, augmentWith_contains, hact₁]; exact contains_of_mem_toList he) hty hne
  rw [hact₁] at had
  exact ⟨a, e, he, hk.cover a _ (mem_targetedAt hi hs had)⟩

end Dogwood.Thm
