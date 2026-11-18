import Dogwood.Spec.SequentialLowering
import Dogwood.Thm.CedarSoundness
import Dogwood.Thm.Frontend.Augment.Selective
import Dogwood.Thm.ContextReads
import Dogwood.Thm.Frontend.Cedarify.Names
import Dogwood.Thm.ValidityDecide
import Dogwood.Thm.Frontend.Validate.Schema

/-!
# Composition: two lowerings in sequence

A policy set can be lowered against a schema that an earlier lowering augmented (the crate's
`lower_with_distincter`, "feeding an augmented schema forward"): lower `A` against its action
schema `S`, then lower new rules `qs` against `A`'s augmented schema, and deploy both in one
Cedar policy store. The crate keeps the two sets' hoisted attributes apart with a distincter; in
the specification, whose leaf attributes are `leafAttr k`, a distincter is an offset: the second
set's leaves are numbered after the first's (`Dogwood.Spec.SequentialLowering`:
`PolicySet.ValidFrom k`).
`A.next qs` is the second lowering's policy set, `A.join qs` the two together. Both share `A`'s
service schema: the model covers feed-forward lowering under one service schema, while the crate
parses each set with a service schema of its own.

* **The joint lowering is the sequence** (`lowered_join`, `augmentedSchema_join`): `A.join qs`
  lowers to `A`'s lowered rules followed by `qs` lowered after them, and its augmented schema is
  the second lowering's augmentation of `A`'s augmented schema (`augmentWith_augmentWith`,
  `targetedAt_join`): both schemas are action-selective, as the crate's are, so the second
  lowering sees `A`'s attributes only on the actions `A`'s rules can apply to.
* **Composition** (`valid_join`): if `A` is valid, the second lowering is valid against `A`'s
  augmented schema, and neither set reads the other's hoisted attributes (the Cedar part of
  `A`'s rules; the Cedar part, temporal leaves, and provider arguments of `qs`'s rules; and the
  event schema's pins), then `A.join qs` is valid against `S`. It then decides as the soundness
  theorems say of a valid set.
* **Under the joint context-read check** (`valid_join_of_contextReadsOk`,
  `valid_join_iff_contextReadsOk`): the Cedar-part read hypotheses are exactly the joint set's
  context-read check (`PolicySet.contextReadsOk`, schema-free). So, when each lowering is valid
  on its own and the second set's leaves and the event schema's pins read none of the first
  set's attributes, sequential lowering is valid exactly when the combined set passes that check.
  Its whole-context part is needed: a rule of the first set that reads `context` whole breaks
  composition once the second set has a leaf (`not_valid_join_of_whole_context_read`). Each
  lowering's own check does not catch this, since a set without leaves may read `context` whole;
  `Validator::validate` on the result of `lower_many`, which checks the combined set, does. The
  crate reserves hoisted-shaped names across lowerings (`is_hoisted_name`), but not whole-context
  reads of a set without leaves.
* **The same names twice fail** (`not_validFrom_next_of_lt`): when `A` is valid, a second lowering
  that numbers its leaves from an offset below the first set's leaf count is never valid, since
  its first name is in the context of an action `A`'s rule can apply to, and the second lowering
  requires every action's context to leave its names free. The crate refuses a schema in which
  any action's context declares a leaf's name (`reject_declared_leaf_names`); since it augments
  only a rule's target actions, the clash shows there.

The Cedar part of composition is `Frontend.Augment.Typecheck.typecheckPolicyWithEnvironments_agree`
applied to the context attributes a lowered rule reads (`ctxReads`, `CtxAvoids`,
`ctxAvoids_lowerFrom`); the temporal part is a typing transfer between contexts that agree but at
the first set's attributes (`Formula.WellTyped.of_agree`, `Provider.Call.TypedIn.of_agree`). That
the schema declares each action once, which the Cedar part needs, follows from validity
(`actions_nodup_of_valid`).
-/

namespace Dogwood.Spec.Temporal

open Cedar.Spec (Attr)

theorem Formula.argsAvoidContext_mem {N : List Attr} :
    ∀ {args : List (Path × Term)}, Formula.argsAvoidContext N args →
      ∀ arg ∈ args, arg.2.AvoidsContext N
  | [], _, _, h => by cases h
  | (_, t) :: args, h, arg, harg => by
    simp only [Formula.argsAvoidContext] at h
    rcases List.mem_cons.mp harg with rfl | harg
    · exact h.1
    · exact Formula.argsAvoidContext_mem h.2 arg harg

/-- Two typing contexts that differ at most in the context record, and there only at the
attributes in `N`. -/
structure CtxAgree (N : List Attr) (C₁ C₂ : TypingCtx) : Prop where
  ets : C₁.env.ets = C₂.env.ets
  principal : C₁.env.reqty.principal = C₂.env.reqty.principal
  resource : C₁.env.reqty.resource = C₂.env.reqty.resource
  contains : ∀ uid, C₁.env.acts.contains uid = C₂.env.acts.contains uid
  events : C₁.events = C₂.events
  maxWindow : C₁.maxWindow = C₂.maxWindow
  facts : C₁.facts = C₂.facts
  context : ∀ a, a ∉ N → C₁.env.reqty.context.find? a = C₂.env.reqty.context.find? a

theorem pathType?_congr {present : Path → Bool} {r₁ r₂ : Cedar.Validation.RecordType}
    {pre : Path} {a : Attr} (p : Path) (h : r₁.find? a = r₂.find? a) :
    pathType? present r₁ pre (a :: p) = pathType? present r₂ pre (a :: p) := by
  simp only [pathType?, h]

theorem CtxAgree.contextType? {N : List Attr} {C₁ C₂ : TypingCtx} (h : CtxAgree N C₁ C₂)
    {p : Path} (hp : headAvoids N p) : C₁.contextType? p = C₂.contextType? p := by
  cases p with
  | nil => rfl
  | cons a p =>
    simp only [TypingCtx.contextType?, h.facts]
    exact pathType?_congr p (h.context a hp)

theorem CtxAgree.scopeType {N : List Attr} {C₁ C₂ : TypingCtx} (h : CtxAgree N C₁ C₂)
    (r : ScopeRoot) : C₁.scopeType r = C₂.scopeType r := by
  cases r
  · exact h.principal
  · exact h.resource

theorem CtxAgree.scopeAttrType? {N : List Attr} {C₁ C₂ : TypingCtx} (h : CtxAgree N C₁ C₂)
    (r : ScopeRoot) (p : Path) : C₁.scopeAttrType? r p = C₂.scopeAttrType? r p := by
  simp only [TypingCtx.scopeAttrType?, h.ets, h.scopeType, h.facts]

theorem CtxAgree.pinsTyped {N : List Attr} {C₁ C₂ : TypingCtx} (h : CtxAgree N C₁ C₂)
    {sig : EventSignature} (hpins : ∀ pin ∈ sig.pins, ∀ p, pin.ref = .context p → headAvoids N p)
    (hs : sig.PinsTyped C₁) : sig.PinsTyped C₂ := by
  intro pin hpin
  obtain ⟨fd, τ, hf, hsort, hacc⟩ := hs pin hpin
  refine ⟨fd, τ, hf, ?_, hacc⟩
  have h' : CtxAgree N { C₁ with facts := [] } { C₂ with facts := [] } :=
    { h with facts := rfl }
  rw [← hsort]
  cases hr : pin.ref with
  | context p =>
    simp only [PinRef.sort?]
    rw [h'.contextType? (hpins pin hpin p hr)]
  | scope r p =>
    cases p with
    | nil => simp only [PinRef.sort?, h'.scopeType]
    | cons a p => simp only [PinRef.sort?, h'.scopeAttrType?]

variable {N : List Attr} {C₁ C₂ : TypingCtx}

-- The members of a mutual block reach a section hypothesis only through each other's calls,
-- which the unused-variable linter does not see.
set_option linter.unusedSectionVars false in
mutual

/-- **Typing does not see context attributes a term does not read.** -/
theorem Term.Typed.of_agree (h : CtxAgree N C₁ C₂) (hpins : PinsAvoid N C₁.events)
    {Γ : Bindings} {t : Term} {τ : TType} :
    t.AvoidsContext N → Term.Typed C₁ Γ t τ → Term.Typed C₂ Γ t τ
  | _, .entity hu => .entity (by rw [← h.ets, ← h.contains]; exact hu)
  | _, .long => .long
  | _, .decimal hd => .decimal hd
  | _, .string => .string
  | _, .bool => .bool
  | ha, .context hc hs => .context (by rw [← h.contextType? ha]; exact hc) hs
  | _, .scopeRoot => by rw [h.scopeType]; exact .scopeRoot
  | _, .scopeAttr h₁ h₂ hs => .scopeAttr h₁ (by rw [← h.scopeAttrType?]; exact h₂) hs
  | _, .var hl => .var hl
  | ha, .agg hg => .agg (Aggregate.Typed.of_agree h hpins ha hg)
  | ha, .arith hl hr =>
    .arith (Term.Typed.of_agree h hpins ha.1 hl) (Term.Typed.of_agree h hpins ha.2 hr)

theorem Aggregate.Typed.of_agree (h : CtxAgree N C₁ C₂) (hpins : PinsAvoid N C₁.events)
    {Γ : Bindings} {a : Aggregate} :
    a.AvoidsContext N → Aggregate.Typed C₁ Γ a → Aggregate.Typed C₂ Γ a
  | ha, .count hd hb =>
    .count (by rw [← h.ets]; exact hd) (Formula.WellTyped.of_agree h hpins ha hb)
  | ha, .sum hd hs hb =>
    .sum (by rw [← h.ets]; exact hd) hs (Formula.WellTyped.of_agree h hpins ha hb)

/-- **Typing does not see context attributes a formula does not read**, when the event
schema's pins do not read them either. -/
theorem Formula.WellTyped.of_agree (h : CtxAgree N C₁ C₂) (hpins : PinsAvoid N C₁.events)
    {Γ : Bindings} {φ : Formula} :
    φ.AvoidsContext N → Formula.WellTyped C₁ Γ φ → Formula.WellTyped C₂ Γ φ
  | ha, .and h₁ h₂ => .and (Formula.WellTyped.of_agree h hpins ha.1 h₁)
      (Formula.WellTyped.of_agree h hpins ha.2 h₂)
  | ha, .not h₁ => .not (Formula.WellTyped.of_agree h hpins ha h₁)
  | ha, .formerly hw h₁ => .formerly (by rw [← h.maxWindow]; exact hw)
      (Formula.WellTyped.of_agree h hpins ha h₁)
  | ha, .previous hw h₁ => .previous (by rw [← h.maxWindow]; exact hw)
      (Formula.WellTyped.of_agree h hpins ha h₁)
  | ha, .since hw h₁ h₂ => .since (by rw [← h.maxWindow]; exact hw)
      (Formula.WellTyped.of_agree h hpins ha.1 h₁) (Formula.WellTyped.of_agree h hpins ha.2 h₂)
  | ha, .pred hsig hargs hp =>
    .pred (by rw [← h.events]; exact hsig)
      (fun arg harg => Formula.ArgTyped.of_agree h hpins
        (Formula.argsAvoidContext_mem ha arg harg) (hargs arg harg))
      (h.pinsTyped (fun pin hpin => hpins _ (List.mem_of_find?_eq_some hsig) pin hpin) hp)
  | ha, .eq hop hl hr hc =>
    .eq hop (Term.Typed.of_agree h hpins ha.1 hl) (Term.Typed.of_agree h hpins ha.2 hr) hc
  | ha, .ord hop hl hr =>
    .ord hop (Term.Typed.of_agree h hpins ha.1 hl) (Term.Typed.of_agree h hpins ha.2 hr)
  | ha, .exist hs h₁ =>
    .exist (by rw [← h.ets]; exact hs) (Formula.WellTyped.of_agree h hpins ha h₁)
  | _, .tp hl => .tp hl

theorem Formula.ArgTyped.of_agree (h : CtxAgree N C₁ C₂) (hpins : PinsAvoid N C₁.events)
    {Γ : Bindings} {sig : EventSignature}
    {a : Path × Term} :
    a.2.AvoidsContext N → Formula.ArgTyped C₁ Γ sig a → Formula.ArgTyped C₂ Γ sig a
  | _, .wildcard hf => .wildcard hf
  | _, .var hf hl hw => .var hf hl hw
  | ha, .term hf hs hv hw ht hacc => .term hf hs hv hw (Term.Typed.of_agree h hpins ha ht) hacc

end

end Dogwood.Spec.Temporal


namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Attr EntityUID Var)
open Cedar.Validation (Schema QualifiedType TypeEnv ActionSchemaEntry)
open Cedar.Data (Map)
open Dogwood.Frontend.Augment.Typecheck (ReadsOnly ReadsOnlyList ReadsOnlyRecord)


/-- **Validity is validity of the lowering from `0`.** -/
theorem validFrom_zero_iff {P : PolicySet} : P.ValidFrom 0 ↔ P.Valid := by
  have hn := hoistedNamesFrom_zero P
  constructor
  · intro h
    exact ⟨h.leafTypes, hn ▸ h.namesNodup, hn ▸ h.namesFresh, hn ▸ h.readsContext, h.wellFormed,
      h.standardAncestors, h.complete, h.cedar, h.temporal, h.providers, h.horizon⟩
  · intro h
    exact ⟨h.leafTypes, hn ▸ h.namesNodup, hn ▸ h.namesFresh, hn ▸ h.readsContext, h.wellFormed,
      h.standardAncestors, h.complete, h.cedar, h.temporal, h.providers, h.horizon⟩


/-! ## Two lowerings in sequence, and together -/

variable {A : PolicySet} {qs : Policies}

theorem leafList_join : (A.join qs).leafList = A.leafList ++ (A.next qs).leafList := by
  simp [PolicySet.leafList, PolicySet.join, PolicySet.next, List.flatMap_append]

theorem leafList_join_length :
    (A.join qs).leafList.length = A.leafList.length + (A.next qs).leafList.length := by
  rw [leafList_join, List.length_append]

theorem policies_lowerFrom_snd : (ps : Policies) → (k : Nat) →
    (Policies.lowerFrom k ps).2 = k + (ps.flatMap (·.toExpr.leaves)).length
  | [], k => rfl
  | p :: ps, k => by
    simp only [Policies.lowerFrom, policies_lowerFrom_snd ps, policy_lowerFrom_snd,
      List.flatMap_cons, List.length_append]
    omega

theorem policies_lowerFrom_append : (ps qs : Policies) → (k : Nat) →
    (Policies.lowerFrom k (ps ++ qs)).1 =
      (Policies.lowerFrom k ps).1 ++ (Policies.lowerFrom (Policies.lowerFrom k ps).2 qs).1
  | [], qs, k => rfl
  | p :: ps, qs, k => by
    simp only [List.cons_append, Policies.lowerFrom, policies_lowerFrom_append ps qs]

/-- **The joint lowering is the two lowerings in sequence**: `A`'s, then `qs` lowered with its
leaves numbered after `A`'s. -/
theorem lowered_join :
    (A.join qs).lowered = A.lowered ++ (A.next qs).loweredFrom A.leafList.length := by
  show (Policies.lowerFrom 0 (A.policies ++ qs)).1 =
    (Policies.lowerFrom 0 A.policies).1 ++ (Policies.lowerFrom A.leafList.length qs).1
  rw [policies_lowerFrom_append, policies_lowerFrom_snd, Nat.zero_add]
  rfl

theorem hoistedNames_join :
    (A.join qs).hoistedNames =
      A.hoistedNames ++ (A.next qs).hoistedNamesFrom A.leafList.length := by
  simp only [PolicySet.hoistedNames, PolicySet.hoistedNamesFrom, leafList_join_length,
    List.range_eq_range', ← List.map_append]
  congr 1
  simpa using (List.range'_append (s := 0) (m := A.leafList.length)
    (n := (A.next qs).leafList.length) (step := 1)).symm

theorem hoistedTypes_join :
    (A.join qs).hoistedTypes? = (do
      let H₁ ← A.hoistedTypes?
      let H₂ ← (A.next qs).hoistedTypesFrom? A.leafList.length
      pure (H₁ ++ H₂)) := by
  unfold PolicySet.hoistedTypes? PolicySet.hoistedTypesFrom?
  rw [leafList_join, List.zipIdx_append, List.mapM_append, Nat.zero_add]
  rfl

private theorem make_make_append (c : Map Attr QualifiedType)
    (H₁ H₂ : List (Attr × QualifiedType)) :
    Map.make ((Map.make (c.toList ++ H₁)).toList ++ H₂) = Map.make (c.toList ++ (H₁ ++ H₂)) := by
  refine Map.find?_ext (Map.make_wf _) (Map.make_wf _) fun a => ?_
  rw [Frontend.Augment.find?_augmentedContext, Frontend.Augment.find?_augmentedContext,
    Frontend.Augment.find?_augmentedContext, List.lookup_append, Option.or_assoc]

private theorem toList_mk {α β : Type} (l : List (α × β)) : (Map.mk l).toList = l := rfl

/-- Augmenting twice is augmenting once, with both lists of attributes. -/
theorem augment_augment (S : Schema) (H₁ H₂ : List (Attr × QualifiedType)) :
    Schema.augment (Schema.augment S H₁) H₂ = Schema.augment S (H₁ ++ H₂) := by
  simp only [Schema.augment, Map.mapOnValues, toList_mk, List.map_map, Function.comp_def,
    make_make_append]

/-- Augmenting twice, action by action, is augmenting once, with both lists of attributes. -/
theorem augmentWith_augmentWith (S : Schema) (H₁ H₂ : EntityUID → List (Attr × QualifiedType)) :
    Schema.augmentWith (Schema.augmentWith S H₁) H₂ =
      Schema.augmentWith S (fun u => H₁ u ++ H₂ u) := by
  simp only [Schema.augmentWith, toList_mk, List.map_map, Function.comp_def, make_make_append]

theorem augmentWith_maybeDescendentOf (S : Schema) (Hk : EntityUID → List (Attr × QualifiedType))
    (e₁ e₂ : Cedar.Spec.EntityType) :
    (Schema.augmentWith S Hk).acts.maybeDescendentOf e₁ e₂ = S.acts.maybeDescendentOf e₁ e₂ := by
  simp only [Cedar.Validation.ActionSchema.maybeDescendentOf, augmentWith_acts_toList, List.any_map,
    Function.comp_def, augmentEntry]

theorem actionScopeAdmits_augmentWith (S : Schema) (Hk : EntityUID → List (Attr × QualifiedType)) :
    actionScopeAdmits (Schema.augmentWith S Hk) = actionScopeAdmits S := by
  funext act sc
  rcases sc with ⟨sc⟩ | ls
  · cases sc <;> simp [actionScopeAdmits, augmentWith_descendentOf]
  · simp [actionScopeAdmits, augmentWith_descendentOf]

theorem scopeAdmitsType_augmentWith (S : Schema) (Hk : EntityUID → List (Attr × QualifiedType)) :
    scopeAdmitsType (Schema.augmentWith S Hk) = scopeAdmitsType S := by
  funext sc ety
  cases sc <;> simp only [scopeAdmitsType, Schema.memberOfType, augmentWith_maybeDescendentOf,
    augmentWith_ets]

theorem leafScopes_join : (A.join qs).leafScopes = A.leafScopes ++ (A.next qs).leafScopes := by
  simp [PolicySet.leafScopes, PolicySet.join, PolicySet.next, List.flatMap_append]

theorem length_of_hoistedTypesFrom {P : PolicySet} {k : Nat} {H : List (Attr × QualifiedType)}
    (h : P.hoistedTypesFrom? k = some H) : H.length = P.leafScopes.length := by
  rw [leafScopes_length, ← List.length_map (f := Prod.fst), keys_hoistedTypesFrom h,
    PolicySet.hoistedNamesFrom, List.length_map, List.length_range']

/-- The joint set adds, at each action, `A`'s attributes there and then the second lowering's. -/
theorem targetedAt_join {H₁ H₂ : List (Attr × QualifiedType)}
    (h₁ : A.hoistedTypes? = some H₁)
    (h₂ : (A.next qs).hoistedTypesFrom? A.leafList.length = some H₂) (uid : EntityUID) :
    (A.join qs).targetedAt (H₁ ++ H₂) uid =
      A.targetedAt H₁ uid ++ (A.next qs).targetedAt H₂ uid := by
  have hl₁ : H₁.length = A.leafScopes.length := length_of_hoistedTypesFrom (k := 0) h₁
  unfold PolicySet.targetedAt
  rw [leafScopes_join, List.zip_append hl₁, List.filter_append, List.map_append]
  have hS : (A.join qs).actionSchema = A.actionSchema := rfl
  have hS' : (A.next qs).actionSchema = A.augmentedSchema := rfl
  obtain ⟨-, hA⟩ : True ∧ A.augmentedSchema = Schema.augmentWith A.actionSchema (A.targetedAt H₁) :=
    ⟨trivial, augmentedSchema_eq_augmentWith h₁⟩
  rw [hS, hS', hA, actionScopeAdmits_augmentWith]

/-- **The joint augmented schema is the second lowering's augmentation of the first's.** -/
theorem augmentedSchema_join {H₁ H₂ : List (Attr × QualifiedType)}
    (h₁ : A.hoistedTypes? = some H₁)
    (h₂ : (A.next qs).hoistedTypesFrom? A.leafList.length = some H₂) :
    (A.join qs).augmentedSchema = (A.next qs).augmentedSchemaFrom A.leafList.length := by
  have hJt : (A.join qs).hoistedTypes? = some (H₁ ++ H₂) := by
    rw [hoistedTypes_join, h₁, h₂]; rfl
  rw [augmentedSchema_eq_augmentWith hJt, augmentedSchemaFrom_eq_augmentWith h₂]
  show _ = Schema.augmentWith A.augmentedSchema _
  rw [augmentedSchema_eq_augmentWith h₁, augmentWith_augmentWith]
  congr 1
  funext uid
  exact targetedAt_join h₁ h₂ uid


/-! ## Names -/

theorem lookup_eq_none_of_not_mem {β : Type} {H : List (Attr × β)} {a : Attr}
    (h : a ∉ H.map Prod.fst) : H.lookup a = none :=
  List.lookup_eq_none_iff.mpr fun p hp => by
    have : a ≠ p.1 := fun he => h (List.mem_map.mpr ⟨p, hp, he.symm⟩)
    simpa using this

theorem lookup_isSome_of_mem {β : Type} {H : List (Attr × β)} {a : Attr}
    (h : a ∈ H.map Prod.fst) : (H.lookup a).isSome = true := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  exact List.lookup_isSome_iff.mpr ⟨p, hp, by simp⟩

theorem mem_hoistedNamesFrom {P : PolicySet} {k : Nat} {a : Attr} :
    a ∈ P.hoistedNamesFrom k ↔ ∃ i, k ≤ i ∧ i < k + P.leafList.length ∧ a = leafAttr i := by
  simp only [PolicySet.hoistedNamesFrom, List.mem_map, List.mem_range'_1]
  exact ⟨fun ⟨i, hi, h⟩ => ⟨i, hi.1, hi.2, h.symm⟩, fun ⟨i, h₁, h₂, h⟩ => ⟨i, ⟨h₁, h₂⟩, h.symm⟩⟩

theorem leafAttr_not_mem_hoistedNamesFrom {P : PolicySet} {k i : Nat} (hi : i < k) :
    leafAttr i ∉ P.hoistedNamesFrom k := by
  rw [mem_hoistedNamesFrom]
  rintro ⟨j, hj, -, h⟩
  have := Frontend.Cedarify.leafAttr_inj h
  omega


/-- A lowered rule is a rule lowered from an offset within the list's leaves. -/
theorem mem_policies_lowerFrom : (ps : Policies) → (k : Nat) → ∀ lp ∈ (Policies.lowerFrom k ps).1,
    ∃ p ∈ ps, ∃ k', k ≤ k' ∧
      k' + p.toExpr.leaves.length ≤ k + (ps.flatMap (·.toExpr.leaves)).length ∧
      lp = (p.lowerFrom k').1
  | [], _, lp, h => by cases h
  | p :: ps, k, lp, h => by
    simp only [Policies.lowerFrom, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨p, List.mem_cons_self .., k, Nat.le_refl _, by simp [List.flatMap_cons], rfl⟩
    · obtain ⟨q, hq, k', h₁, h₂, rfl⟩ := mem_policies_lowerFrom ps _ lp h
      rw [policy_lowerFrom_snd] at h₁ h₂
      refine ⟨q, List.mem_cons_of_mem _ hq, k', by omega, ?_, rfl⟩
      simp only [List.flatMap_cons, List.length_append]
      omega


/-! ## Cedar validation after a second augmentation -/

open Frontend.Augment Frontend.Augment.Typecheck in
private theorem sameSkeleton_augment (S : Schema) (H₁ H₂ : List (Attr × QualifiedType)) :
    SameSkeleton (Schema.augment S H₁) (Schema.augment S H₂) where
  ets := rfl
  acts := by
    simp only [Schema.augment, Map.mapOnValues, Map.toList]
    exact forall₂_map_same fun _ _ => ⟨rfl, rfl⟩

private theorem except_toBool_unit {ε : Type} {r : Except ε Unit} :
    r.toBool = true ↔ r = .ok () := by
  cases r <;> simp [Except.toBool]

open Frontend.Augment Frontend.Augment.Typecheck in
/-- **A second augmentation keeps Cedar's verdict** on rules that read the context only through
attributes it does not add, when the schema declares each action once (as a valid set's does,
`actions_nodup_of_valid`). -/
theorem validate_augment_append {S : Schema} {H₁ H₂ : List (Attr × QualifiedType)}
    {ps : Cedar.Spec.Policies} (hnd : (S.acts.toList.map Prod.fst).Nodup)
    (hps : ∀ p ∈ ps, CtxAvoids (H₂.map Prod.fst) p.toExpr)
    (h : Cedar.Validation.validate ps (Schema.augment S H₁) = .ok ()) :
    Cedar.Validation.validate ps (Schema.augment S (H₁ ++ H₂)) = .ok () := by
  have hone : ∀ p ∈ ps,
      (Cedar.Validation.typecheckPolicyWithEnvironments Cedar.Validation.typecheckPolicy p
        (Schema.augment S H₁)).toBool =
      (Cedar.Validation.typecheckPolicyWithEnvironments Cedar.Validation.typecheckPolicy p
        (Schema.augment S (H₁ ++ H₂))).toBool := by
    intro p hp
    refine typecheckPolicyWithEnvironments_agree (sameSkeleton_augment S _ _) p ?_
    intro q₁ hq₁ q₂ hq₂ hrel
    simp only [Schema.augment, Map.mapOnValues, Map.toList, List.mem_map] at hq₁ hq₂
    obtain ⟨⟨uid, e⟩, he, rfl⟩ := hq₁
    obtain ⟨⟨uid', e'⟩, he', rfl⟩ := hq₂
    obtain ⟨huid, _⟩ := hrel
    simp only at huid
    subst huid
    have hee : e = e' := value_unique hnd he he'
    subst hee
    refine .inl ⟨ctxReads p.toExpr, readsOnly_of_ctxAvoids _ (hps p hp) fun _ h => h,
      fun a ha => ?_⟩
    show (Map.make (e.context.toList ++ H₁)).find? a =
      (Map.make (e.context.toList ++ (H₁ ++ H₂))).find? a
    rw [find?_augmentedContext, find?_augmentedContext, List.lookup_append,
      lookup_eq_none_of_not_mem (ctxReads_not_mem _ (hps p hp) a ha), Option.or_none]
  unfold Cedar.Validation.validate at h ⊢
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.forM] at h ⊢
    cases h₁ : Cedar.Validation.typecheckPolicyWithEnvironments Cedar.Validation.typecheckPolicy p
        (Schema.augment S H₁) with
    | error => rw [h₁] at h; cases h
    | ok u =>
      rw [h₁] at h
      have h₂ := hone p (List.mem_cons_self ..)
      rw [h₁, show (Except.ok u : Except _ Unit).toBool = true from rfl, eq_comm,
        except_toBool_unit] at h₂
      rw [h₂]
      exact ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) h
        (fun q hq => hone q (List.mem_cons_of_mem _ hq))

/-! ## Environments of the augmented schema -/

private theorem augment_descendentOf (S : Schema) (H : List (Attr × QualifiedType))
    (u₁ u₂ : EntityUID) :
    (Schema.augment S H).acts.descendentOf u₁ u₂ = S.acts.descendentOf u₁ u₂ := by
  simp only [Schema.augment, Cedar.Validation.ActionSchema.descendentOf, Map.find?_mapOnValues]
  cases S.acts.find? u₁ <;> rfl

private theorem augment_maybeDescendentOf (S : Schema) (H : List (Attr × QualifiedType))
    (e₁ e₂ : Cedar.Spec.EntityType) :
    (Schema.augment S H).acts.maybeDescendentOf e₁ e₂ = S.acts.maybeDescendentOf e₁ e₂ := by
  simp only [Schema.augment, Cedar.Validation.ActionSchema.maybeDescendentOf, Map.mapOnValues,
    Map.toList, List.any_map, Function.comp_def]

private theorem augment_ets (S : Schema) (H : List (Attr × QualifiedType)) :
    (Schema.augment S H).ets = S.ets := rfl

private theorem scopeAdmitsType_augment (S : Schema) (H : List (Attr × QualifiedType)) :
    scopeAdmitsType (Schema.augment S H) = scopeAdmitsType S := by
  funext sc ety
  cases sc <;> simp only [scopeAdmitsType, Schema.memberOfType, augment_maybeDescendentOf,
    augment_ets]

private theorem actionScopeAdmits_augment (S : Schema) (H : List (Attr × QualifiedType)) :
    actionScopeAdmits (Schema.augment S H) = actionScopeAdmits S := by
  funext act sc
  rcases sc with ⟨sc⟩ | ls
  · cases sc <;> simp [actionScopeAdmits, augment_descendentOf]
  · simp [actionScopeAdmits, augment_descendentOf]

theorem admits_augmentEnv (S : Schema) (H : List (Attr × QualifiedType)) (env : TypeEnv)
    (p : Policy) : p.admits (Schema.augment S H) (augmentEnv S H env) = p.admits S env := by
  simp only [Policy.admits, scopeAdmitsType_augment, actionScopeAdmits_augment, augmentEnv]

/-- The environment of an action-selective augmentation that corresponds to an environment of the
schema: the same request type, with the attributes `Hk` gives its action added to its context. -/
def augmentEnvWith (S : Schema) (Hk : EntityUID → List (Attr × QualifiedType)) (env : TypeEnv) :
    TypeEnv :=
  { ets := env.ets, acts := (Schema.augmentWith S Hk).acts,
    reqty := { env.reqty with
      context := Map.make (env.reqty.context.toList ++ Hk env.reqty.action) } }

theorem augmentEnvWith_mem {S : Schema} {Hk : EntityUID → List (Attr × QualifiedType)}
    {env : TypeEnv} (h : env ∈ S.environments) :
    augmentEnvWith S Hk env ∈ (Schema.augmentWith S Hk).environments := by
  obtain ⟨a, entry, p, r, hmem, hp, hr, rfl⟩ := mem_environments.mp h
  refine mem_environments.mpr ⟨a, augmentEntry (Hk a) entry, p, r, ?_, hp, hr, rfl⟩
  rw [augmentWith_acts_toList]
  exact List.mem_map.mpr ⟨(a, entry), hmem, rfl⟩

theorem admits_augmentEnvWith (S : Schema) (Hk : EntityUID → List (Attr × QualifiedType))
    (env : TypeEnv) (p : Policy) :
    p.admits (Schema.augmentWith S Hk) (augmentEnvWith S Hk env) = p.admits S env := by
  simp only [Policy.admits, scopeAdmitsType_augmentWith, actionScopeAdmits_augmentWith,
    augmentEnvWith]

/-- A rule's environments in the joint set, augmented, are its environments in the second
lowering. -/
theorem augmentEnv_mem_envsOf {env : TypeEnv} {p : Policy} {H : List (Attr × QualifiedType)}
    (hH : A.hoistedTypes? = some H) (h : env ∈ (A.join qs).envsOf p) :
    augmentEnvWith A.actionSchema (A.targetedAt H) env ∈ (A.next qs).envsOf p := by
  simp only [PolicySet.envsOf, List.mem_filter] at h ⊢
  have hS : (A.next qs).actionSchema = Schema.augmentWith A.actionSchema (A.targetedAt H) :=
    augmentedSchema_eq_augmentWith hH
  rw [hS]
  refine ⟨augmentEnvWith_mem h.1, ?_⟩
  rw [admits_augmentEnvWith]
  exact h.2

/-- The typing context of a leaf of the second lowering, in an augmented environment, agrees
with the joint set's but at the first lowering's names. -/
theorem ctxAgree_augmentEnv {env : TypeEnv} {F : List Guard} {H : List (Attr × QualifiedType)}
    (hH : A.hoistedTypes? = some H) (henv : env ∈ A.actionSchema.environments) :
    CtxAgree A.hoistedNames
      ((A.next qs).typingCtx (augmentEnvWith A.actionSchema (A.targetedAt H) env) F)
      ((A.join qs).typingCtx env F) where
  ets := rfl
  principal := rfl
  resource := rfl
  contains u := by
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := mem_environments.mp henv
    exact augmentWith_contains _ _ u
  events := rfl
  maxWindow := rfl
  facts := rfl
  context a ha := by
    show (Map.make (env.reqty.context.toList ++ A.targetedAt H env.reqty.action)).find? a =
      env.reqty.context.find? a
    rw [find?_augmentEntry, attrType?_none fun x hx hxa => ha ?_, Option.or_none]
    rw [← hoistedNamesFrom_zero, ← keys_hoistedTypesFrom (k := 0) hH, ← hxa]
    exact List.mem_map.mpr ⟨x, targetedAt_sub hx, rfl⟩


/-! ## Provider arguments -/

section

variable {N : List Attr} {C₁ C₂ : TypingCtx}

theorem typeIn?_agree (h : CtxAgree N C₁ C₂) {a : Provider.Arg} (ha : a.AvoidsContext N) :
    a.typeIn? C₁ = a.typeIn? C₂ := by
  cases a with
  | context p =>
    cases p with
    | nil => rfl
    | cons x p =>
      simp only [Provider.Arg.typeIn?, declaredPathType?]
      exact pathType?_congr p (h.context x ha)
  | scope r p =>
    cases p with
    | nil => simp only [Provider.Arg.typeIn?, h.scopeType]
    | cons x p => simp only [Provider.Arg.typeIn?, h.ets, h.scopeType]
  | _ => rfl

mutual

theorem hasTypeIn_agree (h : CtxAgree N C₁ C₂) :
    (a : Provider.Arg) → a.AvoidsContext N → ∀ ty, a.hasTypeIn C₁ ty = a.hasTypeIn C₂ ty
  | .set items, ha, ty => by
    cases ty with
    | set ty =>
      simp only [Provider.Arg.hasTypeIn]
      exact allHaveTypeIn_agree h items ha ty
    | _ => simp only [Provider.Arg.hasTypeIn]
  | .context p, ha, ty => by simp only [Provider.Arg.hasTypeIn, typeIn?_agree h ha]
  | .scope r p, ha, ty => by simp only [Provider.Arg.hasTypeIn, typeIn?_agree h ha]
  | .string _, _, _ | .long _, _, _ | .decimal _, _, _ | .bool _, _, _ => rfl

theorem allHaveTypeIn_agree (h : CtxAgree N C₁ C₂) :
    (xs : List Provider.Arg) → Provider.Arg.allAvoidContext N xs →
      ∀ ty, Provider.Arg.allHaveTypeIn C₁ xs ty = Provider.Arg.allHaveTypeIn C₂ xs ty
  | [], _, _ => rfl
  | x :: xs, ha, ty => by
    simp only [Provider.Arg.allAvoidContext] at ha
    simp only [Provider.Arg.allHaveTypeIn, hasTypeIn_agree h x ha.1 ty,
      allHaveTypeIn_agree h xs ha.2 ty]

end

theorem argsTypedIn_agree (h : CtxAgree N C₁ C₂) {args : List Provider.Arg}
    {tys : List Cedar.Validation.CedarType} (ha : ∀ a ∈ args, a.AvoidsContext N)
    (ht : Provider.ArgsTypedIn C₁ args tys) : Provider.ArgsTypedIn C₂ args tys :=
  ⟨ht.1, fun p hp => by
    rw [← hasTypeIn_agree h p.1 (ha p.1 (List.of_mem_zip hp).1)]
    exact ht.2 p hp⟩

/-- **A provider invocation's typing does not see context attributes it does not read.** -/
theorem _root_.Dogwood.Spec.Provider.Call.TypedIn.of_agree (h : CtxAgree N C₁ C₂)
    {D : Provider.Declarations}
    {c : Provider.Call} (ha : c.AvoidsContext N) (ht : c.TypedIn C₁ D) : c.TypedIn C₂ D := by
  obtain ⟨sig, hsig, hargs, hms⟩ := ht
  refine ⟨sig, hsig, argsTypedIn_agree h ha.1 hargs, fun m hm => ?_⟩
  obtain ⟨ms, hms', hname, hmargs⟩ := hms m hm
  exact ⟨ms, hms', hname, argsTypedIn_agree h (ha.2 m hm) hmargs⟩

end


/-! ## The actions of a valid set's schema -/

private theorem nodup_of_sortedBy {α β : Type} [LT α] [Cedar.Data.StrictLT α] :
    ∀ {l : List (α × β)}, l.SortedBy Prod.fst → (l.map Prod.fst).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_of_sortedBy (List.tail_sortedBy h)⟩
    obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hm
    have := List.sortedBy_implies_head_lt_tail h y hy
    rw [hxy] at this
    exact Cedar.Data.StrictLT.irreflexive _ this

theorem policies_lowerFrom_length : (ps : Policies) → (k : Nat) →
    (Policies.lowerFrom k ps).1.length = ps.length
  | [], _ => rfl
  | p :: ps, k => by simp [Policies.lowerFrom, policies_lowerFrom_length ps]

/-- **A valid set with a rule has an action schema that declares each action once**: Cedar's
validator accepts its rules only in some request environment, and a well-formed environment's
action schema is a well-formed map. -/
theorem actions_nodup_of_valid {A : PolicySet} (hA : A.Valid) (hne : A.policies ≠ []) :
    (A.actionSchema.acts.toList.map Prod.fst).Nodup := by
  have hlow : A.lowered ≠ [] := by
    intro hl
    have := congrArg List.length hl
    simp only [PolicySet.lowered, policies_lowerFrom_length, List.length_nil] at this
    exact hne (List.eq_nil_of_length_eq_zero this)
  obtain ⟨H, hH⟩ := Option.isSome_iff_exists.mp hA.leafTypes
  have hwf := hA.wellFormed
  have hval := hA.cedar
  rw [augmentedSchema_eq_augmentWith hH] at hwf hval
  exact acts_nodup_of_wellFormed hwf (environments_ne_nil_of_validate hlow hval)

/-! ## Composition -/

theorem validate_append {ps₁ ps₂ : Cedar.Spec.Policies} {S : Schema} :
    Cedar.Validation.validate (ps₁ ++ ps₂) S = .ok () ↔
      Cedar.Validation.validate ps₁ S = .ok () ∧ Cedar.Validation.validate ps₂ S = .ok () := by
  unfold Cedar.Validation.validate
  induction ps₁ with
  | nil => simp [List.forM, pure, Except.pure]
  | cons p ps ih =>
    simp only [List.cons_append, List.forM]
    cases Cedar.Validation.typecheckPolicyWithEnvironments Cedar.Validation.typecheckPolicy p S with
    | error e => simp [bind, Except.bind]
    | ok u => simpa [bind, Except.bind] using ih

theorem hoistedNamesFrom_eq_nil {P : PolicySet} {k : Nat} (h : P.leafList = []) :
    P.hoistedNamesFrom k = [] := by
  simp [PolicySet.hoistedNamesFrom, h]

theorem hoistedNames_eq_nil {P : PolicySet} (h : P.leafList = []) : P.hoistedNames = [] := by
  simp [PolicySet.hoistedNames, h]

private theorem readsContext_nil {x : Expr} {N : List Attr} (h : x.ReadsContext N) :
    x.ReadsContext [] :=
  readsContext_mono (fun _ h => by cases h) x h

/-- **Two lowerings in sequence make one valid policy set.** Lower `A`, valid against its action
schema; then lower the rules `qs` with `A`'s service schema against `A`'s augmented schema, with
their leaves numbered after `A`'s (`PolicySet.next`, `PolicySet.ValidFrom`). If `A`'s rules read
none of the second lowering's attributes, and the second set's rules (their Cedar part, temporal
leaves, and provider arguments) and the event schema's pins read none of `A`'s, then `A` and `qs`
together are valid against the action schema (`PolicySet.join`), lowered and augmented as the
two lowerings were (`lowered_join`, `augmentedSchema_join`). The joint set then decides as
`Dogwood.Thm.cedar_sound` and `Dogwood.Thm.decision_sound` say of a valid set.

The whole-context part of `hAreads` is needed (`not_valid_join_of_whole_context_read`); the
necessity of the other read hypotheses is not shown. Together the Cedar-part ones are the joint
set's context-read check (`valid_join_of_contextReadsOk`). The crate enforces part of them: it
reserves every name of the shape of a hoisted attribute, another lowering's included, in
a rule's Cedar part, its temporal leaves, its provider arguments, and the pins. It does not
enforce the rest: a policy set without leaves may read `context` whole, and its own check passes,
though a later lowering that adds a leaf, on any action, changes that context, since a
decision's request context holds every leaf's value. -/
theorem valid_join {A : PolicySet} {qs : Policies} (hA : A.Valid)
    (hB : (A.next qs).ValidFrom A.leafList.length)
    (hAreads : (A.next qs).leafList ≠ [] → ∀ p ∈ A.policies,
      p.toExpr.ReadsContext ((A.next qs).hoistedNamesFrom A.leafList.length))
    (hBreads : A.leafList ≠ [] → ∀ p ∈ qs, p.toExpr.ReadsContext A.hoistedNames)
    (hBleaves : ∀ p ∈ qs,
      (∀ φ F, (.inl φ, F) ∈ p.toExpr.leafFacts [] → φ.AvoidsContext A.hoistedNames) ∧
      ∀ c F, (.inr c, F) ∈ p.toExpr.leafFacts [] → c.AvoidsContext A.hoistedNames)
    (hpins : PinsAvoid A.hoistedNames A.schema) :
    (A.join qs).Valid := by
  obtain ⟨HA, hHA⟩ := Option.isSome_iff_exists.mp hA.leafTypes
  obtain ⟨HB, hHB⟩ := Option.isSome_iff_exists.mp hB.leafTypes
  have hJt : (A.join qs).hoistedTypes? = some (HA ++ HB) := by
    rw [hoistedTypes_join, hHA, hHB]; rfl
  have haug := augmentedSchema_join (qs := qs) hHA hHB
  have hAaug : A.augmentedSchema = Schema.augmentWith A.actionSchema (A.targetedAt HA) :=
    augmentedSchema_eq_augmentWith hHA
  have hJaug : (A.join qs).augmentedSchema = Schema.augmentWith A.actionSchema
      (fun u => A.targetedAt HA u ++ (A.next qs).targetedAt HB u) := by
    rw [augmentedSchema_eq_augmentWith hJt]
    show Schema.augmentWith A.actionSchema _ = _
    congr 1
    funext uid
    exact targetedAt_join hHA hHB uid
  have hkeysB : HB.map Prod.fst = (A.next qs).hoistedNamesFrom A.leafList.length :=
    keys_hoistedTypesFrom hHB
  have hmemJ : ∀ {p}, p ∈ (A.join qs).policies ↔ p ∈ A.policies ∨ p ∈ qs := by
    intro p; simp [PolicySet.join]
  have hBacts : ∀ act ∈ A.actionSchema.acts.toList,
      (act.1, augmentEntry (A.targetedAt HA act.1) act.2) ∈
        (A.next qs).actionSchema.acts.toList := by
    intro act hact
    show (act.1, augmentEntry (A.targetedAt HA act.1) act.2) ∈ A.augmentedSchema.acts.toList
    rw [hAaug, augmentWith_acts_toList]
    exact List.mem_map.mpr ⟨act, hact, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hJt]; rfl
  · exact Frontend.Cedarify.nodup_map_of_inj (fun _ _ h => Frontend.Cedarify.leafAttr_inj h)
      List.nodup_range
  · intro act hact a ha
    rw [hoistedNames_join, List.mem_append] at ha
    rcases ha with ha | ha
    · exact hA.namesFresh act hact a ha
    · have := hB.namesFresh _ (hBacts act hact) a ha
      simp only [augmentEntry, find?_augmentEntry, Option.or_eq_none_iff] at this
      exact this.1
  · intro hne p hp
    rw [hoistedNames_join]
    rw [leafList_join] at hne
    rcases hmemJ.mp hp with hp | hp
    · have RA : p.toExpr.ReadsContext A.hoistedNames := by
        by_cases hAl : A.leafList = []
        · rw [hoistedNames_eq_nil hAl]
          have hBl : (A.next qs).leafList ≠ [] := by simpa [hAl] using hne
          exact readsContext_nil (hAreads hBl p hp)
        · exact hA.readsContext hAl p hp
      have RB : p.toExpr.ReadsContext ((A.next qs).hoistedNamesFrom A.leafList.length) := by
        by_cases hBl : (A.next qs).leafList = []
        · rw [hoistedNamesFrom_eq_nil hBl]; exact readsContext_nil RA
        · exact hAreads hBl p hp
      exact readsContext_append _ RA RB
    · have RB : p.toExpr.ReadsContext ((A.next qs).hoistedNamesFrom A.leafList.length) := by
        by_cases hBl : (A.next qs).leafList = []
        · rw [hoistedNamesFrom_eq_nil hBl]
          have hAl : A.leafList ≠ [] := by simpa [hBl] using hne
          exact readsContext_nil (hBreads hAl p hp)
        · exact hB.readsContext hBl p hp
      have RA : p.toExpr.ReadsContext A.hoistedNames := by
        by_cases hAl : A.leafList = []
        · rw [hoistedNames_eq_nil hAl]; exact readsContext_nil RB
        · exact hBreads hAl p hp
      exact readsContext_append _ RA RB
  · rw [haug]; exact hB.wellFormed
  · rw [haug]; exact hB.standardAncestors
  · intro hne
    by_cases hAp : A.policies = []
    · have : qs ≠ [] := by simpa [PolicySet.join, hAp] using hne
      exact hB.complete this
    · exact hA.complete hAp
  · rw [lowered_join, validate_append]
    refine ⟨?_, haug ▸ hB.cedar⟩
    rw [hJaug]
    have hAc := hA.cedar
    rw [hAaug] at hAc
    by_cases hBl : (A.next qs).leafList = []
    · have : HB = [] := by
        rw [hoistedNamesFrom_eq_nil hBl] at hkeysB
        exact List.map_eq_nil_iff.mp hkeysB
      have hnil : ∀ u, (A.next qs).targetedAt HB u = [] := by
        intro u
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro x hx
        have := targetedAt_sub hx
        rw [‹HB = []›] at this
        cases this
      simp only [hnil, List.append_nil]
      exact hAc
    · by_cases hAp : A.policies = []
      · show Cedar.Validation.validate (Policies.lowerFrom 0 A.policies).1 _ = .ok ()
        rw [hAp]
        rfl
      refine (validate_augmentWith_agree _ _ _ _ (actions_nodup_of_valid hA hAp)
        (fun lp hlp uid e _ _ => ?_)).mp hAc
      obtain ⟨p, hp, k', _, hk', rfl⟩ := mem_policies_lowerFrom A.policies 0 lp hlp
      have havoid : CtxAvoids ((A.next qs).hoistedNamesFrom A.leafList.length)
          (p.lowerFrom k').1.toExpr := by
        rw [policy_lowerFrom]
        refine ctxAvoids_lowerFrom _ k' (hAreads hBl p hp) fun i _ hi => ?_
        refine leafAttr_not_mem_hoistedNamesFrom ?_
        simp only [PolicySet.leafList] at hk' ⊢
        omega
      refine ⟨ctxReads (p.lowerFrom k').1.toExpr, readsOnly_of_ctxAvoids _ havoid fun a ha => ha,
        fun a ha => .inr ?_⟩
      have hnot := ctxReads_not_mem _ havoid a ha
      have hB0 : attrType? ((A.next qs).targetedAt HB uid) a = none := by
        refine attrType?_none fun x hx hxa => hnot ?_
        rw [← hkeysB, ← hxa]
        exact List.mem_map.mpr ⟨x, targetedAt_sub hx, rfl⟩
      have happ : attrType? (A.targetedAt HA uid ++ (A.next qs).targetedAt HB uid) a =
          (attrType? (A.targetedAt HA uid) a).or (attrType? ((A.next qs).targetedAt HB uid) a) := by
        unfold attrType?
        rw [List.find?_append]
        cases (A.targetedAt HA uid).find? (·.1 == a) <;> rfl
      show _ = attrType? (A.targetedAt HA uid ++ (A.next qs).targetedAt HB uid) a
      rw [happ, hB0, Option.or_none]
  · intro p hp φ F hφ
    rcases hmemJ.mp hp with hp | hp
    · have h := hA.temporal p hp φ F hφ
      exact ⟨h.wellTyped, h.safe, h.monitorsTime⟩
    · have h := hB.temporal p hp φ F hφ
      refine ⟨fun env henv => ?_, h.safe, h.monitorsTime⟩
      have henv' := augmentEnv_mem_envsOf (qs := qs) hHA henv
      exact Formula.WellTyped.of_agree
        (ctxAgree_augmentEnv hHA (List.mem_filter.mp henv).1) hpins
        ((hBleaves p hp).1 φ F hφ) (h.wellTyped _ henv')
  · intro p hp c F hc
    rcases hmemJ.mp hp with hp | hp
    · exact hA.providers p hp c F hc
    · have h := hB.providers p hp c F hc
      refine ⟨h.1, fun env henv => ?_⟩
      have henv' := augmentEnv_mem_envsOf (qs := qs) hHA henv
      exact Provider.Call.TypedIn.of_agree
        (ctxAgree_augmentEnv hHA (List.mem_filter.mp henv).1)
        ((hBleaves p hp).2 c F hc) (h.2 _ henv')
  · intro H hH φ hφ
    have hJ : (A.join qs).temporalLeaves = A.temporalLeaves ++ (A.next qs).temporalLeaves := by
      simp [PolicySet.temporalLeaves, PolicySet.join, PolicySet.next, List.flatMap_append]
    rw [hJ, List.mem_append] at hφ
    rcases hφ with hφ | hφ
    · exact hA.horizon H hH φ hφ
    · exact hB.horizon H hH φ hφ


/-- **A second lowering whose leaves take names the first gave is invalid**: lowering rules with
a leaf against `A`'s augmented schema, numbering their leaves from an offset `k` below the number
of `A`'s leaves, never validates. The first of the new names is the attribute of `A`'s `k`-th
leaf, which `A`'s augmented schema adds to the context of an action its rule's action scope
admits (there is one, since Cedar's validator accepts `A`'s rules), and no action's context may
declare a new leaf's name. Lowering twice with the same names is the case `k = 0`. The crate
refuses a schema in which any action's context declares a temporal leaf's name, whichever
actions the leaf targets (`reject_declared_leaf_names`). -/
theorem not_validFrom_next_of_lt {A : PolicySet} {qs : Policies} {k : Nat}
    (hA : A.Valid) (hk : k < A.leafList.length)
    (hBl : (A.next qs).leafList ≠ []) : ¬ (A.next qs).ValidFrom k := by
  intro h
  obtain ⟨HA, hHA⟩ := Option.isSome_iff_exists.mp hA.leafTypes
  have hval := hA.cedar
  rw [augmentedSchema_eq_augmentWith hHA] at hval
  have hlen : HA.length = A.leafList.length := by
    rw [length_of_hoistedTypesFrom (k := 0) hHA, leafScopes_length]
  have hki : k < HA.length := by omega
  obtain ⟨a, e, he, hin⟩ := leaf_targeted (k := 0) hHA (covers_targetedAt A HA) hval hki
  have hkeys := keys_hoistedTypesFrom (k := 0) hHA
  have hkey : HA[k].1 = leafAttr k := by
    have := key_of_hoistedNamesFrom hkeys hki
    rwa [Nat.zero_add] at this
  have hmem : (a, augmentEntry (A.targetedAt HA a) e) ∈ (A.next qs).actionSchema.acts.toList := by
    show (a, augmentEntry (A.targetedAt HA a) e) ∈ A.augmentedSchema.acts.toList
    rw [augmentedSchema_eq_augmentWith hHA, augmentWith_acts_toList]
    exact List.mem_map.mpr ⟨(a, e), he, rfl⟩
  have hname : leafAttr k ∈ (A.next qs).hoistedNamesFrom k :=
    mem_hoistedNamesFrom.mpr ⟨k, Nat.le_refl _, by
      have := List.length_pos_iff.mpr hBl
      omega, rfl⟩
  have hfresh := h.namesFresh _ hmem _ hname
  have hnd : (HA.map (·.1)).Nodup := by
    rw [hkeys, hoistedNamesFrom_zero]; exact hA.namesNodup
  have hsome := attrType?_of_mem hnd (fun x hx => targetedAt_sub hx) hin
  simp only [augmentEntry, find?_augmentEntry, ← hkey, hsome] at hfresh
  cases h' : e.context.find? HA[k].1 <;> simp [h'] at hfresh


/-! ## Composition under the joint context-read check -/

/-- **The context-read check of a policy set**, as a Boolean: when the set has a leaf, every rule
reads the request context only through attributes that are not hoisted (`Expr.ReadsContext`).
It is `PolicySet.Valid.readsContext`, decided; it needs no schema. -/
def _root_.Dogwood.Spec.PolicySet.contextReadsOk (P : PolicySet) : Bool :=
  P.leafList.isEmpty || P.policies.all (·.toExpr.readsContextB P.hoistedNames)

theorem contextReadsOk_iff {P : PolicySet} :
    P.contextReadsOk = true ↔
      (P.leafList ≠ [] → ∀ p ∈ P.policies, p.toExpr.ReadsContext P.hoistedNames) := by
  simp only [PolicySet.contextReadsOk, Bool.or_eq_true, List.isEmpty_iff, List.all_eq_true,
    Expr.readsContextB_iff]
  constructor
  · rintro (h | h) hne
    · exact absurd h hne
    · exact h
  · intro h
    by_cases hne : P.leafList = []
    · exact .inl hne
    · exact .inr (h hne)

/-- The joint set's context-read check gives both read hypotheses of `valid_join`. -/
theorem reads_of_contextReadsOk_join {A : PolicySet} {qs : Policies}
    (h : (A.join qs).contextReadsOk = true) :
    ((A.next qs).leafList ≠ [] → ∀ p ∈ A.policies,
        p.toExpr.ReadsContext ((A.next qs).hoistedNamesFrom A.leafList.length)) ∧
      (A.leafList ≠ [] → ∀ p ∈ qs, p.toExpr.ReadsContext A.hoistedNames) := by
  rw [contextReadsOk_iff, hoistedNames_join, leafList_join] at h
  refine ⟨fun hB p hp => ?_, fun hA p hp => ?_⟩
  · exact readsContext_mono (fun a ha => List.mem_append_right _ ha) _
      (h (by simp [hB]) p (List.mem_append_left _ hp))
  · exact readsContext_mono (fun a ha => List.mem_append_left _ ha) _
      (h (by simp [hA]) p (List.mem_append_right _ hp))

/-- **Two lowerings in sequence, checked together, make one valid policy set.** Each lowering is
valid on its own (`A` against its action schema, the second against `A`'s augmented schema), and
the two sets together pass the context-read check (`PolicySet.contextReadsOk`), which reads no
schema; then `A` and `qs` together are valid. The check is what feed-forward lowering misses on
its own: a policy set without leaves may read `context` whole, and its own check passes, but a
later lowering that adds a leaf, on any action, changes the context it reads, since a
decision's request context holds every leaf's value. -/
theorem valid_join_of_contextReadsOk {A : PolicySet} {qs : Policies} (hA : A.Valid)
    (hB : (A.next qs).ValidFrom A.leafList.length)
    (hreads : (A.join qs).contextReadsOk = true)
    (hBleaves : ∀ p ∈ qs,
      (∀ φ F, (.inl φ, F) ∈ p.toExpr.leafFacts [] → φ.AvoidsContext A.hoistedNames) ∧
      ∀ c F, (.inr c, F) ∈ p.toExpr.leafFacts [] → c.AvoidsContext A.hoistedNames)
    (hpins : PinsAvoid A.hoistedNames A.schema) :
    (A.join qs).Valid :=
  have h := reads_of_contextReadsOk_join hreads
  valid_join hA hB h.1 h.2 hBleaves hpins

/-- **Sequential lowering is valid exactly when the joint context-read check passes**, when each
lowering is valid on its own and the second set's leaves and the pins read none of the first
set's attributes. -/
theorem valid_join_iff_contextReadsOk {A : PolicySet} {qs : Policies} (hA : A.Valid)
    (hB : (A.next qs).ValidFrom A.leafList.length)
    (hBleaves : ∀ p ∈ qs,
      (∀ φ F, (.inl φ, F) ∈ p.toExpr.leafFacts [] → φ.AvoidsContext A.hoistedNames) ∧
      ∀ c F, (.inr c, F) ∈ p.toExpr.leafFacts [] → c.AvoidsContext A.hoistedNames)
    (hpins : PinsAvoid A.hoistedNames A.schema) :
    (A.join qs).Valid ↔ (A.join qs).contextReadsOk = true :=
  ⟨fun hv => contextReadsOk_iff.mpr hv.readsContext,
    fun h => valid_join_of_contextReadsOk hA hB h hBleaves hpins⟩

/-- **A rule of the first set that reads `context` whole breaks composition**: if the second set
has a leaf, `A` and `qs` together are not valid, however each lowering fares on its own. -/
theorem not_valid_join_of_whole_context_read {A : PolicySet} {qs : Policies} {p : Policy}
    (hp : p ∈ A.policies) (hwhole : ¬ p.toExpr.ReadsContext [])
    (hBl : (A.next qs).leafList ≠ []) : ¬ (A.join qs).Valid := by
  intro hv
  have hne : (A.join qs).leafList ≠ [] := by
    rw [leafList_join]; simp [hBl]
  exact hwhole (readsContext_nil
    (hv.readsContext hne p (by simp [PolicySet.join, hp])))

end Dogwood.Thm
