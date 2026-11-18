import Dogwood.Thm.Frontend.Augment.Typecheck
import Dogwood.Thm.Frontend.Augment.Spec

/-!
# Action-selective and all-action augmentation give the same validation verdict

The crate adds a hoisted attribute only to the contexts of the actions its rule can apply to, and so
does the specification (`PolicySet.augmentedSchema`); `Schema.augment` adds every hoisted attribute
to every action, which the specification shows gives the same verdict
(`Dogwood.Thm.valid_iff_validAll`, `Dogwood.Thm.validate_augmentWith_agree`). On the compiled
schema, the crate's augmentation is `selectiveAugment A Hsel`, where `Hsel uid` are the
attributes of the fields targeting `uid` (`augment_compiles_to_selective`, at one action, for an
attribute-wise compilation of record types, when no declared attribute has a hoisted name).

Cedar's validator gives a rule the same verdict against both
(`validate_selective_agrees`), provided that at every action either the rule reads the context
only at attributes the action declares or that are hoisted there with the type the specification
gives them, or the rule's action scope excludes the action. A rule that reads only declared
attributes and its own hoisted attributes meets this: its own leaves target exactly the actions
its scope admits, and on the others its scope typechecks as `false`, or fails to typecheck
(`Dogwood.Thm.actionScope_ff_or_error`). The specification's own selective augmentation adds a
leaf's attribute at the actions its rule's action scope admits (`actionScopeAdmits`), which are the
crate's target actions (`scope_target_actions`) up to pure action groups, which have no request
environment.
-/

namespace Dogwood.Frontend.Augment

open Cedar.Spec Cedar.Validation Cedar.Data
open Typecheck

/-- The augmentation of a compiled schema that adds the attributes `Hsel uid` to the context of
the action `uid` only. -/
def selectiveAugment (A : Schema) (Hsel : EntityUID → List (Attr × QualifiedType)) : Schema where
  ets := A.ets
  acts := Map.mk (A.acts.toList.map fun (uid, e) =>
    (uid, { e with context := Map.make (e.context.toList ++ Hsel uid) }))

theorem sameSkeleton_selective (A : Schema) (Hsel : EntityUID → List (Attr × QualifiedType))
    (H : List (Attr × QualifiedType)) :
    SameSkeleton (selectiveAugment A Hsel) (Dogwood.Spec.Schema.augment A H) where
  ets := rfl
  acts := by
    simp only [selectiveAugment, Dogwood.Spec.Schema.augment, Map.mapOnValues, Map.toList]
    exact forall₂_map_same fun q _ => ⟨rfl, rfl⟩

theorem value_unique {L : List (EntityUID × ActionSchemaEntry)} (hnd : (L.map Prod.fst).Nodup) :
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

/-- The temporal fields that target the action `id` of the namespace `nsName`. -/
def targetingFields (CF : List ContextField) (nsName id : String) : List ContextField :=
  CF.filter fun f => f.targetActions.contains (nsName, id)

theorem hoistedAt_eq_any (CF : List ContextField) (nsName id key : String) :
    hoistedAt CF nsName id key = (targetingFields CF nsName id).any (·.fieldName == key) := by
  simp only [hoistedAt, targetingFields, List.any_filter]
  congr 1; funext f; rw [Bool.and_comm]

/-- **The crate's augmentation compiles to the selective augmentation.** Under an attribute-wise
compilation `cmp` of record types (with `Bool` compiled to `Bool`), when no declared attribute
has the name of a temporal field, the crate's compiled augmented context of an action is, at
every attribute (`providers` aside on an action a provider field targets), the declared context
extended with the attributes of the temporal fields that target the action: the action's entry
of `selectiveAugment` with `Hsel` the `hoistedTypes` of `targetingFields`. -/
theorem augment_compiles_to_selective {F F' : CedarSchema.Fragment} {decls : Option ProviderDecls.Declarations}
    {enums : List String} {CF : List ContextField} {PF : List ProviderField} {nsName id : String}
    {k : Option String} {attrs attrs' : List (String × CedarSchema.AttrType)} {add add' : Bool}
    {cmp : CedarSchema.AttrType → Option QualifiedType} {L L' : List (Attr × QualifiedType)}
    (hb : cmp boolAttr = some (.required (.bool .anyBool)))
    (h : augmentSchema F decls enums CF PF = .ok F') (hk : nsKey nsName = .ok k)
    (hc : contextAt F k id = some (.record attrs add))
    (hc' : contextAt F' k id = some (.record attrs' add'))
    (hL : compileAttrs cmp attrs = some L) (hL' : compileAttrs cmp attrs' = some L')
    (hnc : ∀ f ∈ CF, attrs.lookup f.fieldName = none) (key : String)
    (hp : key ≠ "providers" ∨ (nsName, id) ∉ providerTargets PF) :
    (Map.make L').find? key =
      (Map.make ((Map.make L).toList ++ hoistedTypes (targetingFields CF nsName id))).find? key := by
  rw [find?_augmentedContext, find?_make, find?_make, compileAttrs_lookup hL' key,
    compileAttrs_lookup hL key, (augment_lookup h hk hc hc' key hp).2, lookup_hoistedTypes,
    hoistedAt_eq_any]
  by_cases hh : (targetingFields CF nsName id).any (·.fieldName == key) = true
  · obtain ⟨fl, hf, hname⟩ := List.any_eq_true.mp hh
    have hf' : fl ∈ CF := (List.mem_filter.mp hf).1
    have hnone : attrs.lookup key = none := by
      simp only [beq_iff_eq] at hname; rw [← hname]; exact hnc fl hf'
    simp [hh, hnone, hb]
  · simp only [Bool.not_eq_true] at hh
    simp [hh]

/-- The context of an augmented action at one attribute: the declared attribute, else the
hoisted one. -/
theorem find?_augmented (ctx : Map Attr QualifiedType) (H : List (Attr × QualifiedType)) (a : Attr) :
    (Map.make (ctx.toList ++ H)).find? a = (ctx.find? a).or (H.lookup a) :=
  find?_augmentedContext ctx H a

/-- **The crate's action-selective augmentation and the specification's all-action augmentation
give a rule the same Cedar validation verdict**, when at every action of the schema either the
rule reads the context only at attributes the action declares or that are hoisted there with the
type `H` gives them, or the rule's action scope excludes the action. -/
theorem validate_selective_agrees (A : Schema) (H : List (Attr × QualifiedType))
    (Hsel : EntityUID → List (Attr × QualifiedType)) (p : Policy)
    (hnd : (A.acts.toList.map Prod.fst).Nodup)
    (hp : ∀ uid e, (uid, e) ∈ A.acts.toList →
      (∃ R, ReadsOnly R p.toExpr ∧ ∀ a ∈ R, (e.context.find? a).isSome ∨ (Hsel uid).lookup a = H.lookup a) ∨
      (∀ env : TypeEnv, env.acts = (selectiveAugment A Hsel).acts → env.ets = A.ets →
        env.reqty.action = uid → ScopeExcludes p env)) :
    (typecheckPolicyWithEnvironments typecheckPolicy p (selectiveAugment A Hsel)).toBool =
      (typecheckPolicyWithEnvironments typecheckPolicy p (Dogwood.Spec.Schema.augment A H)).toBool := by
  refine typecheckPolicyWithEnvironments_agree (sameSkeleton_selective A Hsel H) p ?_
  intro q₁ hq₁ q₂ hq₂ hrel
  simp only [selectiveAugment, Map.toList, List.mem_map] at hq₁
  simp only [Dogwood.Spec.Schema.augment, Map.mapOnValues, Map.toList, List.mem_map] at hq₂
  obtain ⟨⟨uid, e⟩, he, rfl⟩ := hq₁
  obtain ⟨⟨uid', e'⟩, he', rfl⟩ := hq₂
  obtain ⟨huid, _⟩ := hrel
  simp only at huid
  subst huid
  have hee : e = e' := value_unique hnd he he'
  subst hee
  rcases hp uid e he with ⟨R, hR, hctx⟩ | hex
  · refine .inl ⟨R, hR, fun a ha => ?_⟩
    show (Map.make (e.context.toList ++ Hsel uid)).find? a = (Map.make (e.context.toList ++ H)).find? a
    rw [find?_augmented, find?_augmented]
    rcases hctx a ha with hdecl | hsame
    · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hdecl
      simp [hq]
    · rw [hsame]
  · exact .inr hex

/-- **The same verdict for a set of rules.** -/
theorem validate_selective_agrees_all (A : Schema) (H : List (Attr × QualifiedType))
    (Hsel : EntityUID → List (Attr × QualifiedType)) (ps : Policies)
    (hnd : (A.acts.toList.map Prod.fst).Nodup)
    (hp : ∀ p ∈ ps, ∀ uid e, (uid, e) ∈ A.acts.toList →
      (∃ R, ReadsOnly R p.toExpr ∧ ∀ a ∈ R, (e.context.find? a).isSome ∨ (Hsel uid).lookup a = H.lookup a) ∨
      (∀ env : TypeEnv, env.acts = (selectiveAugment A Hsel).acts → env.ets = A.ets →
        env.reqty.action = uid → ScopeExcludes p env)) :
    (validate ps (selectiveAugment A Hsel)).toBool =
      (validate ps (Dogwood.Spec.Schema.augment A H)).toBool := by
  unfold validate
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have h₁ := validate_selective_agrees A H Hsel p hnd (hp p (List.mem_cons_self ..))
    have ih := ih fun q hq => hp q (List.mem_cons_of_mem _ hq)
    simp only [List.forM]
    cases hs : typecheckPolicyWithEnvironments typecheckPolicy p (selectiveAugment A Hsel) <;>
      cases ha : typecheckPolicyWithEnvironments typecheckPolicy p (Dogwood.Spec.Schema.augment A H) <;>
      rw [hs, ha] at h₁ <;> simp_all [Except.toBool, bind, Except.bind]

/-- A rule scoped to one action, `action == a`, excludes every other action of the schema. -/
theorem scopeExcludes_eq {p : Policy} {a : EntityUID} {env : TypeEnv}
    (hscope : p.actionScope = .actionScope (.eq a)) (ha : env.acts.contains a = true)
    (hact : env.acts.contains env.reqty.action = true) (hne : env.reqty.action ≠ a) :
    ScopeExcludes p env := by
  intro c
  refine .inl ?_
  have hne' : (Prim.entityUID env.reqty.action == Prim.entityUID a) = false := by
    simp [hne]
  refine ⟨.binaryApp .eq (.lit (.entityUID env.reqty.action) (.entity env.reqty.action.ty))
      (.lit (.entityUID a) (.entity a.ty)) (.bool .ff), ∅, ?_, rfl⟩
  simp [hscope, substituteAction, ActionScope.toExpr, Scope.toExpr, Var.eqEntityUID, mapOnVars,
    typeOf, typeOfLit, ha, hact, typeOfBinaryApp, typeOfEq, hne', ok]

end Dogwood.Frontend.Augment
