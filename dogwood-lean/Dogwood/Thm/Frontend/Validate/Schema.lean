import Dogwood.Thm.Frontend.Validate.Interface
import Dogwood.Thm.CedarSoundness
import Dogwood.Thm.SchemaWellFormed
import Cedar.Thm.Validation.EnvironmentValidation

/-!
# The conformance projection's action schema

The conformance projection reads the action schema off the augmented schema the crate compiles
(`actionSchemaJson`, then `ActionSchemaJson.toSchema`): it exports each entity type with its
descendants and each action with its descendants, its `appliesTo` lists and its context without
the hoisted attributes, and reads the schema back, recomputing the ancestors from the
descendants. On a well-formed schema with an environment, that round trip is exact except for the
contexts (`specActionSchema_eq`): the entity types are the augmented schema's, and every action
is the augmented schema's with the hoisted attributes dropped from its context.

The specification's schema augmented at every action (`PolicySet.allAugmentedSchema`) adds the
leaves' attributes to every action's context, and validates as its action-selective augmented
schema does (`Dogwood.Thm.valid_iff_validAll`). It is well-formed when the crate's augmented schema is and the added types are
(`augment_wellFormed`), and no action of the projection declares an attribute named like the
specification's leaves when the crate's augmented schema declares none
(`specActionSchema_fresh`).
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.Validate
open Cedar.Validation
open Cedar.Spec (Attr EntityType EntityUID)
open Cedar.Data (Map Set)

/-! ## Well-formedness, read off a validated schema -/

/-- A schema with an environment that validates is well-formed in that environment. -/
theorem wellFormed_of_validate {S : Schema} (hwf : S.validateWellFormed = .ok ())
    (hne : S.environments ≠ []) :
    ∃ env : TypeEnv, env.ets = S.ets ∧ env.acts = S.acts ∧ env.WellFormed := by
  obtain ⟨env, henv⟩ := List.exists_mem_of_ne_nil _ hne
  have h := List.forM_ok_implies_all_ok _ _ hwf env henv
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := Dogwood.Thm.mem_environments.mp henv
  exact ⟨_, rfl, rfl, Cedar.Thm.env_validate_well_formed_is_sound h⟩


/-! ## The round trip: entity types -/

/-- The entity types the projection exports as the descendants of `n`. -/
def etDescendants (S : Schema) (n : EntityType) : List EntityType :=
  (S.ets.toList.filter fun x => x.2.ancestors.contains n).map (·.1)

theorem exportedEt_of_mem {S : Schema} {drop : List String} {d : Conformance.EntityDecl}
    (h : d ∈ (actionSchemaJson S drop).ets) :
    ∃ e, (d.name, e) ∈ S.ets.toList ∧ d.descendants = etDescendants S d.name := by
  simp only [actionSchemaJson, List.mem_map] at h
  obtain ⟨⟨n, e⟩, hmem, rfl⟩ := h
  cases e <;> exact ⟨_, hmem, rfl⟩

theorem mem_exportedEt {S : Schema} {drop : List String} {n : EntityType} {e : EntitySchemaEntry}
    (h : (n, e) ∈ S.ets.toList) :
    ∃ d ∈ (actionSchemaJson S drop).ets, d.name = n ∧ d.descendants = etDescendants S n := by
  simp only [actionSchemaJson, List.mem_map]
  refine ⟨_, ⟨(n, e), h, rfl⟩, ?_⟩
  cases e <;> exact ⟨rfl, rfl⟩

theorem specActionSchema_ets {l : Lowered} (hwf : l.schema.validateWellFormed = .ok ())
    (hne : l.schema.environments ≠ []) : (specActionSchema l).ets = l.schema.ets := by
  obtain ⟨env, hets, _, ⟨hmap, hent⟩, _, _⟩ := wellFormed_of_validate hwf hne
  rw [hets] at hmap hent
  unfold specActionSchema Conformance.ActionSchemaJson.toSchema
  show Map.make (List.map _ (List.map _ l.schema.ets.toList)) = _
  rw [List.map_map]
  conv => rhs; rw [hmap, ← List.map_id l.schema.ets.toList]
  congr 1
  apply List.map_congr_left
  intro ⟨n, e⟩ hmem
  have hfind := Map.mem_toList_find? hmap hmem
  have hwfe := hent n e hfind
  cases e with
  | enum eids =>
    simp only [Function.comp, id]
    show (n, EntitySchemaEntry.enum (Set.make eids.toList)) = _
    rw [← hwfe.1]
  | standard ty =>
    obtain ⟨anc, attrs, tags⟩ := ty
    obtain ⟨hanc, hancs, _⟩ := hwfe
    simp only [Function.comp, id]
    have hX : List.map (fun x => x.name) (List.filter (fun d' => d'.descendants.contains n)
        (actionSchemaJson l.schema l.hoistedNames).ets) ≡ anc.toList := by
      constructor
      · intro m hm
        simp only [List.mem_map, List.mem_filter] at hm
        obtain ⟨d, ⟨hd, hc⟩, rfl⟩ := hm
        obtain ⟨_, _, hdesc⟩ := exportedEt_of_mem hd
        rw [hdesc] at hc
        simp only [etDescendants, List.contains_iff_mem, List.mem_map, List.mem_filter] at hc
        obtain ⟨⟨n', e''⟩, ⟨hmem'', hanc''⟩, hn⟩ := hc
        simp only at hn
        subst hn
        have h'' := Map.mem_toList_find? hmap hmem''
        rw [hfind] at h''
        cases h''
        exact Set.contains_prop_bool_equiv.mp hanc''
      · intro m hm
        obtain ⟨entry, hf⟩ := hancs m hm
        rw [hets] at hf
        obtain ⟨d, hd, hname, hdesc⟩ :=
          mem_exportedEt (drop := l.hoistedNames) (Map.find?_mem_toList hf)
        simp only [List.mem_map, List.mem_filter]
        refine ⟨d, ⟨hd, ?_⟩, hname⟩
        rw [hdesc]
        simp only [etDescendants, List.contains_iff_mem, List.mem_map, List.mem_filter]
        exact ⟨_, ⟨hmem, Set.contains_prop_bool_equiv.mpr hm⟩, rfl⟩
    rw [(Set.make_make_eqv.mpr hX).trans hanc.symm]

/-! ## The round trip: actions -/

/-- The actions the projection exports as the descendants of `a`. -/
def actDescendants (S : Schema) (a : EntityUID) : List EntityUID :=
  (S.acts.toList.filter fun x => x.2.ancestors.contains a).map (·.1)

theorem exportedAct_of_mem {S : Schema} {drop : List String} {d : Conformance.ActionDecl}
    (h : d ∈ (actionSchemaJson S drop).acts) :
    ∃ e, (d.name, e) ∈ S.acts.toList ∧ d.descendants = actDescendants S d.name := by
  simp only [actionSchemaJson, List.mem_map] at h
  obtain ⟨⟨a, e⟩, hmem, rfl⟩ := h
  exact ⟨_, hmem, rfl⟩

theorem mem_exportedAct {S : Schema} {drop : List String} {a : EntityUID} {e : ActionSchemaEntry}
    (h : (a, e) ∈ S.acts.toList) :
    ∃ d ∈ (actionSchemaJson S drop).acts, d.name = a ∧ d.descendants = actDescendants S a := by
  simp only [actionSchemaJson, List.mem_map]
  exact ⟨_, ⟨(a, e), h, rfl⟩, rfl, rfl⟩

theorem specActionSchema_acts {l : Lowered} (hwf : l.schema.validateWellFormed = .ok ())
    (hne : l.schema.environments ≠ []) :
    (specActionSchema l).acts = l.schema.acts.mapOnValues (dropContext l.hoistedNames) := by
  obtain ⟨env, _, hacts, _, ⟨hmap, hent, _⟩, _⟩ := wellFormed_of_validate hwf hne
  rw [hacts] at hmap hent
  unfold specActionSchema Conformance.ActionSchemaJson.toSchema
  show Map.make (List.map _ (List.map _ l.schema.acts.toList)) = _
  rw [List.map_map, Map.mapOnValues_wf.mp hmap]
  congr 1
  show _ = List.map (fun x => (x.1, dropContext l.hoistedNames x.2)) l.schema.acts.toList
  apply List.map_congr_left
  intro ⟨a, e⟩ hmem
  have hfind := Map.mem_toList_find? hmap hmem
  obtain ⟨hp, hr, hanc, _, _, hancs, _⟩ := hent a e hfind
  simp only [Function.comp, dropContext]
  have hX : List.map (fun x => x.name) (List.filter (fun d' => d'.descendants.contains a)
      (actionSchemaJson l.schema l.hoistedNames).acts) ≡ e.ancestors.toList := by
    constructor
    · intro m hm
      simp only [List.mem_map, List.mem_filter] at hm
      obtain ⟨d, ⟨hd, hc⟩, rfl⟩ := hm
      obtain ⟨_, _, hdesc⟩ := exportedAct_of_mem hd
      rw [hdesc] at hc
      simp only [actDescendants, List.contains_iff_mem, List.mem_map, List.mem_filter] at hc
      obtain ⟨⟨a', e''⟩, ⟨hmem'', hanc''⟩, ha⟩ := hc
      simp only at ha
      subst ha
      have h'' := Map.mem_toList_find? hmap hmem''
      rw [hfind] at h''
      cases h''
      exact Set.contains_prop_bool_equiv.mp hanc''
    · intro m hm
      have hc := hancs m hm
      rw [hacts] at hc
      obtain ⟨em, hf⟩ := Map.contains_iff_some_find?.mp hc
      obtain ⟨d, hd, hname, hdesc⟩ :=
        mem_exportedAct (drop := l.hoistedNames) (Map.find?_mem_toList hf)
      simp only [List.mem_map, List.mem_filter]
      refine ⟨d, ⟨hd, ?_⟩, hname⟩
      rw [hdesc]
      simp only [actDescendants, List.contains_iff_mem, List.mem_map, List.mem_filter]
      exact ⟨_, ⟨hmem, Set.contains_prop_bool_equiv.mpr hm⟩, rfl⟩
  rw [(Set.make_make_eqv.mpr hX).trans hanc.symm]
  rw [← hp, ← hr]

/-- **The projection's action schema** is the augmented schema with the hoisted attributes
dropped from every action's context. -/
theorem specActionSchema_eq {l : Lowered} (hwf : l.schema.validateWellFormed = .ok ())
    (hne : l.schema.environments ≠ []) :
    specActionSchema l =
      { ets := l.schema.ets, acts := l.schema.acts.mapOnValues (dropContext l.hoistedNames) } := by
  rw [← specActionSchema_ets hwf hne, ← specActionSchema_acts hwf hne]

/-! ## The specification's names -/

theorem exportedAct_context {S : Schema} {drop : List String} {d : Conformance.ActionDecl}
    (h : d ∈ (actionSchemaJson S drop).acts) :
    ∃ e, (d.name, e) ∈ S.acts.toList ∧ d.context = (dropContext drop e).context := by
  simp only [actionSchemaJson, List.mem_map] at h
  obtain ⟨⟨a, e⟩, hmem, rfl⟩ := h
  exact ⟨_, hmem, rfl⟩

/-- No action of the projection declares an attribute named like the specification's leaves. -/
theorem specActionSchema_fresh {l : Lowered} (h : specNamesAbsent l = true) :
    ∀ act ∈ (specActionSchema l).acts.toList, ∀ a, isSpecLeafName a = true →
      act.2.context.find? a = none := by
  intro act hact a ha
  simp only [specNamesAbsent, Bool.and_eq_true, List.all_eq_true] at h
  have hctx := h.1
  unfold specActionSchema Conformance.ActionSchemaJson.toSchema at hact
  have hact := Map.mem_make_mem_list hact
  simp only [List.mem_map] at hact
  obtain ⟨d, hd, rfl⟩ := hact
  obtain ⟨e, hmem, hdc⟩ := exportedAct_context hd
  simp only
  rw [hdc, dropContext, Map.make_find?_eq_list_find?]
  cases hf : List.find? (fun x => x.fst == a)
      (e.context.toList.filter fun (k, _) => !l.hoistedNames.contains k) with
  | none => rfl
  | some p =>
    have hp := List.mem_of_find?_eq_some hf
    have hpa : p.1 = a := by simpa using List.find?_some hf
    have := hctx (d.name, e) hmem p (List.mem_filter.mp hp).1
    simp [hpa, ha] at this

/-! ## The augmented projection is well-formed -/

theorem exportedAct_applies {S : Schema} {drop : List String} {d : Conformance.ActionDecl}
    (h : d ∈ (actionSchemaJson S drop).acts) :
    ∃ e, (d.name, e) ∈ S.acts.toList ∧ d.principals = e.appliesToPrincipal.toList ∧
      d.resources = e.appliesToResource.toList := by
  simp only [actionSchemaJson, List.mem_map] at h
  obtain ⟨⟨a, e⟩, hmem, rfl⟩ := h
  exact ⟨_, hmem, rfl, rfl⟩

theorem mem_toList_make_toList {α : Type} [LT α] [DecidableLT α] [Cedar.Data.StrictLT α]
    {x : α} {xs : List α} (h : x ∈ (Set.make xs).toList) : x ∈ xs :=
  (Set.mem_make x xs).mp ((Set.mem_elts_iff_mem_set x _).mp h)

/-- Without an environment in the augmented schema, the specification's has none either. -/
theorem augment_environments_nil {l : Lowered} {H : List (Attr × QualifiedType)}
    (hne : l.schema.environments = []) :
    (Dogwood.Spec.Schema.augment (specActionSchema l) H).environments = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro env₂ henv₂
  obtain ⟨a, e₂, p, r, hmem, hp, hr, _⟩ := mem_environments.mp henv₂
  rw [augment_acts] at hmem
  simp only [Map.mapOnValues, Map.toList_mk_id, List.mem_map] at hmem
  obtain ⟨⟨a', e₁⟩, hmem₁, heq⟩ := hmem
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  unfold specActionSchema Conformance.ActionSchemaJson.toSchema at hmem₁
  have hmem₁ := Map.mem_make_mem_list hmem₁
  simp only [List.mem_map, Prod.mk.injEq] at hmem₁
  obtain ⟨d, hd, rfl, rfl⟩ := hmem₁
  obtain ⟨e, he, hP, hR⟩ := exportedAct_applies hd
  have hp' : p ∈ e.appliesToPrincipal.toList := by
    rw [← hP]; exact mem_toList_make_toList hp
  have hr' : r ∈ e.appliesToResource.toList := by
    rw [← hR]; exact mem_toList_make_toList hr
  have := mem_environments.mpr ⟨d.name, e, p, r, he, hp', hr', rfl⟩
  rw [hne] at this
  cases this

/-- **Adding well-formed, lifted attributes to every context keeps the projection well-formed.** -/
theorem augment_wellFormed {l : Lowered} {H : List (Attr × QualifiedType)}
    (hwf : l.schema.validateWellFormed = .ok ())
    (hH : ∀ p ∈ H, p.2.getType.validateWellFormed (schemaEnv l.schema) = .ok () ∧
      p.2.getType.validateLifted = .ok ()) :
    (Dogwood.Spec.Schema.augment (specActionSchema l) H).validateWellFormed = .ok () := by
  by_cases hne : l.schema.environments = []
  · unfold Schema.validateWellFormed
    rw [augment_environments_nil hne]
    rfl
  rw [specActionSchema_eq hwf hne]
  unfold Schema.validateWellFormed
  apply List.all_ok_implies_forM_ok
  intro env₂ henv₂
  have hacts₂ : (Dogwood.Spec.Schema.augment ⟨l.schema.ets, l.schema.acts.mapOnValues (dropContext l.hoistedNames)⟩
      H).acts = l.schema.acts.mapOnValues (fun e => augmentEntry H (dropContext l.hoistedNames e)) := by
    simp [augment_acts, Map.mapOnValues, Map.toList_mk_id, List.map_map, Function.comp_def]
  obtain ⟨a, e₂, p, r, hmem₂, hp, hr, rfl⟩ := mem_environments.mp henv₂
  rw [hacts₂] at hmem₂ ⊢
  simp only [Map.mapOnValues, Map.toList_mk_id, List.mem_map, Prod.mk.injEq] at hmem₂
  obtain ⟨⟨a', e⟩, hmem, rfl, rfl⟩ := hmem₂
  have henv₁ := mem_environments.mpr ⟨a', e, p, r, hmem, hp, hr, rfl⟩
  have h₁ := List.forM_ok_implies_all_ok _ _ hwf _ henv₁
  simp only [TypeEnv.validateWellFormed, bind_unit_ok_iff] at h₁ ⊢
  obtain ⟨hE, hA, hR⟩ := h₁
  have hkeys := keys_mapOnValues' (acts := l.schema.acts)
    (g := fun e => augmentEntry H (dropContext l.hoistedNames e))
  have hH' : ∀ env' : TypeEnv, env'.ets = l.schema.ets →
      env'.acts.toList.map Prod.fst = l.schema.acts.toList.map Prod.fst →
      ∀ q ∈ H, q.2.getType.validateWellFormed env' = .ok () ∧ q.2.getType.validateLifted = .ok () := by
    intro env' hets' hkeys' q hq
    rw [cedarType_validateWellFormed_congr (env := schemaEnv l.schema) hets' hkeys']
    exact hH q hq
  refine ⟨?_, ?_, ?_⟩
  · refine (entitySchema_validateWellFormed_congr ?_ ?_ _).trans hE
    · rfl
    · exact hkeys
  · refine actionSchema_validateWellFormed_mapOnValues ?_ ?_ ?_ (fun _ => ⟨rfl, rfl, rfl⟩) ?_ hA
    · rfl
    · exact hkeys
    · exact fun _ => Map.contains_mapOnValues _
    · intro _ hc hl
      refine augmentedContext_ok ?_ ?_ (hH' _ rfl hkeys) hc hl
      · rfl
      · exact hkeys
  · obtain ⟨_, _, hacts, _, ⟨hmap, _⟩, _⟩ := wellFormed_of_validate hwf hne
    rw [hacts] at hmap
    have hfind := Map.find?_mapOnValues_some
      (fun e => augmentEntry H (dropContext l.hoistedNames e)) (Map.mem_toList_find? hmap hmem)
    have hpc : (augmentEntry H (dropContext l.hoistedNames e)).appliesToPrincipal.contains p = true :=
      Set.contains_prop_bool_equiv.mpr ((Set.mem_elts_iff_mem_set _ _).mp hp)
    have hrc : (augmentEntry H (dropContext l.hoistedNames e)).appliesToResource.contains r = true :=
      Set.contains_prop_bool_equiv.mpr ((Set.mem_elts_iff_mem_set _ _).mp hr)
    simp only [RequestType.validateWellFormed, hfind, hpc, hrc, beq_self_eq_true, ↓reduceIte,
      Except.bind_ok]

/-! ## The projection's environments -/

theorem mem_mapOnValues_toList {acts : ActionSchema} {g : ActionSchemaEntry → ActionSchemaEntry}
    {a : EntityUID} {e' : ActionSchemaEntry} :
    (a, e') ∈ (acts.mapOnValues g).toList ↔ ∃ e, (a, e) ∈ acts.toList ∧ e' = g e := by
  simp only [Map.mapOnValues, Map.toList_mk_id, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a', e⟩, hmem, rfl, rfl⟩; exact ⟨e, hmem, rfl⟩
  · rintro ⟨e, hmem, rfl⟩; exact ⟨(a, e), hmem, rfl, rfl⟩

/-- The projection's actions: the augmented schema's, with the hoisted attributes dropped. -/
theorem specActionSchema_find? {l : Lowered} (hwf : l.schema.validateWellFormed = .ok ())
    (hne : l.schema.environments ≠ []) (a : EntityUID) :
    (specActionSchema l).acts.find? a = (l.schema.acts.find? a).map (dropContext l.hoistedNames) := by
  rw [specActionSchema_eq hwf hne]
  exact Map.find?_mapOnValues _ _ _

/-- The specification's augmented schema, on a well-formed augmented schema with an environment:
the augmented schema's entity types, and its actions with the hoisted attributes dropped from
each context and the attributes `H` added. -/
theorem augmentedSpec_eq {l : Lowered} {H : List (Attr × QualifiedType)}
    (hwf : l.schema.validateWellFormed = .ok ()) (hne : l.schema.environments ≠ []) :
    Dogwood.Spec.Schema.augment (specActionSchema l) H =
      { ets := l.schema.ets,
        acts := l.schema.acts.mapOnValues fun e => augmentEntry H (dropContext l.hoistedNames e) } := by
  rw [specActionSchema_eq hwf hne]
  show Schema.mk _ _ = Schema.mk _ _
  congr 1
  simp only [Map.mapOnValues, Map.toList_mk_id, List.map_map, Function.comp_def]
  rfl

/-- The projection's request environments are the augmented schema's, with the hoisted
attributes dropped from each context. -/
theorem mem_specEnvironments {l : Lowered} (hwf : l.schema.validateWellFormed = .ok ())
    (hne : l.schema.environments ≠ []) {env : TypeEnv} :
    env ∈ (specActionSchema l).environments ↔
      ∃ a e p r, (a, e) ∈ l.schema.acts.toList ∧ p ∈ e.appliesToPrincipal.toList ∧
        r ∈ e.appliesToResource.toList ∧
        env = { ets := l.schema.ets,
                acts := l.schema.acts.mapOnValues (dropContext l.hoistedNames),
                reqty := { principal := p, action := a, resource := r,
                           context := (dropContext l.hoistedNames e).context } } := by
  rw [specActionSchema_eq hwf hne, mem_environments]
  constructor
  · rintro ⟨a, e', p, r, hmem, hp, hr, rfl⟩
    obtain ⟨e, he, rfl⟩ := mem_mapOnValues_toList.mp hmem
    exact ⟨a, e, p, r, he, hp, hr, rfl⟩
  · rintro ⟨a, e, p, r, he, hp, hr, rfl⟩
    exact ⟨a, _, p, r, mem_mapOnValues_toList.mpr ⟨e, he, rfl⟩, hp, hr, rfl⟩

/-- The specification's augmented schema's request environments are the augmented schema's,
with the hoisted attributes dropped from each context and the attributes `H` added. -/
theorem mem_augmentedSpecEnvironments {l : Lowered} {H : List (Attr × QualifiedType)}
    (hwf : l.schema.validateWellFormed = .ok ()) (hne : l.schema.environments ≠ []) {env : TypeEnv} :
    env ∈ (Dogwood.Spec.Schema.augment (specActionSchema l) H).environments ↔
      ∃ a e p r, (a, e) ∈ l.schema.acts.toList ∧ p ∈ e.appliesToPrincipal.toList ∧
        r ∈ e.appliesToResource.toList ∧
        env = { ets := l.schema.ets,
                acts := l.schema.acts.mapOnValues fun e => augmentEntry H (dropContext l.hoistedNames e),
                reqty := { principal := p, action := a, resource := r,
                           context := (augmentEntry H (dropContext l.hoistedNames e)).context } } := by
  rw [augmentedSpec_eq hwf hne, mem_environments]
  constructor
  · rintro ⟨a, e', p, r, hmem, hp, hr, rfl⟩
    obtain ⟨e, he, rfl⟩ := mem_mapOnValues_toList.mp hmem
    exact ⟨a, e, p, r, he, hp, hr, rfl⟩
  · rintro ⟨a, e, p, r, he, hp, hr, rfl⟩
    exact ⟨a, _, p, r, mem_mapOnValues_toList.mpr ⟨e, he, rfl⟩, hp, hr, rfl⟩


/-! ## Enumerated ancestors -/

/-- No entity type of `S` has an enumerated ancestor, read off its entity types alone. -/
def NoEnumAncestor (S : Schema) : Prop :=
  ∀ d e, (d, e) ∈ S.ets.toList → ∀ anc ∈ e.ancestors.toList,
    (S.ets.find? anc).all (·.isStandard) = true

/-- The crate's schema check finds no enumerated ancestor only when there is none. -/
theorem noEnumAncestor_of_enumAncestors {S : Schema} (h : enumAncestors S = []) :
    NoEnumAncestor S := by
  intro d e hde anc hanc
  cases hf : S.ets.find? anc with
  | none => rfl
  | some x =>
    cases x with
    | standard _ => rfl
    | enum es =>
      exfalso
      cases e with
      | enum _ => exact List.not_mem_nil hanc
      | standard se =>
        have hd : d ∈ descendantsOf S anc := by
          unfold descendantsOf
          apply List.mem_filterMap.mpr
          refine ⟨(d, .standard se), hde, ?_⟩
          have hc : se.ancestors.contains anc = true :=
            Cedar.Data.Set.contains_prop_bool_equiv.mpr hanc
          simp only
          rw [if_pos hc]
        have hmem : (anc, descendantsOf S anc) ∈ enumAncestors S := by
          unfold enumAncestors
          apply List.mem_mergeSort.mpr
          apply List.mem_filterMap.mpr
          refine ⟨(anc, .enum es), Map.find?_mem_toList hf, ?_⟩
          simp only
          rw [if_neg]
          intro hemp
          rw [List.isEmpty_iff] at hemp
          rw [hemp] at hd
          cases hd
        rw [h] at hmem
        cases hmem

/-- On a schema whose entity map is well-formed, no enumerated ancestor means the crate's schema
check finds none. -/
theorem enumAncestors_nil_of {S : Schema} (hmap : Map.WellFormed S.ets) (h : NoEnumAncestor S) :
    enumAncestors S = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  unfold enumAncestors at hx
  obtain ⟨⟨E, e⟩, hE, hfx⟩ := List.mem_filterMap.mp (List.mem_mergeSort.mp hx)
  cases e with
  | standard _ => cases hfx
  | enum es =>
    simp only at hfx
    split at hfx
    · cases hfx
    · rename_i hne
      obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ (by simpa [List.isEmpty_iff] using hne)
      unfold descendantsOf at hd
      obtain ⟨⟨d', e'⟩, hde, hfd⟩ := List.mem_filterMap.mp hd
      cases e' with
      | enum _ => cases hfd
      | standard se =>
        simp only at hfd
        split at hfd
        · rename_i hc
          have := h d' (.standard se) hde E (Cedar.Data.Set.contains_prop_bool_equiv.mp hc)
          rw [Map.mem_toList_find? hmap hE] at this
          cases this
        · cases hfd

/-- `Schema.standardAncestors` holds when no entity type has an enumerated ancestor. -/
theorem standardAncestors_of {S : Schema} (h : NoEnumAncestor S) : S.standardAncestors = true := by
  unfold Schema.standardAncestors
  apply List.all_eq_true.mpr
  intro env henv
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := Dogwood.Thm.mem_environments.mp henv
  simp only [List.all_eq_true]
  intro ⟨d, e⟩ hde anc hanc
  exact h d e hde anc hanc

/-- `Schema.standardAncestors`, on a schema with a request environment. -/
theorem noEnumAncestor_of {S : Schema} (hs : S.standardAncestors = true)
    (hne : S.environments ≠ []) : NoEnumAncestor S := by
  obtain ⟨env, henv⟩ := List.exists_mem_of_ne_nil _ hne
  have h := List.all_eq_true.mp hs env henv
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := Dogwood.Thm.mem_environments.mp henv
  simp only [List.all_eq_true] at h
  intro d e hde anc hanc
  exact h (d, e) hde anc hanc

/-- **The specification's augmented schema has no enumerated ancestor when the crate's schema
check finds none.** -/
theorem augment_standardAncestors {l : Lowered} {H : List (Attr × QualifiedType)}
    (hwf : l.schema.validateWellFormed = .ok ()) (he : enumAncestors l.schema = []) :
    (Dogwood.Spec.Schema.augment (specActionSchema l) H).standardAncestors = true := by
  by_cases hne : l.schema.environments = []
  · unfold Schema.standardAncestors
    rw [augment_environments_nil hne]
    rfl
  · unfold Schema.standardAncestors
    apply List.all_eq_true.mpr
    intro env henv
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := (mem_augmentedSpecEnvironments hwf hne).mp henv
    simp only [List.all_eq_true]
    intro ⟨d, e⟩ hde anc hanc
    exact noEnumAncestor_of_enumAncestors he d e hde anc hanc

/-- **The crate's schema check finds no enumerated ancestor when the specification's augmented
schema has none**, on a schema with a request environment. -/
theorem enumAncestors_nil_of_augment {l : Lowered} {H : List (Attr × QualifiedType)}
    (hwf : l.schema.validateWellFormed = .ok ()) (hne : l.schema.environments ≠ [])
    (hs : (Dogwood.Spec.Schema.augment (specActionSchema l) H).standardAncestors = true) :
    enumAncestors l.schema = [] := by
  obtain ⟨env, hets, -, hw⟩ := wellFormed_of_validate hwf hne
  obtain ⟨hmap, -⟩ := hw.1
  rw [hets] at hmap
  apply enumAncestors_nil_of hmap
  obtain ⟨env₁, henv₁⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨a, e, p, r, hmem, hp, hr, -⟩ := Dogwood.Thm.mem_environments.mp henv₁
  have henv₂ := (mem_augmentedSpecEnvironments (H := H) hwf hne).mpr ⟨a, e, p, r, hmem, hp, hr, rfl⟩
  have h := List.all_eq_true.mp hs _ henv₂
  simp only [List.all_eq_true] at h
  intro d e' hde anc hanc
  exact h (d, e') hde anc hanc

end Dogwood.Thm.Frontend
