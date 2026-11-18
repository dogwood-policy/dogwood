import Cedar.Validation
import Cedar.Thm.Validation.EnvironmentValidation

/-!
# Schema well-formedness: what it depends on

Cedar's well-formedness check of a schema depends only on the entity types and the action names
(`cedarType_validateWellFormed_congr`), reads a record type attribute by attribute
(`record_validateWellFormed_ok_iff`), and is kept by replacing each action's context by one that
passes the checks the original passes (`actionSchema_validateWellFormed_mapOnValues`,
`augmentedContext_ok`). Moved here from `Dogwood.Thm.Frontend.Validate.Schema`, keeping its
namespace, so that the action-selective augmentation (`Dogwood.Thm.SelectiveAugment`) can use it.
-/

namespace Dogwood.Thm.Frontend

open Cedar.Validation
open Cedar.Spec (Attr EntityType EntityUID)
open Cedar.Data (Map Set)

/-! ## Well-formedness depends on the entity types and the action names only -/

theorem entityType_validateWellFormed_congr {env env' : TypeEnv} (hets : env'.ets = env.ets)
    (hkeys : env'.acts.toList.map Prod.fst = env.acts.toList.map Prod.fst) (ety : EntityType) :
    EntityType.validateWellFormed env' ety = EntityType.validateWellFormed env ety := by
  have h₁ : ∀ (L : List (EntityUID × ActionSchemaEntry)),
      (L.any fun (uid, _) => uid.ty == ety) = ((L.map Prod.fst).any fun uid => uid.ty == ety) := by
    intro L; rw [List.any_map]; rfl
  have hany : (env'.acts.toList.any fun (uid, _) => uid.ty == ety) =
      (env.acts.toList.any fun (uid, _) => uid.ty == ety) := by
    rw [h₁, h₁, hkeys]
  simp only [EntityType.validateWellFormed, hets, hany]

mutual

theorem qualifiedType_validateWellFormed_congr {env env' : TypeEnv} (hets : env'.ets = env.ets)
    (hkeys : env'.acts.toList.map Prod.fst = env.acts.toList.map Prod.fst) :
    (qty : QualifiedType) → qty.validateWellFormed env' = qty.validateWellFormed env
  | .optional ty => by
    simp only [QualifiedType.validateWellFormed]
    exact cedarType_validateWellFormed_congr hets hkeys ty
  | .required ty => by
    simp only [QualifiedType.validateWellFormed]
    exact cedarType_validateWellFormed_congr hets hkeys ty

theorem validateAttrsWellFormed_congr {env env' : TypeEnv} (hets : env'.ets = env.ets)
    (hkeys : env'.acts.toList.map Prod.fst = env.acts.toList.map Prod.fst) :
    (rty : List (Attr × QualifiedType)) →
      validateAttrsWellFormed env' rty = validateAttrsWellFormed env rty
  | [] => by simp only [validateAttrsWellFormed]
  | (a, qty) :: rest => by
    simp only [validateAttrsWellFormed]
    rw [qualifiedType_validateWellFormed_congr hets hkeys qty,
      validateAttrsWellFormed_congr hets hkeys rest]

/-- A type's well-formedness reads the environment's entity types and action names only. -/
theorem cedarType_validateWellFormed_congr {env env' : TypeEnv} (hets : env'.ets = env.ets)
    (hkeys : env'.acts.toList.map Prod.fst = env.acts.toList.map Prod.fst) :
    (ty : CedarType) → ty.validateWellFormed env' = ty.validateWellFormed env
  | .bool _ | .int | .string | .ext _ => by simp only [CedarType.validateWellFormed]
  | .entity ety => by
    simp only [CedarType.validateWellFormed]
    exact entityType_validateWellFormed_congr hets hkeys ety
  | .set ty => by
    simp only [CedarType.validateWellFormed]
    exact cedarType_validateWellFormed_congr hets hkeys ty
  | .record (.mk kvs) => by
    simp only [CedarType.validateWellFormed]
    rw [Map.toList_mk_id, validateAttrsWellFormed_congr hets hkeys kvs]

end

/-! ## The checks of a record type -/

theorem validateAttrsWellFormed_ok_iff {env : TypeEnv} : (L : List (Attr × QualifiedType)) →
    (validateAttrsWellFormed env L = .ok () ↔ ∀ p ∈ L, p.2.validateWellFormed env = .ok ())
  | [] => by simp [validateAttrsWellFormed]
  | (a, q) :: rest => by
    simp only [validateAttrsWellFormed]
    have ih := validateAttrsWellFormed_ok_iff (env := env) rest
    cases h : q.validateWellFormed env with
    | error e => simp [h]
    | ok u => cases u; simp [h, ih]

theorem record_validateWellFormed_ok_iff {env : TypeEnv} {rty : RecordType} :
    (CedarType.record rty).validateWellFormed env = .ok () ↔
      rty.wellFormed = true ∧ ∀ p ∈ rty.toList, p.2.validateWellFormed env = .ok () := by
  rw [CedarType.validateWellFormed]
  cases h : rty.wellFormed
  · simp
  · simp [validateAttrsWellFormed_ok_iff]

theorem record_validateLifted_ok_iff {rty : RecordType} :
    (CedarType.record rty).validateLifted = .ok () ↔
      ∀ p ∈ rty.toList, p.2.getType.validateLifted = .ok () := by
  rw [CedarType.validateLifted]
  constructor
  · intro h p hp
    have := List.forM_ok_implies_all_ok _ _ h ⟨p, hp⟩ (List.mem_attach _ _)
    obtain ⟨a, q⟩ := p
    cases q <;> exact this
  · intro h
    apply List.all_ok_implies_forM_ok
    intro ⟨⟨a, q⟩, hp⟩ _
    have := h (a, q) hp
    cases q <;> exact this

theorem qualifiedType_validateWellFormed_getType {env : TypeEnv} (q : QualifiedType) :
    q.validateWellFormed env = q.getType.validateWellFormed env := by
  cases q <;> simp [QualifiedType.validateWellFormed, Qualified.getType]

theorem bind_unit_ok_iff {ε : Type} {x : Except ε Unit} {f : Unit → Except ε Unit} :
    (x >>= f) = .ok () ↔ x = .ok () ∧ f () = .ok () := by
  cases x with
  | error => simp [bind, Except.bind]
  | ok u => cases u; simp [bind, Except.bind]

/-- The check of an action's entry, transferred to an environment with the same entity types and
action names, and to an entry with the same `appliesTo` sets and ancestors whose context passes
the checks the original's does. -/
theorem actionSchemaEntry_validateWellFormed_transfer {env env' : TypeEnv}
    {e e' : ActionSchemaEntry} (hets : env'.ets = env.ets)
    (hkeys : env'.acts.toList.map Prod.fst = env.acts.toList.map Prod.fst)
    (hcontains : ∀ uid, env'.acts.contains uid = env.acts.contains uid)
    (hP : e'.appliesToPrincipal = e.appliesToPrincipal)
    (hR : e'.appliesToResource = e.appliesToResource) (hA : e'.ancestors = e.ancestors)
    (hctx : (CedarType.record e.context).validateWellFormed env = .ok () →
      (CedarType.record e.context).validateLifted = .ok () →
      (CedarType.record e'.context).validateWellFormed env' = .ok () ∧
        (CedarType.record e'.context).validateLifted = .ok ())
    (h : e.validateWellFormed env = .ok ()) : e'.validateWellFormed env' = .ok () := by
  have hety : EntityType.validateWellFormed env' = EntityType.validateWellFormed env :=
    funext (entityType_validateWellFormed_congr hets hkeys)
  revert h
  simp only [ActionSchemaEntry.validateWellFormed, hP, hR, hA, hety, hcontains]
  cases e.appliesToPrincipal.wellFormed <;> cases e.appliesToResource.wellFormed <;>
    cases e.ancestors.wellFormed <;> simp only [Bool.false_eq_true, ↓reduceIte, Except.bind_ok,
      Except.bind_err, reduceCtorEq, imp_self]
  generalize e.appliesToPrincipal.toList.forM (EntityType.validateWellFormed env) = r₁
  generalize e.appliesToResource.toList.forM (EntityType.validateWellFormed env) = r₂
  generalize (e.ancestors.toList.forM fun uid =>
    if env.acts.contains uid = true then (Except.ok () : Except EnvironmentValidationError Unit)
    else .error (EnvironmentValidationError.typeError (toString "non-action ancestor " ++ toString uid))) = r₃
  intro h
  cases r₁ with
  | error => cases h
  | ok u₁ =>
    cases r₂ with
    | error => cases h
    | ok u₂ =>
      cases r₃ with
      | error => cases h
      | ok u₃ =>
        simp only [Except.bind_ok] at h ⊢
        cases hc : CedarType.validateWellFormed env (CedarType.record e.context) with
        | error => rw [hc] at h; cases h
        | ok u₄ =>
          rw [hc] at h
          simp only [Except.bind_ok] at h
          obtain ⟨h₁, h₂⟩ := hctx (by rw [hc]) h
          rw [h₁, h₂]
          rfl

theorem entitySchemaEntry_validateWellFormed_congr {env env' : TypeEnv} (hets : env'.ets = env.ets)
    (hkeys : env'.acts.toList.map Prod.fst = env.acts.toList.map Prod.fst)
    (entry : EntitySchemaEntry) :
    entry.validateWellFormed env' = entry.validateWellFormed env := by
  cases entry with
  | enum _ => rfl
  | standard entry =>
    simp only [EntitySchemaEntry.validateWellFormed, StandardSchemaEntry.validateWellFormed, hets,
      cedarType_validateWellFormed_congr hets hkeys]

theorem entitySchema_validateWellFormed_congr {env env' : TypeEnv} (hets : env'.ets = env.ets)
    (hkeys : env'.acts.toList.map Prod.fst = env.acts.toList.map Prod.fst) (ets : EntitySchema) :
    ets.validateWellFormed env' = ets.validateWellFormed env := by
  have h : (fun x : EntityType × EntitySchemaEntry => x.2.validateWellFormed env') =
      (fun x => x.2.validateWellFormed env) :=
    funext fun x => entitySchemaEntry_validateWellFormed_congr hets hkeys x.2
  simp only [EntitySchema.validateWellFormed, h]

/-! ## The action hierarchy depends on the ancestors only -/

theorem forM_map_eq {α β ε : Type} (L : List α) (f : α → β) (h : β → Except ε Unit) :
    (L.map f).forM h = L.forM (h ∘ f) := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    show (do h (f x); (L.map f).forM h) = (do (h ∘ f) x; L.forM (h ∘ f))
    rw [ih]; rfl

theorem acyclic_mapOnValues {acts : ActionSchema} {g : ActionSchemaEntry → ActionSchemaEntry}
    (hg : ∀ e, (g e).ancestors = e.ancestors) :
    ActionSchema.validateAcyclicActionHierarchy (acts.mapOnValues g) =
      acts.validateAcyclicActionHierarchy := by
  simp only [ActionSchema.validateAcyclicActionHierarchy, Map.mapOnValues, Map.toList_mk_id,
    forM_map_eq]
  congr 1
  funext x
  simp only [Function.comp, hg]

theorem transitive_mapOnValues {acts : ActionSchema} {g : ActionSchemaEntry → ActionSchemaEntry}
    (hg : ∀ e, (g e).ancestors = e.ancestors) :
    ActionSchema.validateTransitiveActionHierarchy (acts.mapOnValues g) =
      acts.validateTransitiveActionHierarchy := by
  simp only [ActionSchema.validateTransitiveActionHierarchy, Map.mapOnValues, Map.toList_mk_id,
    forM_map_eq]
  congr 1
  funext x
  simp only [Function.comp, hg]
  congr 1
  funext y
  simp only [Function.comp, hg]

theorem wellFormed_mapOnValues {acts : ActionSchema} {g : ActionSchemaEntry → ActionSchemaEntry} :
    (acts.mapOnValues g).wellFormed = acts.wellFormed := by
  rw [Bool.eq_iff_iff, Map.wellFormed_correct, Map.wellFormed_correct]
  exact Map.mapOnValues_wf.symm

/-! ## The augmented contexts -/

/-- A context with attributes dropped and well-formed, lifted attributes added passes the checks
the original passes. -/
theorem augmentedContext_ok {env env' : TypeEnv} (hets : env'.ets = env.ets)
    (hkeys : env'.acts.toList.map Prod.fst = env.acts.toList.map Prod.fst)
    {H : List (Attr × QualifiedType)} {drop : List String} {C : RecordType}
    (hH : ∀ p ∈ H, p.2.getType.validateWellFormed env' = .ok () ∧ p.2.getType.validateLifted = .ok ())
    (h : (CedarType.record C).validateWellFormed env = .ok ())
    (hl : (CedarType.record C).validateLifted = .ok ()) :
    (CedarType.record (Map.make ((Map.make (C.toList.filter fun (k, _) => !drop.contains k)).toList ++
        H))).validateWellFormed env' = .ok () ∧
      (CedarType.record (Map.make ((Map.make (C.toList.filter fun (k, _) => !drop.contains k)).toList ++
        H))).validateLifted = .ok () := by
  rw [record_validateWellFormed_ok_iff] at h ⊢
  rw [record_validateLifted_ok_iff] at hl ⊢
  have hsrc : ∀ p ∈ (Map.make ((Map.make (C.toList.filter fun (k, _) => !drop.contains k)).toList ++
      H)).toList, p ∈ C.toList ∨ p ∈ H := by
    intro p hp
    rcases List.mem_append.mp (Map.mem_make_mem_list hp) with hp | hp
    · exact .inl (List.mem_filter.mp (Map.mem_make_mem_list hp)).1
    · exact .inr hp
  refine ⟨⟨Map.wellFormed_correct.mpr (Map.make_wf _), fun p hp => ?_⟩, fun p hp => ?_⟩
  · rcases hsrc p hp with hp | hp
    · rw [qualifiedType_validateWellFormed_congr hets hkeys]
      exact h.2 p hp
    · rw [qualifiedType_validateWellFormed_getType]
      exact (hH p hp).1
  · rcases hsrc p hp with hp | hp
    · exact hl p hp
    · exact (hH p hp).2

/-! ## The action schema's check, transferred -/

theorem keys_mapOnValues' {acts : ActionSchema} {g : ActionSchemaEntry → ActionSchemaEntry} :
    (acts.mapOnValues g).toList.map Prod.fst = acts.toList.map Prod.fst := by
  simp [Map.mapOnValues, Map.toList_mk_id, List.map_map, Function.comp_def]

/-- The check of an action schema, transferred to an environment with the same entity types and
action names, and to the schema with each entry's context replaced by one that passes the checks
the original's does. -/
theorem actionSchema_validateWellFormed_mapOnValues {env env' : TypeEnv} {acts : ActionSchema}
    {g : ActionSchemaEntry → ActionSchemaEntry} (hets : env'.ets = env.ets)
    (hkeys : env'.acts.toList.map Prod.fst = env.acts.toList.map Prod.fst)
    (hcontains : ∀ uid, env'.acts.contains uid = env.acts.contains uid)
    (hg : ∀ e, (g e).appliesToPrincipal = e.appliesToPrincipal ∧
      (g e).appliesToResource = e.appliesToResource ∧ (g e).ancestors = e.ancestors)
    (hctx : ∀ e, (CedarType.record e.context).validateWellFormed env = .ok () →
      (CedarType.record e.context).validateLifted = .ok () →
      (CedarType.record (g e).context).validateWellFormed env' = .ok () ∧
        (CedarType.record (g e).context).validateLifted = .ok ())
    (h : acts.validateWellFormed env = .ok ()) :
    ActionSchema.validateWellFormed env' (acts.mapOnValues g) = .ok () := by
  revert h
  simp only [ActionSchema.validateWellFormed, wellFormed_mapOnValues,
    acyclic_mapOnValues (fun e => (hg e).2.2), transitive_mapOnValues (fun e => (hg e).2.2)]
  cases Map.wellFormed acts <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.bind_ok, Except.bind_err, reduceCtorEq,
      imp_self, bind_unit_ok_iff]
  rintro ⟨hall, hrest⟩
  refine ⟨?_, hrest⟩
  simp only [Map.mapOnValues, Map.toList_mk_id, forM_map_eq]
  apply List.all_ok_implies_forM_ok
  intro ⟨uid, e⟩ hmem
  have := List.forM_ok_implies_all_ok _ _ hall (uid, e) hmem
  simp only [Function.comp, hets] at this ⊢
  revert this
  cases env.ets.contains uid.ty <;>
    simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, imp_self]
  exact actionSchemaEntry_validateWellFormed_transfer hets hkeys hcontains (hg e).1 (hg e).2.1
    (hg e).2.2 (hctx e)


end Dogwood.Thm.Frontend
