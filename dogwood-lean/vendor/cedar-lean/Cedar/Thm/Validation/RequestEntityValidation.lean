import Cedar.Validation.RequestEntityValidator
import Cedar.Validation.EnvironmentValidator
import Cedar.Thm.Validation.EnvironmentValidation
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Validator

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem instance_of_bool_type_refl {b : Bool} {bty : BoolType} :
  instanceOfBoolType b bty = true → InstanceOfBoolType b bty
:= by
  simp only [instanceOfBoolType, InstanceOfBoolType]
  intro h₀
  cases h₁ : b <;> cases h₂ : bty <;> subst h₁ <;> subst h₂ <;> simp only [Bool.false_eq_true] at *

theorem instance_of_entity_type_refl {e : EntityUID} {ety : EntityType} {env : TypeEnv} :
  instanceOfEntityType e ety env.schema = true → InstanceOfEntityType e ety env
:= by
  simp only [InstanceOfEntityType, instanceOfEntityType]
  intro h₀
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h₀
  simp only [EntityUID.WellFormed]
  exact h₀

theorem instance_of_ext_type_refl {ext : Ext} {extty : ExtType} :
  instanceOfExtType ext extty = true → InstanceOfExtType ext extty
:= by
  simp only [InstanceOfExtType, instanceOfExtType]
  intro h₀
  cases h₁ : ext <;> cases h₂ : extty <;> subst h₁ <;> subst h₂ <;> simp only [Bool.false_eq_true] at *

theorem instance_of_type_refl {v : Value} {ty : CedarType} {env : TypeEnv} :
  instanceOfType v ty env.schema = true → InstanceOfType env v ty
:= by
  intro h₀
  unfold instanceOfType at h₀
  cases v with
  | prim p =>
    cases p with
    | bool b =>
      cases ty
      case bool bty =>
        apply InstanceOfType.instance_of_bool b bty
        apply instance_of_bool_type_refl
        assumption
      all_goals contradiction
    | int i =>
      cases ty
      case int => exact InstanceOfType.instance_of_int
      all_goals contradiction
    | string s =>
      cases ty
      case string => exact InstanceOfType.instance_of_string
      all_goals contradiction
    | entityUID uid =>
      cases ty
      case entity ety =>
        apply InstanceOfType.instance_of_entity uid ety
        apply instance_of_entity_type_refl
        assumption
      all_goals contradiction
  | set s =>
    cases ty
    case set sty =>
      apply InstanceOfType.instance_of_set s sty
      split at h₀ <;> simp only [reduceCtorEq, imp_self, implies_true, Value.set.injEq,
        CedarType.set.injEq, imp_false, forall_apply_eq_imp_iff, forall_eq'] at *
      subst s sty
      rw [Set.all₁_eq_all (f := (instanceOfType · _ env.schema))] at h₀
      simp only [Set.all, List.all_eq_true] at h₀
      intro v hv
      simp only [Set.mem_elts_iff_mem_set] at h₀
      exact instance_of_type_refl (h₀ v hv)
    all_goals contradiction
  | record r =>
    cases ty
    case record rty =>
      apply InstanceOfType.instance_of_record r rty
      all_goals simp only [Bool.and_eq_true, List.all_eq_true] at h₀
      intro k h₁
      simp only [Map.contains_iff_some_find?] at h₁
      have ⟨⟨h₂, _⟩, _⟩ := h₀
      replace ⟨v, h₁⟩ := h₁
      specialize h₂ (k, v)
      simp only at h₂
      apply h₂ (Map.find?_mem_toList h₁)
      intro k v qty h₁ h₂
      have ⟨⟨_, h₄⟩, _⟩ := h₀
      have h₆ : sizeOf (k,v).snd < 1 + sizeOf r.toList
      := by
        have hin := Map.find?_mem_toList h₁
        simp only
        replace hin := List.sizeOf_lt_of_mem hin
        simp only [Prod.mk.sizeOf_spec] at hin
        omega
      specialize h₄ ⟨(k, v), h₆⟩
      simp only [List.attach₂, List.mem_pmap_subtype] at h₄
      have h₇ := h₄ (Map.find?_mem_toList h₁)
      cases h₈ : rty.find? k with
      | none =>
        rw [h₂] at h₈
        contradiction
      | some vl =>
        simp only [h₈] at h₇
        simp only [h₈, Option.some.injEq] at h₂
        subst h₂
        exact instance_of_type_refl h₇
      intro k qty h₁ h₂
      have ⟨⟨_, h₄⟩, h₅⟩ := h₀ ; clear h₀
      simp only [List.attach₂] at h₄
      simp only [requiredAttributePresent, Bool.ite_true_right, Bool.decide_eq_true] at h₅
      specialize h₅ (k, qty)
      simp only [h₁, Bool.or_eq_true, Bool.not_eq_true'] at h₅
      have h₆ := Map.find?_mem_toList h₁
      simp only [Map.toList] at h₆
      cases h₅ h₆ with
      | inl h₅ =>
        rw [h₂] at h₅
        contradiction
      | inr h₅ => exact h₅
    all_goals contradiction
  | ext e =>
    cases ty
    case ext ety =>
      apply InstanceOfType.instance_of_ext
      apply instance_of_ext_type_refl
      assumption
    all_goals contradiction
termination_by v
decreasing_by
  all_goals
    simp_wf
    simp only [Bool.and_eq_true, List.all_eq_true] at h₀
    simp only [Value.set.injEq, CedarType.set.injEq, Prod.forall, Subtype.forall] at *
  case _ v' _ _ _ _ h₁ _ _ _ =>
    subst_vars
    simp only [Value.set.sizeOf_spec]
    have := Set.sizeOf_lt_of_mem hv
    omega
  case _ h₉ _ _ _ _ _ _ =>
    subst h₉
    have h₁ := Map.find?_mem_toList h₁
    simp only [Value.record.sizeOf_spec, gt_iff_lt]
    have := Map.sizeOf_lt_of_value h₁
    simp only [Map.mk_toList_id] at this
    omega

theorem instance_of_request_type_refl {request : Request} {env : TypeEnv}:
  instanceOfRequestType request env = true → InstanceOfRequestType request env
:= by
  intro h₀
  simp only [InstanceOfRequestType]
  simp only [instanceOfRequestType, Bool.and_eq_true, beq_iff_eq] at h₀
  have ⟨⟨⟨h₁,h₂⟩,h₃⟩, h₄⟩ := h₀
  and_intros
  · exact (instance_of_entity_type_refl h₁).1
  · exact (instance_of_entity_type_refl h₁).2
  · exact h₂
  · exact (instance_of_entity_type_refl h₃).1
  · exact (instance_of_entity_type_refl h₃).2
  · exact instance_of_type_refl h₄

theorem instance_of_schema_refl {entities : Entities} {env : TypeEnv} :
  instanceOfSchema entities env = .ok () → InstanceOfSchema entities env
:= by
  intro h₀
  simp only [InstanceOfSchema]
  simp only [instanceOfSchema, bind, Except.bind] at h₀
  split at h₀
  case h_1 => contradiction
  case h_2 h₀₁ =>
  generalize h₁ : (λ x : EntityUID × EntityData =>
    instanceOfSchema.instanceOfSchemaEntry env x.fst x.snd) = f
  rw [h₁] at h₀₁
  constructor
  · intro uid data h₂
    have h₀ := List.forM_ok_implies_all_ok (Map.toList entities) f h₀₁ (uid, data)
    replace h₀ := h₀ (Map.find?_mem_toList h₂)
    rw [← h₁] at h₀
    simp only [
      instanceOfSchema.instanceOfSchemaEntry,
      instanceOfSchema.instanceOfEntitySchemaEntry,
      instanceOfSchema.instanceOfActionSchemaEntry,
    ] at h₀
    cases h₂ : Map.find? env.ets uid.ty <;> simp [h₂] at h₀
    case some entry =>
      apply Or.inl
      exists entry
      simp only [h₂, true_and]
      split at h₀ <;> try simp only [reduceCtorEq] at h₀
      rename_i hv
      constructor
      simp only [EntitySchemaEntry.isValidEntityEID] at hv
      simp only [IsValidEntityEID]
      split at hv
      · simp
      · simp
        rw [Set.contains_prop_bool_equiv] at hv
        exact hv
      split at h₀ <;> try simp only [reduceCtorEq] at h₀
      constructor <;> rename_i h₃
      · exact instance_of_type_refl h₃
      · split at h₀ <;> try simp only [reduceCtorEq] at h₀
        rename_i h₄
        simp only [Set.all, List.all_eq_true] at h₄
        constructor
        · intro anc ancin
          simp only [Set.contains, List.elem_eq_mem] at h₄
          rw [← Set.mem_elts_iff_mem_set] at ancin
          replace h₄ := h₄ anc ancin
          simp at h₄
          exact h₄.left
        · split at h₀ <;> try simp only [reduceCtorEq] at h₀
          unfold InstanceOfEntityTags
          rename_i h₅
          simp only [instanceOfSchema.instanceOfEntityTags] at h₅
          split at h₅ <;> rename_i heq <;> simp only [heq]
          · intro v hv
            simp only [List.all_eq_true] at h₅
            exact instance_of_type_refl (h₅ v hv)
          · simp only [beq_iff_eq] at h₅
            exact h₅
    case none =>
      apply Or.inr
      split at h₀
      split at h₀
      split at h₀
      split at h₀
      any_goals contradiction
      case _ h₃ h₄ h₅ =>
      simp [InstanceOfActionSchemaEntry]
      and_intros
      · assumption
      · assumption
      · simp [h₄, h₅]
  · generalize h₁ : (fun x : EntityUID × ActionSchemaEntry =>
      instanceOfSchema.actionExists entities x.fst) = f
    rw [h₁] at h₀
    intro uid entry h₂
    replace h₀ := List.forM_ok_implies_all_ok (Map.toList env.acts) f h₀ (uid, entry)
    replace h₀ := h₀ (Map.find?_mem_toList h₂)
    rw [← h₁] at h₀
    simp only [instanceOfSchema.actionExists] at h₀
    cases h₂ : Map.find? entities uid <;> simp only [ite_eq_left_iff, Bool.not_eq_true,
      reduceCtorEq, imp_false, Bool.not_eq_false] at h₀
    case some data => exists data
    case none => simp [Map.contains, h₂] at h₀

theorem instance_of_well_formed_env {env : TypeEnv} {request : Request} {entities : Entities} :
  env.validateWellFormed = .ok () →
  requestMatchesEnvironment env request →
  entitiesMatchEnvironment env entities = .ok () →
  InstanceOfWellFormedEnvironment request entities env
:= by
  intro h₀ h₁ h₂
  simp only [InstanceOfWellFormedEnvironment]
  simp only [requestMatchesEnvironment] at h₁
  simp only [entitiesMatchEnvironment] at h₂
  constructor
  exact env_validate_well_formed_is_sound h₀
  constructor
  · exact instance_of_request_type_refl h₁
  · cases h₃ : instanceOfSchema entities env <;> simp only [h₃, reduceCtorEq] at h₂
    exact instance_of_schema_refl h₃

theorem request_and_entities_validate_implies_instance_of_wf_schema (schema : Schema) (request : Request) (entities : Entities) :
  schema.validateWellFormed = .ok () →
  validateRequest schema request = .ok () →
  validateEntities schema entities = .ok () →
  InstanceOfWellFormedSchema schema request entities
:= by
  intro h₀ h₁ h₂
  simp only [InstanceOfWellFormedSchema]
  simp only [validateRequest, List.any_eq_true, ite_eq_left_iff, not_exists, not_and,
    Bool.not_eq_true, reduceCtorEq, imp_false, Classical.not_forall,
    Bool.not_eq_false] at h₁
  simp only [validateEntities] at h₂
  simp only [Schema.validateWellFormed] at h₀
  replace ⟨env, ⟨h₁, h₃⟩⟩ := h₁
  exists env
  apply And.intro h₁
  apply instance_of_well_formed_env
  simp only [List.forM_ok_implies_all_ok schema.environments TypeEnv.validateWellFormed h₀ env h₁]
  assumption
  simp only [List.forM_ok_implies_all_ok schema.environments (entitiesMatchEnvironment · entities) h₂ env h₁]

----- How validation depends on the schema -----

/-- `instanceOfType` depends on its schema only through `instanceOfEntityType`. -/
theorem instanceOfType_mono {s₁ s₂ : Schema}
  (hmono : ∀ e ety, instanceOfEntityType e ety s₁ = true →
    instanceOfEntityType e ety s₂ = true)
  (v : Value) (ty : CedarType) (h : instanceOfType v ty s₁ = true) :
  instanceOfType v ty s₂ = true
:= by
  suffices hsize : ∀ n (v : Value) (ty : CedarType), sizeOf v < n →
      instanceOfType v ty s₁ = true → instanceOfType v ty s₂ = true from
    hsize (sizeOf v + 1) v ty (Nat.lt_succ_self _) h
  intro n
  induction n with
  | zero => intro _ _ hlt; omega
  | succ n ih =>
    intro v ty hlt h
    cases v with
    | prim p =>
      cases p with
      | entityUID e =>
        cases ty
        case entity ety =>
          unfold instanceOfType at h ⊢
          exact hmono e ety h
        all_goals unfold instanceOfType at h ⊢; exact h
      | _ => cases ty <;> (unfold instanceOfType at h ⊢; exact h)
    | set s =>
      cases ty
      case set ty =>
        unfold instanceOfType at h ⊢
        rw [Set.all₁_eq_all (f := (instanceOfType · ty s₁))] at h
        rw [Set.all₁_eq_all (f := (instanceOfType · ty s₂))]
        rw [Set.all_eq_true] at h ⊢
        intro x hx
        apply ih x ty _ (h x hx)
        have := Set.sizeOf_lt_of_mem hx
        simp only [Value.set.sizeOf_spec] at hlt
        omega
      all_goals unfold instanceOfType at h ⊢; exact h
    | record r =>
      cases ty
      case record rty =>
        unfold instanceOfType at h ⊢
        simp only [Bool.and_eq_true] at h ⊢
        obtain ⟨⟨hkeys, hvals⟩, hreq⟩ := h
        refine ⟨⟨hkeys, ?_⟩, hreq⟩
        rw [List.all_eq_true] at hvals ⊢
        intro ⟨⟨k, v⟩, hv⟩ hmem
        have hval := hvals ⟨⟨k, v⟩, hv⟩ hmem
        simp only at hval ⊢
        cases hq : rty.find? k with
        | none => rfl
        | some qty =>
          simp only [hq] at hval
          apply ih v qty.getType _ hval
          have hmem' : (k, v) ∈ r.1 := List.mem_attach₂ hmem
          have hlt' := Map.sizeOf_lt_of_value hmem'
          simp only [Value.record.sizeOf_spec] at hlt
          omega
      all_goals unfold instanceOfType at h ⊢; exact h
    | ext _ => cases ty <;> (unfold instanceOfType at h ⊢; exact h)

/-- A record valid against a record type has only attributes of that type. -/
theorem instanceOfType_record_contains {r : Map Attr Value} {rty : RecordType} {schema : Schema}
  {a : Attr}
  (h : instanceOfType (.record r) (.record rty) schema = true)
  (ha : r.contains a = true) :
  rty.contains a = true
:= by
  unfold instanceOfType at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨v, hfind⟩ := Map.contains_iff_some_find?.mp ha
  exact h.1.1 (a, v) (Map.find?_mem_toList hfind)

/-- A record valid against a record type has each required attribute of that type. -/
theorem instanceOfType_record_required {r : Map Attr Value} {rty : RecordType} {schema : Schema}
  {a : Attr} {ty : CedarType}
  (h : instanceOfType (.record r) (.record rty) schema = true)
  (hrequired : rty.find? a = some (.required ty)) :
  r.contains a = true
:= by
  unfold instanceOfType at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have hpresent := h.2 (a, .required ty) (Map.find?_mem_toList hrequired)
  simpa [requiredAttributePresent, hrequired, Qualified.isRequired] using hpresent

-- The facts below unfold the nested definitions generated for `instanceOfSchema`.

/-- Entity-entry validation depends on its schema only through `instanceOfEntityType`. -/
theorem instanceOfEntitySchemaEntry_mono {env₁ env₂ : TypeEnv}
  {uid : EntityUID} {data : EntityData} {entry : EntitySchemaEntry}
  (h : instanceOfSchema.instanceOfEntitySchemaEntry env₁ uid data entry = .ok ())
  (hmono : ∀ e ety, instanceOfEntityType e ety env₁.schema = true →
    instanceOfEntityType e ety env₂.schema = true) :
  instanceOfSchema.instanceOfEntitySchemaEntry env₂ uid data entry = .ok ()
:= by
  simp only [instanceOfSchema.instanceOfEntitySchemaEntry] at h ⊢
  split at h <;> try contradiction
  rename_i heid
  split at h <;> try contradiction
  rename_i hattrs
  split at h <;> try contradiction
  rename_i hancestors
  split at h <;> try contradiction
  rename_i htags
  have hattrs' := instanceOfType_mono hmono _ _ hattrs
  have hancestors' : data.ancestors.all (fun ancestor =>
      entry.ancestors.contains ancestor.ty &&
      instanceOfEntityType ancestor ancestor.ty env₂.schema) = true := by
    rw [Set.all_eq_true] at hancestors ⊢
    intro ancestor hmem
    have hancestor := hancestors ancestor hmem
    simp only [Bool.and_eq_true] at hancestor ⊢
    exact ⟨hancestor.1, hmono _ _ hancestor.2⟩
  have htags' : instanceOfSchema.instanceOfEntityTags env₂ data entry = true := by
    simp only [instanceOfSchema.instanceOfEntityTags] at htags ⊢
    cases htty : entry.tags? with
    | none => simpa [htty] using htags
    | some tty =>
      simp only [htty, List.all_eq_true] at htags ⊢
      exact fun value hvalue => instanceOfType_mono hmono _ _ (htags value hvalue)
  simp [heid, hattrs', hancestors', htags']

/-- Action-entry validation depends on its schema only through the action's ancestors. -/
theorem instanceOfActionSchemaEntry_mono {env₁ env₂ : TypeEnv}
  {uid : EntityUID} {data : EntityData}
  (h : instanceOfSchema.instanceOfActionSchemaEntry env₁ uid data = .ok ())
  (hacts : ∀ entry, env₁.acts.find? uid = some entry →
    ∃ entry', env₂.acts.find? uid = some entry' ∧ entry'.ancestors = entry.ancestors) :
  instanceOfSchema.instanceOfActionSchemaEntry env₂ uid data = .ok ()
:= by
  simp only [instanceOfSchema.instanceOfActionSchemaEntry] at h ⊢
  split at h <;> try contradiction
  rename_i hattrs
  split at h <;> try contradiction
  rename_i htags
  split at h
  · rename_i entry hentry
    split at h <;> try contradiction
    rename_i hancestors
    obtain ⟨_, hentry', heq⟩ := hacts entry hentry
    simp only [beq_iff_eq] at hancestors
    simp [hattrs, htags, hentry', heq, hancestors]
  · contradiction

/-- A valid action entity is an action of the schema. -/
theorem instanceOfActionSchemaEntry_find? {env : TypeEnv}
  {uid : EntityUID} {data : EntityData}
  (h : instanceOfSchema.instanceOfActionSchemaEntry env uid data = .ok ()) :
  ∃ entry, env.acts.find? uid = some entry
:= by
  simp only [instanceOfSchema.instanceOfActionSchemaEntry] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h
  · rename_i entry hentry
    exact ⟨entry, hentry⟩
  · contradiction

/-- Validating an entity depends on the environment only through its entity and action schemas. -/
theorem instanceOfSchemaEntry_eq {env₁ env₂ : TypeEnv}
  (hets : env₁.ets = env₂.ets) (hacts : env₁.acts = env₂.acts) :
  instanceOfSchema.instanceOfSchemaEntry env₁ =
    instanceOfSchema.instanceOfSchemaEntry env₂
:= by
  obtain ⟨ets, acts, _⟩ := env₁
  obtain ⟨_, _, _⟩ := env₂
  dsimp only at hets hacts
  subst hets hacts
  rfl

/-- A valid entity of a type the schema declares has attributes of that type. -/
theorem instanceOfSchemaEntry_attrs {env : TypeEnv} {uid : EntityUID}
  {data : EntityData} {entry : EntitySchemaEntry}
  (h : instanceOfSchema.instanceOfSchemaEntry env uid data = .ok ())
  (hfind : env.ets.find? uid.ty = some entry) :
  instanceOfType data.attrs (.record entry.attrs) env.schema = true
:= by
  simp only [instanceOfSchema.instanceOfSchemaEntry, hfind,
    instanceOfSchema.instanceOfEntitySchemaEntry] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  assumption

/-- In a well-formed environment, the entity of each action is valid. -/
theorem instanceOfSchemaEntry_actionEntity {env : TypeEnv} {uid : EntityUID}
  {entry : ActionSchemaEntry} (hwf : env.WellFormed) (hmem : (uid, entry) ∈ env.acts.toList) :
  instanceOfSchema.instanceOfSchemaEntry env uid (actionSchemaEntryToEntityData entry) =
    .ok ()
:= by
  have hfind := (Map.in_list_iff_find?_some (wf_env_implies_wf_acts_map hwf)).mp hmem
  -- An action's type is not an entity type.
  have hets : env.ets.find? uid.ty = none := by
    cases h : env.ets.find? uid.ty with
    | none => rfl
    | some _ => exact (wf_env_disjoint_ets_acts hwf h hfind).elim
  simp [instanceOfSchema.instanceOfSchemaEntry, instanceOfSchema.instanceOfActionSchemaEntry,
    actionSchemaEntryToEntityData, hets, hfind]
