import Dogwood.Thm.Frontend.Validate.Converse
import Dogwood.Thm.Frontend.Validate.ProviderComplete
import Dogwood.Thm.Frontend.Validate.TypingComplete
import Dogwood.Thm.Frontend.Validate.CedarComplete

/-!
# The frontend's validator is complete, up to the crate's stricter rules

`validate_complete`: if the frontend's earlier stages accepted a policy set, with the guarantees
they give (`Assumptions`, and `ConverseAssumptions`), Cedar's schema construction accepted the
augmented schema, and the specification's projection of the lowered set is valid, then the
frontend's validator reports no error, unless the lowered set breaks one of the crate's stricter
rules (`StrictRules`). Each stricter rule is a decidable property of the lowered set, and a rule of
the crate's validator that the specification does not have (a read or a pin under a reserved name,
the provider rules); `Counterexamples.lean` and the examples at the
end of `ProviderComplete.lean` give, for each temporal rule and each rule of `providerCompleteOk`,
a leaf the specification accepts and the crate rejects. The crate's left-to-right safety
check is a parse-time check, which `Assumptions.parse` takes as given; the crate's other
differences from the specification are outside the validator.

The proof takes each part of the port in turn:

* **context reads**: a rule whose put-back reads the request context only through its attributes
  reads it whole nowhere (`notWhole_of_readsContext`), no rule reads a reserved name
  (`StrictRules.reservedReads`), and the authored rules make no such read the lowered ones hide,
  a leaf's own name read by the author (`StrictRules.recordedReads`);
* **the provider part**: each provider leaf of the lowered set is a leaf of the projection
  (`provider_position'`), declared, and typed in every environment the crate checks it in
  (`specEnv_of_mem`), so the provider dialect reports nothing (`provider_complete`);
* **the Cedar part**: without leaves the two lowerings and schemas are the same; with leaves,
  Cedar's validator accepts the crate's lowering when it accepts the specification's
  (`validate_renameHoisted_converse`), since augmentation declares each hoisted read on the
  actions its rule targets (`graft_of`);
* **the temporal part**: each temporal leaf of the lowered set is a leaf of the projection, at a
  position whose facts agree with the crate's (`temporal_position'`), well-typed in every
  environment the crate checks it in, seen exactly (`viewExact_of`); a rule Cedar's validator
  accepts admits an environment (`admitted_of_cedar`), so the crate checks the leaf in one, and the
  temporal dialect reports nothing (`leaf_complete`).

`accepts_iff_valid` puts the two directions together.
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.Validate
open Dogwood.Spec (Expr Leaf leafAttr PolicySet)
open Dogwood.Spec.Temporal (Formula Guard TypingCtx)
open Cedar.Validation (CedarType Schema ActionSchemaEntry RecordType QualifiedType TypeEnv)
open Cedar.Data (Map)

section

variable {l : Lowered} {T : List (String × Formula)} {Pr : List (String × Dogwood.Spec.Provider.Call)}
  {sigs : Dogwood.Spec.EventSchema}

theorem lowered_ne (h : l.policies ≠ []) : (projected l T Pr sigs).lowered ≠ [] := by
  obtain ⟨q, qs, hq⟩ := List.exists_cons_of_ne_nil h
  simp [projected, PolicySet.lowered, hq, Dogwood.Spec.Policies.lowerFrom]

/-- With a rule, Cedar's validator accepting the specification's lowering needs an environment,
so the crate's schema has one. -/
theorem envs_ne_of_cedar (hpol : l.policies ≠ [])
    (hcedar : Cedar.Validation.validate (projected l T Pr sigs).lowered
      (projected l T Pr sigs).allAugmentedSchema = .ok ()) : l.schema.environments ≠ [] := by
  intro hnil
  have := validate_envs_ne (lowered_ne hpol) hcedar
  apply this
  unfold PolicySet.allAugmentedSchema
  exact augment_environments_nil hnil

/-- **The Cedar part, without leaves**: the specification's lowering and augmented schema are the
crate's. -/
theorem cedarFindings_nil_noLeaves (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hA : Assumptions l) (hwf : l.schema.validateWellFormed = .ok ()) (hlv : hasLeaves l = false)
    (hcedar : Cedar.Validation.validate (projected l T Pr sigs).lowered
      (projected l T Pr sigs).allAugmentedSchema = .ok ())
    (hinc : l.policies ≠ [] → (incompleteNames l).isEmpty = true) : cedarFindings l = [] := by
  unfold cedarFindings
  by_cases hpol : l.policies = []
  · simp [hpol]
  rw [if_neg (by simpa using hpol), if_pos (hinc hpol)]
  have hne := envs_ne_of_cedar hpol hcedar
  obtain ⟨-, -, hnd, -, -, -⟩ := namesOnce_spec hA.names
  unfold hasLeaves at hlv
  simp only [Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff] at hlv
  obtain ⟨ht, hp⟩ := hlv
  have hT0 : T.map Prod.fst = [] := by rw [tids_eq hT, ht]; rfl
  have hP0 : Pr.map Prod.fst = [] := by rw [pids_eq hPr, hp]; rfl
  have hreads : allReads l = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro ⟨b, a⟩ hr
    have := mem_allReads_contains hT hPr hr
    rw [hT0, hP0] at this
    cases b <;> simp at this
  have hH : (projected l T Pr sigs).hoistedTypes? = some [] := by
    unfold PolicySet.hoistedTypes?
    rw [projected_leafList hT hPr hA.leafless, hreads]
    rfl
  have hlow : (projected l T Pr sigs).lowered =
      (cedarPolicies l).map (renamePolicy (T.map Prod.fst) (Pr.map Prod.fst) (specRen l)) :=
    lowered_eq hT hPr hA.leafless hnd
  have hsch : (projected l T Pr sigs).allAugmentedSchema = l.schema := by
    unfold PolicySet.allAugmentedSchema
    rw [hH, Option.getD_some]
    exact augmented_of_noLeaves hwf hne ht hp
  rw [hlow, hsch, hT0, hP0] at hcedar
  have : (cedarPolicies l).map (renamePolicy [] [] (specRen l)) = cedarPolicies l := by
    conv => rhs; rw [← List.map_id (cedarPolicies l)]
    exact List.map_congr_left (fun p _ => renamePolicy_nil _ p)
  rw [this] at hcedar
  rw [hcedar]

end

/-! ## Unpacking the converse assumptions -/

section

variable {l : Lowered}

theorem withinScope_temporal (hs : scopesExact l = true) {j : Nat} {f : TemporalField} {k : Nat}
    {q : Dogwood.Spec.Policy} (hf : l.temporal[j]? = some f) (hk : l.temporalRules[j]? = some k)
    (hq : l.policies[k]? = some q) : withinScope l q f.targetActions f.principal f.resource = true := by
  unfold scopesExact at hs
  simp only [Bool.and_eq_true, List.all_eq_true] at hs
  have := hs.1 (f, k) (mem_zip_of_getElem? hf hk)
  simp only [hq] at this
  exact this

theorem withinScope_provider (hs : scopesExact l = true) {j : Nat} {g : LoweredProviderField} {k : Nat}
    {q : Dogwood.Spec.Policy} (hg : l.providers[j]? = some g) (hk : l.providerRules[j]? = some k)
    (hq : l.policies[k]? = some q) : withinScope l q g.targetActions g.principal g.resource = true := by
  unfold scopesExact at hs
  simp only [Bool.and_eq_true, List.all_eq_true] at hs
  have := hs.2 (g, k) (mem_zip_of_getElem? hg hk)
  simp only [hq] at this
  exact this

theorem rule_of_reads {k : Nat} {r : Bool × String} (h : r ∈ ((ruleReads l)[k]?).getD []) :
    ∃ q, l.policies[k]? = some q := by
  cases hk : l.policies[k]? with
  | some q => exact ⟨q, rfl⟩
  | none =>
    have : (ruleReads l)[k]? = none := by simp [ruleReads, hk]
    rw [this] at h; cases h

/-- A temporal leaf of the lowered set, with its position and rule. -/
theorem temporal_rule (hn : namesOnce l = true) {f : TemporalField} (hf : f ∈ l.temporal) :
    ∃ (j k : Nat) (q : Dogwood.Spec.Policy), l.temporal[j]? = some f ∧ l.temporalRules[j]? = some k ∧ l.policies[k]? = some q := by
  obtain ⟨hlen, -, -, htr, -, -⟩ := namesOnce_spec hn
  obtain ⟨j, hj⟩ := getElem?_of_mem' hf
  have hjl : j < l.temporalRules.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨q, hq⟩ := rule_of_reads (htr j f _ hj (List.getElem?_eq_getElem hjl))
  exact ⟨j, _, q, hj, List.getElem?_eq_getElem hjl, hq⟩

/-- A provider leaf of the lowered set, with its position and rule. -/
theorem provider_rule (hn : namesOnce l = true) {g : LoweredProviderField} (hg : g ∈ l.providers) :
    ∃ (j k : Nat) (q : Dogwood.Spec.Policy), l.providers[j]? = some g ∧ l.providerRules[j]? = some k ∧ l.policies[k]? = some q := by
  obtain ⟨-, hlen, -, -, hpr, -⟩ := namesOnce_spec hn
  obtain ⟨j, hj⟩ := getElem?_of_mem' hg
  have hjl : j < l.providerRules.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨q, hq⟩ := rule_of_reads (hpr j g _ hj (List.getElem?_eq_getElem hjl))
  exact ⟨j, _, q, hj, List.getElem?_eq_getElem hjl, hq⟩

theorem admits_putBackPolicy (T : List (String × Formula)) (Pr : List (String × Dogwood.Spec.Provider.Call))
    (q : Dogwood.Spec.Policy) (A : Schema) (env : TypeEnv) :
    (putBackPolicy T Pr q).admits A env = q.admits A env := rfl

theorem providersResolved_of (h : providersResolved l = true) {g : LoweredProviderField} (hg : g ∈ l.providers)
    {c : Dogwood.Spec.Provider.Call} (hc : g.toCall = .ok c)
    (hD : ((providerDeclsToSpec l.declarations l.schema).1.find? c.function).isSome = true) :
    ∃ d, g.declaration = some d := by
  unfold providersResolved at h
  rw [List.all_eq_true] at h
  have := h g hg
  simp only [hc, hD, Bool.not_true, Bool.false_or] at this
  exact Option.isSome_iff_exists.mp this

end

/-! ## A rule Cedar's validator accepts admits an environment -/

section

/-- Whether a rule's scope admits a request of the principal type, action, and resource type. -/
def admitsTriple (A : Schema) (q : Dogwood.Spec.Policy) (p : Cedar.Spec.EntityType)
    (a : Cedar.Spec.EntityUID) (r : Cedar.Spec.EntityType) : Bool :=
  match q.principalScope, q.resourceScope with
  | .principalScope ps, .resourceScope rs =>
    Dogwood.Spec.scopeAdmitsType A ps p && Dogwood.Spec.actionScopeAdmits A a q.actionScope &&
      Dogwood.Spec.scopeAdmitsType A rs r

theorem admits_eq_triple (A : Schema) (env : TypeEnv) (q : Dogwood.Spec.Policy) :
    q.admits A env = admitsTriple A q env.reqty.principal env.reqty.action env.reqty.resource := rfl

/-- Admission reads only the entity types' ancestors and the actions' hierarchy, which a schema
with each action's entry mapped keeping its ancestors keeps. -/
theorem admitsTriple_transfer {A B : Schema} (hets : B.ets = A.ets)
    {f : ActionSchemaEntry → ActionSchemaEntry} (hacts : B.acts = A.acts.mapOnValues f)
    (hf : ∀ e, (f e).ancestors = e.ancestors) (q : Dogwood.Spec.Policy) (p : Cedar.Spec.EntityType)
    (a : Cedar.Spec.EntityUID) (r : Cedar.Spec.EntityType) :
    admitsTriple B q p a r = admitsTriple A q p a r := by
  unfold admitsTriple
  split
  have hsc : ∀ s ety, Dogwood.Spec.scopeAdmitsType B s ety = Dogwood.Spec.scopeAdmitsType A s ety := by
    intro s ety
    cases s <;> simp [Dogwood.Spec.scopeAdmitsType, Dogwood.Spec.Schema.memberOfType, hets, hacts,
      mapOnValues_maybeDescendentOf hf]
  have hac : ∀ act s, Dogwood.Spec.actionScopeAdmits B act s = Dogwood.Spec.actionScopeAdmits A act s := by
    intro act s
    cases s with
    | actionScope s => cases s <;> simp [Dogwood.Spec.actionScopeAdmits, hacts, mapOnValues_descendentOf hf]
    | actionInAny ls => simp [Dogwood.Spec.actionScopeAdmits, hacts, mapOnValues_descendentOf hf]
  rw [hsc, hsc, hac]

theorem lowerFrom_mem : (ps : Dogwood.Spec.Policies) → (k₀ : Nat) → {k : Nat} → {q : Dogwood.Spec.Policy} →
    ps[k]? = some q → ∃ k', (q.lowerFrom k').1 ∈ (Dogwood.Spec.Policies.lowerFrom k₀ ps).1
  | [], _, _, _, h => by simp at h
  | p :: ps, k₀, 0, q, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨k₀, by simp [Dogwood.Spec.Policies.lowerFrom]⟩
  | p :: ps, k₀, k + 1, q, h => by
    simp only [List.getElem?_cons_succ] at h
    obtain ⟨k', hk'⟩ := lowerFrom_mem ps (p.lowerFrom k₀).2 h
    exact ⟨k', by simp only [Dogwood.Spec.Policies.lowerFrom, List.mem_cons]; exact Or.inr hk'⟩

end

section

variable {l : Lowered} {T : List (String × Formula)} {Pr : List (String × Dogwood.Spec.Provider.Call)}
  {sigs : Dogwood.Spec.EventSchema}

/-- **Every rule of the projection admits an environment**, when Cedar's validator accepts the
specification's lowering: a rule that admits none types `false` in every environment, an
impossible policy. -/
theorem admitted_of_cedar
    (hcedar : Cedar.Validation.validate (projected l T Pr sigs).lowered
      (projected l T Pr sigs).allAugmentedSchema = .ok ())
    {k : Nat} {q : Dogwood.Spec.Policy} (hq : l.policies[k]? = some q) :
    ∃ env ∈ (specActionSchema l).environments, q.admits (specActionSchema l) env = true := by
  have hq' : (projected l T Pr sigs).policies[k]? = some (putBackPolicy T Pr q) := by
    simp [projected, hq]
  obtain ⟨k', hk'⟩ := lowerFrom_mem _ 0 hq'
  obtain ⟨env₂, henv₂, had⟩ := exists_admitted_of_validate hcedar hk'
  have had' : admitsTriple (projected l T Pr sigs).allAugmentedSchema q env₂.reqty.principal
      env₂.reqty.action env₂.reqty.resource = true := had
  obtain ⟨a, e₂, pt, rt, hmem, hpt, hrt, rfl⟩ := Dogwood.Thm.mem_environments.mp henv₂
  simp only [PolicySet.allAugmentedSchema, Dogwood.Spec.Schema.augment, mapOnValues_toList,
    List.mem_map] at hmem
  obtain ⟨⟨a', e₁⟩, hmem₁, heq⟩ := hmem
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  refine ⟨_, Dogwood.Thm.mem_environments.mpr ⟨a', e₁, pt, rt, hmem₁, hpt, hrt, rfl⟩, ?_⟩
  have htr := admitsTriple_transfer (A := specActionSchema l)
    (B := (projected l T Pr sigs).allAugmentedSchema)
    (f := fun entry => { entry with
      context := Map.make (entry.context.toList ++ ((projected l T Pr sigs).hoistedTypes?.getD [])) })
    rfl rfl (fun _ => rfl) q pt a' rt
  show admitsTriple (specActionSchema l) q pt a' rt = true
  rw [← htr]
  exact had'

/-- **A leaf of a rule the specification's Cedar part accepts is checked in some environment.** -/
theorem envs_ne_of_admitted (hwf : l.schema.validateWellFormed = .ok ()) (hA : Assumptions l)
    {targets : List (String × String)} {pc rc : ScopeConstraint} {q : Dogwood.Spec.Policy}
    (hcov : coversScope l q targets pc rc = true)
    (hadm : ∃ env ∈ (specActionSchema l).environments, q.admits (specActionSchema l) env = true) :
    (targets.filterMap fun x => action? l.schema x.1 x.2).flatMap (fun x =>
      (admittedTypes l.schema x.2 .principal pc).flatMap fun p =>
        (admittedTypes l.schema x.2 .resource rc).map fun r => (⟨x.1, x.2, p, r⟩ : ReqEnv)) ≠ [] := by
  obtain ⟨env, henv, had⟩ := hadm
  obtain ⟨e, het, hep, her, -⟩ := leafEnv hwf hA.names hA.appliesTo hcov henv had
  intro h
  have := mem_envs_of het hep her
  rw [h] at this
  cases this

end

/-! ## The Cedar part, with leaves -/

section

open CedarComplete

mutual

theorem graftOk_of_reads {tids pids : List String} {C : RecordType} :
    (y : Cedar.Spec.Expr) →
      (∀ r ∈ hoistedReads tids pids (Expr.ofCedar y),
        (if r.1 then declaredRequired C r.2 else declaredProvider C r.2) = true) →
      graftOk tids pids C y = true
  | .getAttr e a, h => by
    simp only [Expr.ofCedar, hoistedReads, isContext_ofCedar, isContextProviders_ofCedar] at h
    simp only [graftOk]
    split
    · rename_i hc
      rw [if_pos hc] at h
      simpa using h (true, a) (by simp)
    · rename_i hc
      rw [if_neg hc] at h
      split
      · rename_i hp
        rw [if_pos hp] at h
        simpa using h (false, a) (by simp)
      · rename_i hp
        rw [if_neg hp] at h
        exact graftOk_of_reads e h
  | .lit _, _ | .var _, _ => by simp [graftOk]
  | .ite a b c, h => by
    simp only [Expr.ofCedar, hoistedReads, List.mem_append] at h
    simp only [graftOk, Bool.and_eq_true]
    exact ⟨⟨graftOk_of_reads a (fun r hr => h r (Or.inl (Or.inl hr))),
      graftOk_of_reads b (fun r hr => h r (Or.inl (Or.inr hr)))⟩,
      graftOk_of_reads c (fun r hr => h r (Or.inr hr))⟩
  | .and a b, h | .or a b, h | .binaryApp _ a b, h => by
    simp only [Expr.ofCedar, hoistedReads, List.mem_append] at h
    simp only [graftOk, Bool.and_eq_true]
    exact ⟨graftOk_of_reads a (fun r hr => h r (Or.inl hr)),
      graftOk_of_reads b (fun r hr => h r (Or.inr hr))⟩
  | .unaryApp _ x, h | .hasAttr x _, h | .extHasAttr x _ _, h => by
    simp only [Expr.ofCedar, hoistedReads] at h
    simp only [graftOk]
    exact graftOk_of_reads x h
  | .set xs, h | .call _ xs, h => by
    simp only [Expr.ofCedar, hoistedReads] at h
    simp only [graftOk]
    exact graftOkList_of_reads xs h
  | .record axs, h => by
    simp only [Expr.ofCedar, hoistedReads] at h
    simp only [graftOk]
    exact graftOkRecord_of_reads axs h

theorem graftOkList_of_reads {tids pids : List String} {C : RecordType} :
    (ys : List Cedar.Spec.Expr) →
      (∀ r ∈ hoistedReadsList tids pids (Expr.ofCedarList ys),
        (if r.1 then declaredRequired C r.2 else declaredProvider C r.2) = true) →
      graftOkList tids pids C ys = true
  | [], _ => rfl
  | y :: ys, h => by
    simp only [Expr.ofCedarList, hoistedReadsList, List.mem_append] at h
    simp only [graftOkList, Bool.and_eq_true]
    exact ⟨graftOk_of_reads y (fun r hr => h r (Or.inl hr)),
      graftOkList_of_reads ys (fun r hr => h r (Or.inr hr))⟩

theorem graftOkRecord_of_reads {tids pids : List String} {C : RecordType} :
    (ays : List (Cedar.Spec.Attr × Cedar.Spec.Expr)) →
      (∀ r ∈ hoistedReadsRecord tids pids (Expr.ofCedarRecord ays),
        (if r.1 then declaredRequired C r.2 else declaredProvider C r.2) = true) →
      graftOkRecord tids pids C ays = true
  | [], _ => rfl
  | (_, y) :: ays, h => by
    simp only [Expr.ofCedarRecord, hoistedReadsRecord, List.mem_append] at h
    simp only [graftOkRecord, Bool.and_eq_true]
    exact ⟨graftOk_of_reads y (fun r hr => h r (Or.inl hr)),
      graftOkRecord_of_reads ays (fun r hr => h r (Or.inr hr))⟩

end

variable {l : Lowered} {T : List (String × Formula)} {Pr : List (String × Dogwood.Spec.Provider.Call)}
  {sigs : Dogwood.Spec.EventSchema}

/-- A read of a temporal leaf in a rule is the read of a temporal leaf of that rule. -/
theorem temporalField_of_read (hn : namesOnce l = true) {k : Nat} {q : Dogwood.Spec.Policy}
    (hq : l.policies[k]? = some q) {a : String}
    (h : (true, a) ∈ hoistedReads (l.temporal.map (·.id)) (l.providers.map (·.id)) q.toExpr) :
    ∃ (j : Nat) (f : TemporalField), l.temporal[j]? = some f ∧ l.temporalRules[j]? = some k ∧ f.id = a := by
  obtain ⟨hlen, -, hnd, htr, -, -⟩ := namesOnce_spec hn
  have hc := mem_hoistedReads _ _ _ h
  simp only [if_true] at hc
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp (mem_of_contains hc)
  obtain ⟨j, hj⟩ := getElem?_of_mem' hf
  have hjl : j < l.temporalRules.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hj).1
  have hk' := List.getElem?_eq_getElem hjl
  have hread := htr j f _ hj hk'
  have hrk : (ruleReads l)[k]? =
      some (hoistedReads (l.temporal.map (·.id)) (l.providers.map (·.id)) q.toExpr) := by
    simp [ruleReads, hq]
  cases hr : (ruleReads l)[l.temporalRules[j]]? with
  | none => rw [hr] at hread; cases hread
  | some xs =>
    rw [hr, Option.getD_some] at hread
    have := index_unique_of_nodup_flatten hnd hr hrk hread h
    exact ⟨j, f, hj, by rw [hk', this], rfl⟩

/-- A read of a provider leaf in a rule is the read of a provider leaf of that rule. -/
theorem providerField_of_read (hn : namesOnce l = true) {k : Nat} {q : Dogwood.Spec.Policy}
    (hq : l.policies[k]? = some q) {a : String}
    (h : (false, a) ∈ hoistedReads (l.temporal.map (·.id)) (l.providers.map (·.id)) q.toExpr) :
    ∃ (j : Nat) (g : LoweredProviderField), l.providers[j]? = some g ∧ l.providerRules[j]? = some k ∧
      g.id = a := by
  obtain ⟨-, hlen, hnd, -, hpr, -⟩ := namesOnce_spec hn
  have hc := mem_hoistedReads _ _ _ h
  simp only [Bool.false_eq_true, if_false] at hc
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (mem_of_contains hc)
  obtain ⟨j, hj⟩ := getElem?_of_mem' hg
  have hjl : j < l.providerRules.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hj).1
  have hk' := List.getElem?_eq_getElem hjl
  have hread := hpr j g _ hj hk'
  have hrk : (ruleReads l)[k]? =
      some (hoistedReads (l.temporal.map (·.id)) (l.providers.map (·.id)) q.toExpr) := by
    simp [ruleReads, hq]
  cases hr : (ruleReads l)[l.providerRules[j]]? with
  | none => rw [hr] at hread; cases hread
  | some xs =>
    rw [hr, Option.getD_some] at hread
    have := index_unique_of_nodup_flatten hnd hr hrk hread h
    exact ⟨j, g, hj, by rw [hk', this], rfl⟩

theorem action?_of_mem (hwf : l.schema.validateWellFormed = .ok ()) (hne : l.schema.environments ≠ [])
    {a : Cedar.Spec.EntityUID} {e : ActionSchemaEntry} (hmem : (a, e) ∈ l.schema.acts.toList)
    {x : String × String} (hx : actionUidOf x.1 x.2 = a) : action? l.schema x.1 x.2 = some (a, e) := by
  simp only [action?, hx, Map.mem_toList_find? (acts_wf hwf hne) hmem, Option.map_some]

/-- **Augmentation declares every hoisted read of a rule** in each environment of the crate's
schema that the rule's scope admits. -/
theorem graft_of (hwf : l.schema.validateWellFormed = .ok ()) (hne : l.schema.environments ≠ [])
    (hA : Assumptions l) (hgr : leavesGrafted l = true) :
    ∀ p ∈ cedarPolicies l, ∀ env ∈ l.schema.environments,
      (Dogwood.Spec.Policy.ofCedar p).admits l.schema env = true →
        graftOk (l.temporal.map (·.id)) (l.providers.map (·.id)) env.reqty.context p.toExpr = true := by
  intro p hp env henv had
  obtain ⟨q, hq, k', rfl⟩ := mem_policies_lowerFrom _ _ hp
  obtain ⟨k, hk⟩ := getElem?_of_mem' hq
  have hof := policy_lowerFrom_ofCedar (leafless_spec hA.leafless q hq) k'
  apply graftOk_of_reads
  rw [hof]
  obtain ⟨a, e, pt, rt, hmem, hpt, hrt, rfl⟩ := Dogwood.Thm.mem_environments.mp henv
  have had₂ : admitsTriple l.schema q pt a rt = true := had
  obtain ⟨env', henv', hep, hea, her⟩ : ∃ env' ∈ (specActionSchema l).environments,
      env'.reqty.principal = pt ∧ env'.reqty.action = a ∧ env'.reqty.resource = rt :=
    ⟨_, (mem_specEnvironments hwf hne).mpr ⟨a, e, pt, rt, hmem, hpt, hrt, rfl⟩, rfl, rfl, rfl⟩
  have had' : q.admits (specActionSchema l) env' = true := by
    rw [admits_eq_triple, hep, hea, her, admitsTriple_transfer (specActionSchema_ets hwf hne)
      (specActionSchema_acts hwf hne) (fun _ => rfl)]
    exact had₂
  unfold leavesGrafted at hgr
  simp only [Bool.and_eq_true, List.all_eq_true] at hgr
  intro ⟨b, x⟩ hr
  cases b with
  | true =>
    obtain ⟨j, f, hfj, hkj, rfl⟩ := temporalField_of_read hA.names hk hr
    obtain ⟨⟨t, ht, hta⟩, -, -⟩ := covered (coversScope_temporal hA.scopes hfj hkj hk) henv' had'
    have := hgr.1 f (List.mem_of_getElem? hfj) t ht
    rw [action?_of_mem hwf hne hmem (hta.trans hea)] at this
    exact this
  | false =>
    obtain ⟨j, g, hgj, hkj, rfl⟩ := providerField_of_read hA.names hk hr
    obtain ⟨⟨t, ht, hta⟩, -, -⟩ := covered (coversScope_provider hA.scopes hgj hkj hk) henv' had'
    have := hgr.2 g (List.mem_of_getElem? hgj) t ht
    rw [action?_of_mem hwf hne hmem (hta.trans hea)] at this
    exact this

/-- **The Cedar part, with leaves**: Cedar's validator accepts the crate's lowering against the
crate's augmented schema when it accepts the specification's against the specification's. -/
theorem cedarFindings_nil_leaves (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hA : Assumptions l) (hwf : l.schema.validateWellFormed = .ok ()) (hgr : leavesGrafted l = true)
    (hlv : hasLeaves l = true) (hctx : contextFindings l = [])
    (hprovs : ∀ g ∈ l.providers, providerLeafFindings l.schema g = [])
    (hcedar : Cedar.Validation.validate (projected l T Pr sigs).lowered
      (projected l T Pr sigs).allAugmentedSchema = .ok ())
    (hinc : l.policies ≠ [] → (incompleteNames l).isEmpty = true) : cedarFindings l = [] := by
  unfold cedarFindings
  by_cases hpol : l.policies = []
  · simp [hpol]
  rw [if_neg (by simpa using hpol), if_pos (hinc hpol)]
  have hne := envs_ne_of_cedar hpol hcedar
  obtain ⟨-, -, hnd, -, -, hh⟩ := namesOnce_spec hA.names
  obtain ⟨H, hH⟩ := projected_hoistedTypes (sigs := sigs) hT hPr hA hprovs
  have hlow : (projected l T Pr sigs).lowered =
      (cedarPolicies l).map (renamePolicy (T.map Prod.fst) (Pr.map Prod.fst) (specRen l)) :=
    lowered_eq hT hPr hA.leafless hnd
  have hsch : (projected l T Pr sigs).allAugmentedSchema =
      Dogwood.Spec.Schema.augment (specActionSchema l) H := by
    unfold PolicySet.allAugmentedSchema; rw [hH]; rfl
  rw [hlow, hsch, augmentedSpec_eq hwf hne] at hcedar
  have hval : Cedar.Validation.validate (cedarPolicies l) l.schema = .ok () := by
    refine validate_renameHoisted_converse (reserved := isSpecLeafName) (S₁ := l.schema)
      (S₂ := { ets := l.schema.ets,
               acts := l.schema.acts.mapOnValues fun e => augmentEntry H (dropContext l.hoistedNames e) })
      (f := fun e => augmentEntry H (dropContext l.hoistedNames e)) ?_ ?_
      (tidsNotProviders hT hA.names) rfl rfl
      (fun _ => ⟨rfl, rfl, rfl⟩) ?_ (acts_wf hwf hne) ?_ ?_ ?_ hcedar
    · intro b₁ i₁ b₂ i₂ h₁ h₂ heq
      rw [tids_eq hT, pids_eq hPr] at h₁ h₂
      have hr₁ := read_of_id hA h₁
      have hr₂ := read_of_id hA h₂
      have := eq_of_idxOf_eq hr₁ hr₂ (leafAttr_inj heq)
      simp only [Prod.mk.injEq] at this
      exact this
    · intro b i; exact isSpecLeafName_leafAttr _
    · intro uid e hfind
      exact ctxRel_projected hT hPr hA hprovs hH (Map.find?_mem_toList hfind)
    · intro hpne uid e q ety hfind hq
      have hpn := hA.providersNotEntity
      unfold providersNotEntity at hpn
      have hpe : l.providers.isEmpty = false := by
        rw [pids_eq hPr] at hpne
        cases hps : l.providers with
        | nil => rw [hps] at hpne; exact absurd rfl hpne
        | cons _ _ => rfl
      rw [hpe, Bool.false_or, List.all_eq_true] at hpn
      have := hpn (uid, e) (Map.find?_mem_toList hfind)
      simp only [hq] at this
      intro hty
      rw [hty] at this
      cases this
    · intro p hp
      obtain ⟨q, hq, k', rfl⟩ := mem_policies_lowerFrom _ _ hp
      have hql := leafless_spec hA.leafless q hq
      have hof := policy_lowerFrom_ofCedar hql k'
      have hT' : ∀ a ∈ l.temporal.map (·.id), isHoistedName a = true := by
        intro a ha; obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha; exact (hh f hf).1
      have htp' : (l.temporal.map (·.id)).contains "providers" = false := by
        simp only [List.contains_eq_any_beq, List.any_map, Bool.eq_false_iff, ne_eq,
          List.any_eq_true, not_exists, not_and, Function.comp, beq_iff_eq]
        intro f hf h; exact (hh f hf).2 h.symm
      have := renameOk_of_reads ⟨l.temporal.map (·.id), l.providers.map (·.id)⟩ hT' htp'
        (q.lowerFrom k').1.toExpr
        (by rw [hof]; exact contextReads_nil hctx hlv q hq)
        (by rw [hof]; exact (specNames_spec hA.specNames).2 q hq)
      rw [tids_eq hT, pids_eq hPr]
      exact this
    · rw [tids_eq hT, pids_eq hPr]
      exact graft_of hwf hne hA hgr
  rw [hval]

end

/-! ## The provider part -/

/-- The crate's stricter provider rules that `providerExceptionsOk` does not state, for a leaf whose
rule admits a request environment: the declaration declares each method once, and each string
literal argument is declared `string` (`providerCompleteOk` without its rules for a rule that
admits no environment). -/
def providerStrictOk (g : LoweredProviderField) (d : ProviderDecls.ProviderDecl) : Bool :=
  providerMethodsDistinct d && providerLiteralKindsExact false g.invocation.args d.argumentTypes &&
  g.methods.all (fun m =>
    match d.methods.lookup m.name with
    | some md => providerLiteralKindsExact false m.args md.argumentTypes
    | none => true)

theorem providerCompleteOk_of {S : Schema} {g : LoweredProviderField} {d : ProviderDecls.ProviderDecl}
    (hne : (providerCtx S g).envs ≠ []) (h : providerStrictOk g d = true) :
    providerCompleteOk S g d = true := by
  have he : (providerCtx S g).envs.isEmpty = false := by
    cases hc : (providerCtx S g).envs with
    | nil => exact absurd hc hne
    | cons _ _ => rfl
  unfold providerCompleteOk
  unfold providerStrictOk at h
  simp only [he, Bool.not_false, Bool.true_or, Bool.and_true]
  exact h

section

variable {l : Lowered} {T : List (String × Formula)} {Pr : List (String × Dogwood.Spec.Provider.Call)}
  {sigs : Dogwood.Spec.EventSchema}

/-- **The provider part**: the port reports nothing on a provider leaf the specification accepts,
unless the leaf meets one of the crate's stricter provider rules. -/
theorem providerFindings_nil (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hA : Assumptions l) (hwf : l.schema.validateWellFormed = .ok ())
    (hexact : scopesExact l = true) (hres : providersResolved l = true)
    (hids : (l.providers.map (·.id)).Nodup)
    (hcedar : Cedar.Validation.validate (projected l T Pr sigs).lowered
      (projected l T Pr sigs).allAugmentedSchema = .ok ())
    (hV : ∀ p ∈ (projected l T Pr sigs).policies, ∀ c F, (.inr c, F) ∈ p.toExpr.leafFacts [] →
      c.Declared (projected l T Pr sigs).providerDecls ∧ ∀ env ∈ (projected l T Pr sigs).envsOf p,
        c.TypedIn ((projected l T Pr sigs).typingCtx env F) (projected l T Pr sigs).providerDecls)
    (hX : ∀ g ∈ l.providers, ∀ d, g.declaration = some d →
      providerExceptionsOk l.schema g d = true ∧ providerStrictOk g d = true) :
    ∀ g ∈ l.providers, providerLeafFindings l.schema g = [] := by
  intro g hg
  obtain ⟨j, k, q, hgj, hkj, hqk⟩ := provider_rule hA.names hg
  obtain ⟨⟨a, c⟩, -, ha, hc⟩ := forall₂_mem_left (providerCalls_forall₂ hPr) hg
  simp only at ha hc
  obtain ⟨F, hF⟩ := provider_position' hT hPr hA.leafless hA.names hids hgj hkj hqk hc
  obtain ⟨hdecl, htyped⟩ := hV _ (List.mem_map.mpr ⟨q, List.mem_of_getElem? hqk, rfl⟩) c F hF
  have hDs : ((providerDeclsToSpec l.declarations l.schema).1.find? c.function).isSome = true := by
    obtain ⟨sig, hsig, -⟩ := hdecl
    simp only [projected] at hsig
    rw [hsig]; rfl
  obtain ⟨d, hd⟩ := providersResolved_of hres hg hc hDs
  obtain ⟨hD, -⟩ := providerTypes_of hA.providerTypes hg hd hc
  obtain ⟨hX₁, hX₂⟩ := hX g hg d hd
  have hne : (providerCtx l.schema g).envs ≠ [] :=
    envs_ne_of_admitted hwf hA (coversScope_provider hA.scopes hgj hkj hqk) (admitted_of_cedar hcedar hqk)
  apply provider_complete hd hc hD hdecl _ hX₁ (providerCompleteOk_of hne hX₂)
  intro e he
  obtain ⟨env, henv, had, hview⟩ :=
    specEnv_of_mem hwf hA.names hA.appliesTo (withinScope_provider hexact hgj hkj hqk) he
  refine ⟨(projected l T Pr sigs).typingCtx env F, hview _ rfl, htyped env ?_⟩
  simp only [PolicySet.envsOf, List.mem_filter]
  exact ⟨henv, had⟩

/-! ## The temporal part -/

/-- **The temporal part**: the port reports nothing on a temporal leaf the specification accepts,
unless the leaf meets one of the crate's stricter rules. -/
theorem temporalFindings_nil (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hS : typedSignatures l.eventSchema l.schema = .ok sigs) (hA : Assumptions l)
    (hwf : l.schema.validateWellFormed = .ok ())
    (hexact : scopesExact l = true) (hfields : derivedFieldsResolve l = true)
    (hids : (l.temporal.map (·.id)).Nodup) (hapart : actionsApart l.schema = true)
    (hcedar : Cedar.Validation.validate (projected l T Pr sigs).lowered
      (projected l T Pr sigs).allAugmentedSchema = .ok ())
    (hV : ∀ p ∈ (projected l T Pr sigs).policies, ∀ φ F, (.inl φ, F) ∈ p.toExpr.leafFacts [] →
      (projected l T Pr sigs).LeafValid p F φ)
    (hX : ∀ f ∈ l.temporal, ∀ φ, f.condition.condition.toFormula = .ok φ →
      noReservedHeadReadsF φ = true)
    (hpins : pinHeadsUnreserved l.eventSchema = true)
    (hH : ∀ H, (projected l T Pr sigs).maxHorizon = some H →
      ∀ φ ∈ (projected l T Pr sigs).temporalLeaves, φ.horizon .seconds ≤ H)
    {leaves : List (TemporalField × Formula)} (hL : leafFormulas l = .ok leaves) :
    ∀ x ∈ leaves, leafFindings (leafCtx l (loweredFacts l) x.1) x.2 = [] := by
  intro ⟨f, φ⟩ hx
  obtain ⟨hf, hφ⟩ := mem_leafFormulas hL hx
  simp only at hf hφ ⊢
  obtain ⟨j, k, q, hfj, hkj, hqk⟩ := temporal_rule hA.names hf
  obtain ⟨G, F, hG, hm, hsub, hsub'⟩ :=
    temporal_position' hT hPr hA.leafless hA.names hids hfj hkj hqk hφ
  have hv := hV _ (List.mem_map.mpr ⟨q, List.mem_of_getElem? hqk, rfl⟩) φ F hm
  have hX₂ := hX f hf φ hφ
  have hres : ∀ ev ∈ l.eventSchema.events,
      ev.leafFields.all (fun x => lookupPath ev x.1 == .leaf) = true := by
    unfold derivedFieldsResolve at hfields
    rw [List.all_eq_true] at hfields
    exact hfields
  have hne : (leafCtx l (loweredFacts l) f).envs ≠ [] :=
    envs_ne_of_admitted hwf hA (coversScope_temporal hA.scopes hfj hkj hqk) (admitted_of_cedar hcedar hqk)
  refine leaf_complete hv.monitorsTime hne ?_ hX₂ hapart hpins ?_
  rotate_left
  · have hmem : φ ∈ (projected l T Pr sigs).temporalLeaves := by
      simp only [PolicySet.temporalLeaves, List.mem_flatMap, List.mem_filterMap]
      refine ⟨_, List.mem_map.mpr ⟨q, List.mem_of_getElem? hqk, rfl⟩, .inl φ, ?_, rfl⟩
      rw [← Dogwood.Thm.leafFacts_fst []]
      exact List.mem_map.mpr ⟨_, hm, rfl⟩
    exact fun H hc => hH H hc φ hmem
  intro e he
  obtain ⟨env, henvm, had, hview⟩ :=
    specEnv_of_mem hwf hA.names hA.appliesTo (withinScope_temporal hexact hfj hkj hqk) he
  refine ⟨(projected l T Pr sigs).typingCtx env F, ?_, hv.wellTyped env ?_⟩
  · refine viewExact_of (C := leafCtx l (loweredFacts l) f) (e := e)
      (C' := (projected l T Pr sigs).typingCtx env F) ?_ ?_ hS hres
    · exact {
        toEnvView := hview _ rfl
        maxWindow := rfl
        facts := by
          intro g hg hr
          simp only [leafCtx, hG, Option.getD_some] at hg
          exact hsub g hg hr
        events := fun a kd ev hev => events_agree hS (derived_spec hA.derived) hev }
    · intro g hg
      simp only [leafCtx, hG, Option.getD_some]
      exact hsub' g hg
  · simp only [PolicySet.envsOf, List.mem_filter]
    exact ⟨henvm, had⟩

end

/-! ## Completeness -/

/-- **What the validator's completeness assumes of the earlier stages beyond `Assumptions`**, each
decided by `Dogwood.Frontend.Validate.converseAssumptions`. -/
structure ConverseAssumptions (l : Lowered) : Prop where
  /-- Each leaf's target actions and narrowing admit only environments its rule admits. -/
  scopes : scopesExact l = true
  /-- A provider leaf whose provider the projection declares has a declaration. -/
  providers : providersResolved l = true
  /-- Derivation finds each leaf field of a derived event by its path. -/
  fields : derivedFieldsResolve l = true
  /-- The leaves' ids are distinct. -/
  ids : leafIdsDistinct l = true
  /-- Augmentation declares each leaf's attribute, required, on its rule's target actions. -/
  grafted : leavesGrafted l = true
  /-- The schema's actions are its uids of a type named `Action`. -/
  actionsApart : actionsApart l.schema = true

/-- **The crate's stricter rules**: what the crate's validator rejects and `PolicySet.Valid`
accepts. -/
structure StrictRules (l : Lowered) : Prop where
  /-- No temporal leaf reads a `context.<path>` whose head is a name lowering reserves. -/
  contextHeads : ∀ f ∈ l.temporal, ∀ φ, f.condition.condition.toFormula = .ok φ →
    noReservedHeadReadsF φ = true
  /-- No pin of a derived event correlates its field with such a path. -/
  pinHeads : pinHeadsUnreserved l.eventSchema = true
  /-- No provider leaf meets one of the crate's stricter provider rules: a declared
  entity type that is not an enum, a method named like a Cedar extension method, an argument
  under a reserved context name or ambiguous on the scope, a method declared twice, a string
  literal declared other than `string`. -/
  providers : ∀ g ∈ l.providers, ∀ d, g.declaration = some d →
    providerExceptionsOk l.schema g d = true ∧ providerStrictOk g d = true
  /-- No rule reads or tests a request-context attribute whose name lowering reserves, other than
  the leaves' own. -/
  reservedReads : ∀ r ∈ loweredReads l, r.1 = true
  /-- The authored rules, as the crate records their reads while it lowers them, read no
  attribute whose name lowering reserves, a leaf's own included, and read the context whole only
  in a set without leaves. -/
  recordedReads : ∀ r ∈ l.contextReads, r.1 = true ∧ hasLeaves l = false
  /-- A schema without request environments, of a set without rules, has no enumerated ancestor
  (cedar-lean's well-formedness, which `PolicySet.Valid` requires, is checked in each request
  environment; the crate checks the entity types alone). -/
  enumAncestors : l.policies = [] → l.schema.environments = [] → enumAncestors l.schema = []

/-- **The frontend's validator is complete, up to the crate's stricter rules.** If the earlier
stages of the frontend accepted a policy set, with the guarantees they give (`Assumptions`,
`ConverseAssumptions`), Cedar's schema construction accepted the augmented schema, and the
specification's projection of the lowered set is valid, then the validator reports no error,
unless the lowered set breaks one of the crate's stricter rules (`StrictRules`). -/
theorem validate_complete {l : Lowered} {c : Conformance.Lowered}
    (hc : l.toConformance = .ok c) (hV : c.policySet.Valid) (hA : Assumptions l)
    (hB : ConverseAssumptions l) (hwf : l.schema.validateWellFormed = .ok ()) (hX : StrictRules l) :
    ∃ fs, validate l = .ok fs ∧ ∀ f ∈ fs, f.warning = true := by
  obtain ⟨T, Pr, sigs, hT, hPr, hS, hP⟩ := toConformance_ok hc
  rw [hP] at hV
  have hV' : (projected l T Pr sigs).ValidAll := PolicySet.Valid.toAll hV
  obtain ⟨leaves, hL⟩ := leafFormulas_ok hT
  have hids := hB.ids
  unfold leafIdsDistinct at hids
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hids
  have hctx := contextFindings_nil hT hPr hA hV'.readsContext hX.reservedReads hX.recordedReads
  have hprovs := providerFindings_nil hT hPr hA hwf hB.scopes hB.providers hids.2 hV'.cedar
    hV'.providers hX.providers
  have hinc : l.policies ≠ [] → (incompleteNames l).isEmpty = true := by
    intro hpol
    obtain ⟨h₁, h₂⟩ := hV'.complete (by simpa [projected] using hpol)
    simp only [projected] at h₁ h₂
    simp [incompleteNames, h₁, h₂]
  have hcedar : cedarFindings l = [] := by
    cases hlv : hasLeaves l
    · exact cedarFindings_nil_noLeaves hT hPr hA hwf hlv hV'.cedar hinc
    · exact cedarFindings_nil_leaves hT hPr hA hwf hB.grafted hlv hctx hprovs hV'.cedar hinc
  have hschema : schemaFindings l = [] := by
    have : enumAncestors l.schema = [] := by
      by_cases hne : l.schema.environments = []
      · by_cases hpol : l.policies = []
        · exact hX.enumAncestors hpol hne
        · exact absurd hne (envs_ne_of_cedar hpol hV'.cedar)
      · have hs := hV'.standardAncestors
        obtain ⟨H, hH⟩ := projected_hoistedTypes (sigs := sigs) hT hPr hA hprovs
        unfold PolicySet.allAugmentedSchema at hs
        rw [hH, Option.getD_some] at hs
        exact enumAncestors_nil_of_augment hwf hne hs
    unfold schemaFindings
    rw [this]
    rfl
  have htemp := temporalFindings_nil hT hPr hS hA hwf hB.scopes hB.fields hids.1 hB.actionsApart
    hV'.cedar hV'.temporal hX.contextHeads
    hX.pinHeads hV'.horizon hL
  exact validate_of_parts hL hcedar hschema hctx htemp hprovs

/-- **The validator decides validity**, on a lowered set that meets the guarantees of the earlier
stages and breaks none of the crate's stricter rules: it accepts exactly when the specification's
projection is valid. -/
theorem accepts_iff_valid {l : Lowered} {c : Conformance.Lowered} (hc : l.toConformance = .ok c)
    (hA : Assumptions l) (hB : ConverseAssumptions l) (hwf : l.schema.validateWellFormed = .ok ())
    (hX : StrictRules l) : accepts l = true ↔ c.policySet.Valid := by
  constructor
  · intro h
    unfold accepts at h
    split at h
    · rename_i fs hv
      exact validate_sound hc hv (fun f hf => List.all_eq_true.mp h f hf) hA hwf
    · cases h
  · intro hV
    obtain ⟨fs, hv, hw⟩ := validate_complete hc hV hA hB hwf hX
    unfold accepts
    rw [hv]
    exact List.all_eq_true.mpr hw

end Dogwood.Thm.Frontend
