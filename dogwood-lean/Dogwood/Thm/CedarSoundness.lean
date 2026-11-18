import Dogwood.Thm.Lowering
import Dogwood.Thm.SelectiveAugment
import Dogwood.Thm.Soundness
import Dogwood.Thm.Decision
import Cedar.Thm.Validation
import Cedar.Thm.Validation.EnvironmentValidation

/-!
# Soundness of the Cedar part

Validity requires Cedar's validator to accept the lowered rules against the augmented schema
(`PolicySet.Valid.cedar`), and so against the schema that adds every leaf's attribute to every
action (`PolicySet.allAugmentedSchema`, `Dogwood.Thm.valid_iff_validAll`), whose request types
hold the whole augmented request context. So Cedar's validation soundness theorem applies to them:
on a request and an entity store that are instances of that schema, every lowered rule evaluates to a
`Bool`, or fails with one of the runtime errors validation cannot rule out (`entityDoesNotExist`,
`extensionError`, `arithBoundsError`). This module builds such a request from a decision:

* the **augmented request** (`PolicySet.augmentRequest`) is the decision's request with its
  context extended by every leaf's value at the leaf's attribute (a policy set without leaves
  leaves the request as it is);
* at a decision every check of which passes (`PolicySet.Admits`), the augmented request and the
  decision's entity store are instances of an environment of the augmented schema
  (`augmented_request`, `augmented_entities`): the request part is the request's environment
  with the leaves' attributes added, which validity keeps fresh and distinct, and the leaves'
  values have their declared types, a temporal leaf a `Bool` and a provider leaf its declared
  output type;
* so every lowered rule evaluates to a `Bool` or a runtime error (`cedar_sound`), and the
  decision's response is Cedar's on the lowered rules (`isAuthorized_lower`).
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Value Attr Request Entities EntityUID)
open Cedar.Data (Map)
open Cedar.Validation (CedarType RecordType TypeEnv Schema QualifiedType Qualified
  ActionSchemaEntry RequestType)
open Cedar.Thm (InstanceOfType InstanceOfEntityType InstanceOfRequestType InstanceOfSchema
  InstanceOfWellFormedEnvironment)


/-- The augmented context holds every leaf's value at its attribute. -/
theorem augmentContext_leaf {P : PolicySet} (hnd : P.hoistedNames.Nodup) (θ : Leaves)
    (ctx : Map Attr Value) {i : Nat} (hi : i < P.leafList.length) :
    (P.augmentContext θ ctx).find? (leafAttr i) = some (θ.valueOf P.leafList[i]) := by
  have hne : P.leafList ≠ [] := List.ne_nil_of_length_pos (by omega)
  simp only [PolicySet.augmentContext, if_neg hne]
  rw [make_append_find?, find?_of_mem (by rw [leafEntries_keys]; exact hnd) (mem_leafEntries hi)]
  rfl

/-- Outside the leaves' attributes, the augmented context is the context. -/
theorem augmentContext_other {P : PolicySet} (θ : Leaves) (ctx : Map Attr Value) {a : Attr}
    (ha : a ∉ P.hoistedNames) : (P.augmentContext θ ctx).find? a = ctx.find? a := by
  unfold PolicySet.augmentContext
  split
  · rfl
  · rw [make_append_find?, find?_of_not_mem (by rw [leafEntries_keys]; exact ha), map_find?_eq]
    simp

/-- The augmented context holds every leaf's value at its attribute. -/
theorem augmentRequest_leaves {P : PolicySet} (hnd : P.hoistedNames.Nodup) (θ : Leaves)
    (req : Request) : LeavesAt θ (P.augmentRequest θ req).context 0 P.leafList := by
  intro i l hl
  have hi : i < P.leafList.length := by
    rcases Nat.lt_or_ge i P.leafList.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hl; cases hl
  have hli : P.leafList[i] = l := by rw [List.getElem?_eq_getElem hi] at hl; exact Option.some.inj hl
  simp only [PolicySet.augmentRequest, Nat.zero_add]
  rw [augmentContext_leaf hnd θ _ hi, hli]

/-- Outside the leaves' attributes, the augmented context is the request's. -/
theorem augmentRequest_other {P : PolicySet} (θ : Leaves) (req : Request) {a : Attr}
    (ha : a ∉ P.hoistedNames) : (P.augmentRequest θ req).context.find? a = req.context.find? a :=
  augmentContext_other θ req.context ha

/-- A policy set without leaves leaves the request as it is. -/
theorem augmentRequest_of_nil {P : PolicySet} (hL : P.leafList = []) (θ : Leaves)
    (req : Request) : P.augmentRequest θ req = req := by
  simp [PolicySet.augmentRequest, PolicySet.augmentContext, hL]

/-- A policy set without leaves has rules without leaves. -/
theorem leaves_of_nil {P : PolicySet} (hL : P.leafList = []) {q : Policy} (hq : q ∈ P.policies) :
    q.toExpr.leaves = [] := by
  unfold PolicySet.leafList at hL
  exact List.flatMap_eq_nil_iff.mp hL q hq

/-- **The decision is Cedar's on the lowering**, on the augmented request. -/
theorem isAuthorized_augmented {P : PolicySet} (hv : P.Valid) (θ : Leaves) (req : Request)
    (es : Entities) :
    Cedar.Spec.isAuthorized (P.augmentRequest θ req) es P.lowered = isAuthorized θ req es P.policies := by
  by_cases hL : P.leafList = []
  · -- Without leaves, the lowered rules are the rules, on the request itself.
    rw [augmentRequest_of_nil hL]
    exact isAuthorized_lower_self θ req es P.policies 0 (by
      have : P.policies.flatMap (·.toExpr.leaves) = [] := hL
      rw [this]
      intro i l h; cases h)
  · exact isAuthorized_lower θ req es (P.augmentRequest θ req).context P.hoistedNames
      (fun a ha => augmentRequest_other θ req ha) P.policies 0 (hv.readsContext hL)
      (augmentRequest_leaves hv.namesNodup θ req)

/-! ## The augmented environment -/

section

variable {P : PolicySet} {env : TypeEnv}

/-- The environment of the augmented schema that corresponds to the request's. -/
abbrev augmented (P : PolicySet) (env : TypeEnv) : TypeEnv :=
  augmentEnv P.actionSchema P.leafTypes env

theorem augmented_ets : (augmented P env).ets = env.ets := rfl

theorem augmented_contains (henv : env ∈ P.actionSchema.environments) (uid : EntityUID) :
    (augmented P env).acts.contains uid = env.acts.contains uid :=
  augmentEnv_contains henv uid

theorem augmentedSchema_eq (hv : P.Valid) :
    P.allAugmentedSchema = Schema.augment P.actionSchema P.leafTypes := by
  obtain ⟨H, hH⟩ := Option.isSome_iff_exists.mp hv.leafTypes
  unfold PolicySet.allAugmentedSchema
  rw [hH, (hoistedTypes_eq hH).1]
  rfl

/-- **The augmented request is an instance of the augmented request type**, when the request
is an instance of its own, and the leaves' values have their attributes' types. -/
theorem augmented_request (hv : P.Valid) (henv : env ∈ P.actionSchema.environments) {θ : Leaves}
    {req : Request} (hreq : InstanceOfRequestType req env)
    (htypes : ∀ i (hi : i < P.leafList.length),
      InstanceOfType env (θ.valueOf P.leafList[i]) ((P.leafType? P.leafList[i]).getD default)) :
    InstanceOfRequestType (P.augmentRequest θ req) (augmented P env) := by
  have hets := augmented_ets (P := P) (env := env)
  have hacts := augmented_contains henv
  obtain ⟨hp, ha, hr, hc⟩ := hreq
  refine ⟨instanceOfEntityType_congr hets hacts hp, ha, instanceOfEntityType_congr hets hacts hr, ?_⟩
  -- The context: the request's attributes, and the leaves'.
  obtain ⟨a, entry, pt, rt, hmem, _, _, rfl⟩ := mem_environments.mp henv
  have hfresh : ∀ k ∈ P.hoistedNames, entry.context.find? k = none :=
    fun k hk => hv.namesFresh (a, entry) hmem k hk
  have hnd := hv.namesNodup
  simp only [augmented, augmentEnv, PolicySet.augmentRequest] at hc ⊢
  cases hc with
  | instance_of_record _ _ h₁ h₂ h₃ =>
  -- Lookups in the two extended maps.
  have hctx_leaf : ∀ i (hi : i < P.leafList.length),
      (P.augmentContext θ req.context).find? (leafAttr i) = some (θ.valueOf P.leafList[i]) :=
    fun i hi => augmentContext_leaf hnd θ _ hi
  have hctx_other : ∀ k, k ∉ P.hoistedNames →
      (P.augmentContext θ req.context).find? k = req.context.find? k :=
    fun k hk => augmentContext_other θ _ hk
  have hty_leaf : ∀ i (hi : i < P.leafList.length),
      (Map.make (entry.context.toList ++ P.leafTypes)).find? (leafAttr i) =
        some (.required ((P.leafType? P.leafList[i]).getD default)) := fun i hi => by
    have hnone : entry.context.toList.find? (·.1 == leafAttr i) = none := by
      have := hfresh (leafAttr i) (mem_hoistedNames.mpr ⟨i, hi, rfl⟩)
      rw [map_find?_eq] at this
      cases h : entry.context.toList.find? (·.1 == leafAttr i) with
      | none => rfl
      | some _ => rw [h] at this; cases this
    rw [make_append_find?, hnone, Option.none_or,
      find?_of_mem (by rw [leafTypes_keys]; exact hnd) (mem_leafTypes hi)]
    rfl
  have hty_other : ∀ k, k ∉ P.hoistedNames →
      (Map.make (entry.context.toList ++ P.leafTypes)).find? k = entry.context.find? k := fun k hk => by
    rw [make_append_find?, find?_of_not_mem (by rw [leafTypes_keys]; exact hk) (L := P.leafTypes),
      map_find?_eq]
    simp
  refine .instance_of_record _ _ ?_ ?_ ?_
  · intro k hk
    by_cases hkh : k ∈ P.hoistedNames
    · obtain ⟨i, hi, rfl⟩ := mem_hoistedNames.mp hkh
      simp [Map.contains, hty_leaf i hi]
    · have : req.context.contains k := by
        simpa [Map.contains, hctx_other k hkh] using hk
      have := h₁ k this
      simpa [Map.contains, hty_other k hkh] using this
  · intro k v qty hv' hq
    by_cases hkh : k ∈ P.hoistedNames
    · obtain ⟨i, hi, rfl⟩ := mem_hoistedNames.mp hkh
      rw [hctx_leaf i hi, Option.some.injEq] at hv'
      rw [hty_leaf i hi, Option.some.injEq] at hq
      subst hv' hq
      exact instanceOfType_congr_contains hets hacts (htypes i hi)
    · rw [hctx_other k hkh] at hv'
      rw [hty_other k hkh] at hq
      exact instanceOfType_congr_contains hets hacts (h₂ k v qty hv' hq)
  · intro k qty hq hreqd
    by_cases hkh : k ∈ P.hoistedNames
    · obtain ⟨i, hi, rfl⟩ := mem_hoistedNames.mp hkh
      simp [Map.contains, hctx_leaf i hi]
    · rw [hty_other k hkh] at hq
      have := h₃ k qty hq hreqd
      simpa [Map.contains, hctx_other k hkh] using this

/-- **The entity store is an instance of the augmented environment** when it is an instance of
the request's. -/
theorem augmented_entities (henv : env ∈ P.actionSchema.environments) {es : Entities}
    (h : InstanceOfSchema es env) : InstanceOfSchema es (augmented P env) := by
  have hets := augmented_ets (P := P) (env := env)
  have hacts := augmented_contains henv
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := mem_environments.mp henv
  obtain ⟨hall, hactions⟩ := h
  refine ⟨fun uid data hd => ?_, fun uid entry' he => ?_⟩
  · rcases hall uid data hd with ⟨entry, hf, hvalid, hattrs, hanc, htags⟩ | ⟨hattrs, htags, entry, hf, hanc⟩
    · refine .inl ⟨entry, hf, hvalid, instanceOfType_congr_contains hets hacts hattrs, hanc, ?_⟩
      unfold Cedar.Thm.InstanceOfEntityTags at htags ⊢
      split at htags
      · exact fun v hv' => instanceOfType_congr_contains hets hacts (htags v hv')
      · exact htags
    · refine .inr ⟨hattrs, htags, augmentEntry P.leafTypes entry, ?_, hanc⟩
      exact Map.find?_mapOnValues_some _ hf
  · obtain ⟨entry, hf, _⟩ := Map.find?_mapOnValues_some' _ he
    exact hactions uid entry hf

/-- The augmented environment is well-formed, since validity makes the augmented schema so. -/
theorem augmented_wf (hv : P.Valid) (henv : env ∈ P.actionSchema.environments) :
    (augmented P env).WellFormed := by
  have hwf := hv.toAll.wellFormed
  rw [augmentedSchema_eq hv] at hwf
  exact Cedar.Thm.env_validate_well_formed_is_sound
    (List.forM_ok_implies_all_ok _ _ hwf _ (augmentEnv_mem henv))

end

/-! ## Soundness -/

/-- Dogwood's evaluator gives an expression a `Bool`, or one of the runtime errors Cedar's
validation cannot rule out. -/
def EvaluatesToBool (θ : Leaves) (x : Expr) (req : Request) (es : Entities) : Prop :=
  ∃ b : Bool, evaluate θ x req es = .error .entityDoesNotExist ∨
    evaluate θ x req es = .error .extensionError ∨
    evaluate θ x req es = .error .arithBoundsError ∨ evaluate θ x req es = .ok (.prim (.bool b))

theorem mem_providerCalls {ps : Policies} {c : Provider.Call} :
    c ∈ ps.providerCalls ↔ Sum.inr c ∈ ps.flatMap (·.toExpr.leaves) := by
  simp only [Policies.providerCalls, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, l, hl, hc⟩
    cases l with
    | inl _ => cases hc
    | inr c' => cases hc; exact ⟨p, hp, hl⟩
  · rintro ⟨p, hp, hl⟩
    exact ⟨p, hp, .inr c, hl, rfl⟩

/-- Each rule of the policy set is lowered, among the lowered rules, from the index of its first
leaf. -/
theorem lowered_of_mem : (ps : Policies) → (k : Nat) → ∀ p ∈ ps, ∃ k',
    (p.lowerFrom k').1 ∈ (Policies.lowerFrom k ps).1 ∧
    ∀ (θ : Leaves) (ctx : Map Attr Value), LeavesAt θ ctx k (ps.flatMap (·.toExpr.leaves)) →
      LeavesAt θ ctx k' p.toExpr.leaves
  | [], _, _, hp => by cases hp
  | q :: ps, k, p, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨k, by simp [Policies.lowerFrom], fun θ ctx hl => by
        simp only [List.flatMap_cons] at hl
        exact hl.left⟩
    · obtain ⟨k', hmem, hl'⟩ := lowered_of_mem ps (q.lowerFrom k).2 p hp
      refine ⟨k', by simp [Policies.lowerFrom, hmem], fun θ ctx hl => hl' θ ctx ?_⟩
      simp only [List.flatMap_cons] at hl
      rw [policy_lowerFrom_snd]
      exact hl.right

/-- **Soundness of the Cedar part.** At a decision every check of which passes, under any
reading, every lowered rule of a valid policy set evaluates, on the augmented request and the
decision's entity store, to a `Bool` or one of the runtime errors validation cannot rule out; so
does every rule, under Dogwood's evaluator; and the decision's response is Cedar's on the
lowered rules. -/
theorem cedar_sound {P : PolicySet} (hv : P.Valid) {ι : ImplChoices} {ω : Provider.Providers}
    {σ : Trace} {n : Nat} {p : TimePoint} {pr rs : EntityUID}
    (ha : P.Admits P.policies ω p pr rs) :
    let θ := P.leaves ι ω σ n p.event
    let req := p.event.request pr rs
    let es := P.decisionEntities p.event
    (∀ q ∈ P.lowered, ∃ b : Bool,
      Cedar.Thm.EvaluatesTo q.toExpr (P.augmentRequest θ req) es (.prim (.bool b))) ∧
    (∀ q ∈ P.policies, EvaluatesToBool θ q.toExpr req es) ∧
    Cedar.Spec.isAuthorized (P.augmentRequest θ req) es P.lowered = isAuthorized θ req es P.policies := by
  intro θ req es
  -- The request's environment.
  obtain ⟨env, henv, hreq⟩ := request_instance ha.request
  -- The store is an instance of every environment.
  have hes : InstanceOfSchema es env := by
    have := ha.entities
    unfold succeeds at this
    split at this
    · rename_i hok
      have := List.forM_ok_implies_all_ok _ _ hok env henv
      unfold Cedar.Validation.entitiesMatchEnvironment at this
      exact Cedar.Thm.instance_of_schema_refl this
    · cases this
  -- The leaves' values have their attributes' types.
  have hA : env.ets = P.actionSchema.ets ∧ env.acts = P.actionSchema.acts := by
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := mem_environments.mp henv
    exact ⟨rfl, rfl⟩
  have htypes : ∀ i (hi : i < P.leafList.length),
      InstanceOfType env (θ.valueOf P.leafList[i]) ((P.leafType? P.leafList[i]).getD default) := by
    intro i hi
    have hmem : P.leafList[i] ∈ P.leafList := List.getElem_mem hi
    generalize P.leafList[i] = l at hmem ⊢
    cases l with
    | inl φ =>
      exact .instance_of_bool _ _ (by
        cases θ.temporal φ <;> simp [Cedar.Thm.InstanceOfBoolType])
    | inr c =>
      have hc : c ∈ P.policies.providerCalls := mem_providerCalls.mpr hmem
      have hnf := ha.providers
      have hconf := ha.outputs
      unfold Policies.providersFail at hnf
      unfold PolicySet.providerOutputsConform at hconf
      have hne := List.any_eq_false.mp hnf c hc
      have hco := List.all_eq_true.mp hconf c hc
      simp only [Leaves.valueOf, θ, PolicySet.leaves, PolicySet.leafType?]
      cases hω : ω (c.resolve p.event) with
      | error => rw [hω] at hne; simp [Provider.Output.isError] at hne
      | value v =>
        rw [hω] at hco
        simp only at hco
        cases hty : c.outputType? P.providerDecls with
        | none => rw [hty] at hco; cases hco
        | some ty =>
          rw [hty] at hco
          have : Provider.Output.Conforms P.actionSchema ty (.value v) := of_decide_eq_true hco
          have hinst := Cedar.Thm.instance_of_type_refl
            (env := ⟨P.actionSchema.ets, P.actionSchema.acts, default⟩) this
          simp only [Provider.Output.leafValue, Option.getD_some]
          exact instanceOfType_congr_contains
            (env := ⟨P.actionSchema.ets, P.actionSchema.acts, default⟩)
            (by rw [hA.1]) (by intro uid; rw [hA.2]) hinst
  -- The augmented request and store are instances of the augmented environment.
  have hinst : ∃ env' ∈ P.allAugmentedSchema.environments,
      InstanceOfWellFormedEnvironment (P.augmentRequest θ req) es env' := by
    refine ⟨augmented P env, by rw [augmentedSchema_eq hv]; exact augmentEnv_mem henv,
      augmented_wf hv henv, augmented_request hv henv hreq htypes, augmented_entities henv hes⟩
  -- Cedar's soundness, rule by rule.
  have hlow : ∀ q ∈ P.lowered, ∃ b : Bool,
      Cedar.Thm.EvaluatesTo q.toExpr (P.augmentRequest θ req) es (.prim (.bool b)) := by
    intro q hq
    have htc := List.forM_ok_implies_all_ok _ _ hv.toAll.cedar q hq
    exact Cedar.Thm.typecheck_policy_with_environments_is_sound q _ _ _ hinst htc
  refine ⟨hlow, fun q hq => ?_, isAuthorized_augmented hv θ req es⟩
  -- A rule evaluates as its lowering.
  obtain ⟨k, hmem, hleaves⟩ := lowered_of_mem P.policies 0 q hq
  have heval : Cedar.Spec.evaluate (q.lowerFrom k).1.toExpr (P.augmentRequest θ req) es =
      evaluate θ q.toExpr req es := by
    by_cases hL : P.leafList = []
    · rw [augmentRequest_of_nil hL]
      exact evaluate_policy_lower_self θ req es q k (by
        rw [leaves_of_nil hL hq]; intro i l h; cases h)
    · have := evaluate_policy_lower θ req es (P.augmentRequest θ req).context P.hoistedNames
        (fun a ha' => augmentRequest_other θ req ha') q k (hv.readsContext hL q hq)
        (hleaves θ _ (augmentRequest_leaves hv.namesNodup θ req))
      exact this
  obtain ⟨b, hb⟩ := hlow _ hmem
  refine ⟨b, ?_⟩
  simpa [Cedar.Thm.EvaluatesTo, heval] using hb

/-! ## The soundness theorem -/

/-- **Soundness.** For a valid policy set, at a decision every check of which passes, over a
trace whose events conform:

1. **readings** — the outcome under any reading fails closed for a temporal error, or is the
   outcome under every completion of the reading (`authorize_dichotomy`), and every completion is
   total;
2. **the Cedar part** — under every total reading, every lowered rule evaluates, on the augmented
   request, to a `Bool` or a runtime error, so does every rule under Dogwood's evaluator, and the
   response is Cedar's on the lowered rules (`cedar_sound`);
3. **the temporal part** — under every total reading, every temporal leaf, in every environment
   its rule admits of which the decision event is an instance, when the event supplies the scope
   entities the leaf reads, at a position whose facts hold, is sound (`leaves_sound`): every
   comparison it reaches is two-valued, and every witness and row it uses is typed.
   `decision_sound` discharges the hypotheses on environments, scope entities, and facts from the
   decision's checks, for the leaves the response depends on. -/
theorem soundness {P : PolicySet} (hv : P.Valid) {ω : Provider.Providers} {σ : Trace} {n : Nat}
    {p : TimePoint} {pr rs : EntityUID} (_hσ : σ[n]? = some p)
    (ha : P.Admits P.policies ω p pr rs)
    (htr : ∀ (k : Nat) (q : TimePoint), σ[k]? = some q →
      q.event.Conforms P.actionSchema P.schema) :
    (∀ ι : ImplChoices, (P.authorize ι ω σ n = .failClosed .temporalError ∨
        ∀ ι', ι'.Completes ι → P.authorize ι ω σ n = P.authorize ι' ω σ n) ∧
      ∀ ι' : ImplChoices, ι'.Completes ι → ι'.Total) ∧
    (∀ ι : ImplChoices,
      let θ := P.leaves ι ω σ n p.event
      let req := p.event.request pr rs
      let es := P.decisionEntities p.event
      (∀ q ∈ P.lowered, ∃ b : Bool,
        Cedar.Thm.EvaluatesTo q.toExpr (P.augmentRequest θ req) es (.prim (.bool b))) ∧
      (∀ q ∈ P.policies, EvaluatesToBool θ q.toExpr req es) ∧
      Cedar.Spec.isAuthorized (P.augmentRequest θ req) es P.lowered =
        isAuthorized θ req es P.policies) ∧
    (∀ ι : ImplChoices, ι.Total → ∀ q ∈ P.policies, ∀ φ F, (.inl φ, F) ∈ q.toExpr.leafFacts [] →
      ∀ env ∈ P.envsOf q, p.event.InstanceOf env →
      (∀ r ∈ (φ.injectPins P.schema).scopeReads, p.event.Supplies env r) →
      (∀ g ∈ F, g.Holds p.event) →
      ∀ vis, (φ.injectPins P.schema).Sound ι P.tickRate σ p.event vis (P.typingCtx env F) [] Valuation.empty n) := by
  refine ⟨fun ι => ⟨authorize_dichotomy, fun ι' hc => hc.total⟩, fun ι => cedar_sound hv ha,
    fun ι hι q hq φ F hφ env henv he hsup hf vis =>
      leaves_sound hv hι htr n hq hφ henv he hsup hf vis⟩

/-- **No allow is caused by an ill-typed value.** An allowed decision of a valid policy set over
a trace whose events conform is the allow of every completion of the reading, at a decision every
check of which passes; under each, every rule evaluates to a `Bool` or a runtime error, never a
type error, and the response is Cedar's on the lowered rules. -/
theorem allow_sound {P : PolicySet} (hv : P.Valid) {ι : ImplChoices} {ω : Provider.Providers}
    {σ : Trace} {n : Nat} (h : (P.authorize ι ω σ n).decision? = some .allow) :
    ∃ p pr rs, σ[n]? = some p ∧ P.Admits P.policies ω p pr rs ∧ ∀ ι', ι'.Completes ι →
      (isAuthorized (P.leaves ι' ω σ n p.event) (p.event.request pr rs)
          (P.decisionEntities p.event) P.policies).decision = .allow ∧
      (∀ q ∈ P.policies, EvaluatesToBool (P.leaves ι' ω σ n p.event) q.toExpr
        (p.event.request pr rs) (P.decisionEntities p.event)) := by
  obtain ⟨p, pr, rs, r, hσ, ha, hr, hd⟩ := decideWith_decision?_allow h
  refine ⟨p, pr, rs, hσ, ha, fun ι' hc => ⟨?_, (cedar_sound (ι := ι') hv ha).2.1⟩⟩
  rw [supervaluate_eq_some_iff.mp hr ι' hc]
  exact hd

end Dogwood.Thm
