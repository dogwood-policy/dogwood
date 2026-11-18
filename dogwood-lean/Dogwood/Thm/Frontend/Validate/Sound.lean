import Dogwood.Thm.Frontend.Validate.Projection
import Dogwood.Thm.Frontend.Validate.Events
import Dogwood.Thm.Frontend.Validate.Schema
import Dogwood.Thm.Frontend.Validate.Typing
import Dogwood.Thm.Frontend.Validate.Monitor
import Dogwood.Thm.Frontend.Validate.Provider
import Dogwood.Thm.SafetyDecide
import Dogwood.Thm.Frontend.Validate.CedarRename

/-!
# The frontend's validator is sound with respect to `PolicySet.Valid`

`validate_sound`: if the frontend's earlier stages accepted a policy set, with the guarantees they
give of the lowered set (`Assumptions`), Cedar's schema construction accepted the augmented
schema, and the frontend's validator (`Dogwood.Frontend.Validate.validate`, a port of the crate's
`Validator::validate`) reports no error, then the specification's projection of the lowered set
(`Lowered.toConformance`) is valid (`Dogwood.Spec.PolicySet.Valid`).

The proof takes each clause of validity in turn:

* **the leaves' types and names**: every leaf of the projection is a read the crate hoisted
  (`leafList_eq`), a provider leaf of a declared provider (`provider_read`); the specification's
  names are distinct (`leafAttr_inj`) and no action declares one (`specActionSchema_fresh`);
* **context reads**: the crate's context-read check gives `Expr.ReadsContext` on the put-back rules
  (`readsContext_putBack`);
* **the Cedar part**: the specification's lowering is the crate's with each hoisted read renamed
  (`lowered_eq`), and the specification's schema augmented at every action relates to the
  crate's as the renaming needs (`ctxRel_projected`), so Cedar's validator accepts it
  (`validate_renameHoisted`); without leaves, the two are the same; that schema is well-formed
  (`augment_wellFormed`), has no enumerated ancestor when the crate's schema check finds none
  (`augment_standardAncestors`), and, with a rule, declares no name `external` when Cedar's
  validator reports nothing (`projected_complete`); so the projection is valid against the
  all-action schema (`PolicySet.ValidAll`), which is validity (`Dogwood.Thm.valid_iff_validAll`);
* **the temporal part**: each temporal leaf of the projection is a leaf the port checked, at a
  position whose facts the port computed (`temporal_position`), in an environment the port checked
  it in (`leafEnv`), seen alike (`envView_of_mem`, `events_agree`); so it is well-typed
  (`leaf_wellTyped`), monitors time (`checkTpDependence_eq_nil_iff`), and is safe by the parse-time
  checks;
* **the provider part**: each provider leaf is declared and typed (`provider_sound`).
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.Validate
open Dogwood.Spec (Expr Leaf leafAttr PolicySet)
open Dogwood.Spec.Temporal (Formula Guard TypingCtx)
open Cedar.Validation (CedarType Schema ActionSchemaEntry RecordType QualifiedType TypeEnv)
open Cedar.Data (Map)

/-! ## What the port reports -/

theorem all_warning_nil {xs : List Conformance.CrateFinding} (h : ∀ f ∈ xs, f.warning = false)
    (hacc : ∀ f ∈ xs, f.warning = true) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons x _ => have := h x (by simp); rw [hacc x (by simp)] at this; cases this

theorem finding_warning (code m : String) : (finding code m).warning = false := rfl

/-- **The port accepts**: each of its parts reports nothing. -/
theorem validate_parts {l : Lowered} {fs : List Conformance.CrateFinding}
    (hv : validate l = .ok fs) (hacc : ∀ f ∈ fs, f.warning = true) :
    ∃ leaves, leafFormulas l = .ok leaves ∧ cedarFindings l = [] ∧ contextFindings l = [] ∧
      (∀ x ∈ leaves, leafFindings (leafCtx l (loweredFacts l) x.1) x.2 = []) ∧
      (∀ g ∈ l.providers, providerLeafFindings l.schema g = []) := by
  unfold validate at hv
  cases hL : leafFormulas l with
  | error e => rw [hL] at hv; cases hv
  | ok leaves =>
    rw [hL] at hv
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hv
    subst hv
    have sub : ∀ (xs : List Conformance.CrateFinding), (∀ f ∈ xs, f.warning = false) →
        (∀ f ∈ xs, f.warning = true) → xs = [] := fun xs hw hm => all_warning_nil hw hm
    refine ⟨leaves, rfl, ?_, ?_, ?_, ?_⟩
    · apply sub
      · intro f hf; unfold cedarFindings at hf; split at hf
        · cases hf
        · split at hf
          · split at hf
            · cases hf
            · rcases List.mem_cons.mp hf with hf | hf
              · subst hf; rfl
              · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hf; rfl
          · unfold incompleteFindings at hf
            obtain ⟨_, _, rfl⟩ := List.mem_map.mp hf; rfl
      · intro f hf; exact hacc f (by simp [hf])
    · apply sub
      · intro f hf; unfold contextFindings at hf
        obtain ⟨⟨w, a⟩, _, hx⟩ := List.mem_filterMap.mp hf
        cases w <;> cases hb : hasLeaves l <;> simp only [hb] at hx <;> simp at hx <;> subst hx <;> rfl
      · intro f hf; exact hacc f (by simp [hf])
    · intro x hx
      have := sub ((leafFindings (leafCtx l (loweredFacts l) x.1) x.2).map (finding "temporal"))
        (fun f hf => by obtain ⟨m, _, rfl⟩ := List.mem_map.mp hf; rfl)
        (fun f hf => hacc f (by
          simp only [List.mem_append, List.mem_flatMap]
          exact Or.inl (Or.inl (Or.inr ⟨x, hx, hf⟩))))
      simpa using this
    · intro g hg
      have := sub ((providerLeafFindings l.schema g).map (finding "provider"))
        (fun f hf => by obtain ⟨m, _, rfl⟩ := List.mem_map.mp hf; rfl)
        (fun f hf => hacc f (by
          simp only [List.mem_append, List.mem_flatMap]
          exact Or.inl (Or.inr ⟨g, hg, hf⟩)))
      simpa using this

/-- No schema finding of an accepted set. -/
theorem validate_schema {l : Lowered} {fs : List Conformance.CrateFinding}
    (hv : validate l = .ok fs) (hacc : ∀ f ∈ fs, f.warning = true) : schemaFindings l = [] := by
  unfold validate at hv
  cases hL : leafFormulas l with
  | error e => rw [hL] at hv; cases hv
  | ok leaves =>
    rw [hL] at hv
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hv
    subst hv
    apply all_warning_nil
    · intro f hf
      unfold schemaFindings at hf
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hf
      rfl
    · intro f hf; exact hacc f (by simp [hf])

/-! ## What the earlier stages guarantee -/

/-- **What the frontend's earlier stages guarantee of a lowered set**, as the validator's soundness
takes it: each a property of the lowered set the stage guarantees, decided by
`Dogwood.Frontend.Validate.assumptions`. -/
structure Assumptions (l : Lowered) : Prop where
  /-- The parse-time checks (`extension/temporal/check.rs`) passed on every leaf. -/
  parse : leavesParseChecked l = true
  /-- No leaf has a bare `context` term (the temporal grammar has none). -/
  noEmptyContext : leavesNoEmptyContext l = true
  /-- Lowering read each leaf once, in its own rule, under a reserved name. -/
  names : namesOnce l = true
  /-- Each leaf's target actions and narrowing admit every environment its rule admits. -/
  scopes : scopesCovered l = true
  /-- The projection's provider declarations are the crate's, as the augmented schema types them. -/
  providerTypes : providerTypesAgree l = true
  /-- Each provider leaf's type is well-formed in the augmented schema. -/
  providerWellFormed : providerTypesWellFormed l = true
  /-- The augmented schema types each temporal leaf's attribute `Bool`. -/
  temporalBool : temporalAttrsBool l = true
  /-- Derivation splices fields that resolve, and pins declared fields. -/
  derived : derivedFacts l = true
  /-- The lowered rules are Cedar's. -/
  leafless : policiesLeafless l = true
  /-- No name of the specification's leaf attributes' shape is declared or read. -/
  specNames : specNamesAbsent l = true
  /-- Every entity type an action admits is declared. -/
  appliesTo : appliesToDeclared l = true
  /-- With a provider leaf, no action's `providers` attribute is an entity. -/
  providersNotEntity : providersNotEntity l = true

theorem mem_zip_of_getElem? {α β : Type} : {l₁ : List α} → {l₂ : List β} → {i : Nat} → {a : α} →
    {b : β} → l₁[i]? = some a → l₂[i]? = some b → (a, b) ∈ l₁.zip l₂
  | [], _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h
  | x :: xs, y :: ys, 0, a, b, h₁, h₂ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁ h₂; subst h₁ h₂; simp
  | x :: xs, y :: ys, i + 1, a, b, h₁, h₂ => by
    simp only [List.getElem?_cons_succ] at h₁ h₂
    simp only [List.zip_cons_cons, List.mem_cons]
    exact Or.inr (mem_zip_of_getElem? h₁ h₂)

/-- Lowering's names, unfolded. -/
theorem namesOnce_spec {l : Lowered} (h : namesOnce l = true) :
    l.temporalRules.length = l.temporal.length ∧ l.providerRules.length = l.providers.length ∧
      (ruleReads l).flatten.Nodup ∧
      (∀ (j : Nat) (f : TemporalField) (k : Nat), l.temporal[j]? = some f →
        l.temporalRules[j]? = some k → (true, f.id) ∈ ((ruleReads l)[k]?).getD []) ∧
      (∀ (j : Nat) (g : LoweredProviderField) (k : Nat), l.providers[j]? = some g →
        l.providerRules[j]? = some k → (false, g.id) ∈ ((ruleReads l)[k]?).getD []) ∧
      (∀ f ∈ l.temporal, isHoistedName f.id = true ∧ f.id ≠ "providers") := by
  unfold namesOnce at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩ := h
  refine ⟨h₁, h₂, h₃, fun j f k hf hk => ?_, fun j g k hg hk => ?_, fun f hf => ?_⟩
  · have := h₄ (f, k) (mem_zip_of_getElem? hf hk)
    simpa using this
  · have := h₅ (g, k) (mem_zip_of_getElem? hg hk)
    simpa using this
  · have := h₆ f hf
    simp only [bne_iff_ne, ne_eq] at this
    exact this

/-- Every hoisted read of the lowered set, in order. -/
def allReads (l : Lowered) : List (Bool × String) := (ruleReads l).flatten

/-- The specification's name of each hoisted read: the leaf attribute of its position. -/
def specRen (l : Lowered) (b : Bool) (a : String) : Cedar.Spec.Attr := leafAttr ((allReads l).idxOf (b, a))

/-! ## The projection's leaves and lowering -/

section

variable {l : Lowered} {T : List (String × Formula)} {Pr : List (String × Dogwood.Spec.Provider.Call)}

theorem tids_eq (hT : l.leafFormulas = .ok T) : T.map Prod.fst = l.temporal.map (·.id) :=
  keys_of_forall₂ (leafFormulas_forall₂ hT) (fun _ _ h => h.1)

theorem pids_eq (hPr : l.providerCalls = .ok Pr) : Pr.map Prod.fst = l.providers.map (·.id) :=
  keys_of_forall₂ (providerCalls_forall₂ hPr) (fun _ _ h => h.1)

theorem ruleReads_eq (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr) :
    ruleReads l = l.policies.map fun q => hoistedReads (T.map Prod.fst) (Pr.map Prod.fst) q.toExpr := by
  rw [tids_eq hT, pids_eq hPr]; rfl

theorem leafless_spec (h : policiesLeafless l = true) : ∀ q ∈ l.policies, q.toExpr.leaves = [] := by
  unfold policiesLeafless at h
  rw [List.all_eq_true] at h
  intro q hq; simpa using h q hq

/-- **The projection's leaves are the crate's hoisted reads**, in order. -/
theorem leafList_eq (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hl : policiesLeafless l = true) (D : Dogwood.Spec.Provider.Declarations) (sigs) (A) (mw)
    (mh xt xa) :
    ({ policies := l.policies.map (putBackPolicy T Pr), schema := sigs, actionSchema := A,
       maxWindow := mw, maxHorizon := mh, providerDecls := D, externalTypes := xt,
       externalActions := xa } :
      PolicySet).leafList = (allReads l).map (readLeaf T Pr) := by
  unfold PolicySet.leafList allReads
  rw [ruleReads_eq hT hPr]
  have hl' := leafless_spec hl
  simp only [List.flatMap_map, List.map_flatten, List.map_map]
  generalize l.policies = qs at hl' ⊢
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.flatMap_cons, List.map_cons, List.flatten_cons, Function.comp]
    rw [putBackPolicy_toExpr, leaves_putBack _ _ _ (hl' q (by simp)),
      ih (fun q' h => hl' q' (by simp [h]))]

/-- **The projection's lowering is the crate's, with the hoisted reads renamed** to the
specification's leaf attributes. -/
theorem lowered_eq (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hl : policiesLeafless l = true) (hn : (allReads l).Nodup) :
    (Dogwood.Spec.Policies.lowerFrom 0 (l.policies.map (putBackPolicy T Pr))).1 =
      (cedarPolicies l).map (renamePolicy (T.map Prod.fst) (Pr.map Prod.fst) (specRen l)) := by
  unfold cedarPolicies
  apply policies_lowerFrom_putBack (specRen l) l.policies 0 (leafless_spec hl)
  intro i r hr
  rw [Nat.zero_add]
  unfold specRen
  congr 1
  apply idxOf_of_getElem? hn
  unfold allReads
  rw [ruleReads_eq hT hPr]
  simpa [List.flatMap, Function.comp_def] using hr

theorem mem_temporalIds {L : List (Bool × String)} {a : String} : a ∈ temporalIds L ↔ (true, a) ∈ L := by
  unfold temporalIds
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨⟨b, a'⟩, h, hb⟩
    cases b <;> simp at hb
    subst hb; exact h
  · intro h; exact ⟨(true, a), h, rfl⟩

theorem temporalIds_nodup : {L : List (Bool × String)} → L.Nodup → (temporalIds L).Nodup
  | [], _ => List.nodup_nil
  | (b, a) :: L, h => by
    rw [List.nodup_cons] at h
    cases b with
    | false => simpa [temporalIds] using temporalIds_nodup h.2
    | true =>
      have : temporalIds ((true, a) :: L) = a :: temporalIds L := by simp [temporalIds]
      rw [this, List.nodup_cons]
      exact ⟨fun ha => h.1 (mem_temporalIds.mp ha), temporalIds_nodup h.2⟩

theorem getElem?_of_mem' {α : Type} {L : List α} {x : α} (h : x ∈ L) : ∃ i : Nat, L[i]? = some x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨i, by simp [hi]⟩

theorem nodup_of_getElem?_flatten {α : Type} {L : List (List α)} (hn : L.flatten.Nodup) {k : Nat}
    {xs : List α} (h : L[k]? = some xs) : xs.Nodup :=
  List.Nodup.sublist (List.sublist_flatten_of_mem (List.mem_of_getElem? h)) hn

/-- **Each temporal leaf of the projection is a temporal leaf of the lowered set**, read in its own
rule, at a position whose facts, as the port computes them, are among the specification's outside
reserved heads. -/
theorem temporal_position (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hl : policiesLeafless l = true) (hn : namesOnce l = true) {p : Dogwood.Spec.Policy}
    (hp : p ∈ l.policies.map (putBackPolicy T Pr)) {φ : Formula} {F : List Guard}
    (hm : (.inl φ, F) ∈ p.toExpr.leafFacts []) :
    ∃ (j : Nat) (f : TemporalField) (k : Nat) (q : Dogwood.Spec.Policy),
      l.temporal[j]? = some f ∧ l.temporalRules[j]? = some k ∧ l.policies[k]? = some q ∧
      p = putBackPolicy T Pr q ∧ f.condition.condition.toFormula = .ok φ ∧
      ∃ G, (loweredFacts l).lookup f.id = some G ∧ NrSub G F := by
  obtain ⟨hlen, -, hnd, htr, -, hhoist⟩ := namesOnce_spec hn
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  obtain ⟨k, hk⟩ := getElem?_of_mem' hq
  have hql := leafless_spec hl q hq
  rw [putBackPolicy_toExpr] at hm
  have hTh : ∀ a ∈ T.map Prod.fst, isHoistedName a = true := by
    rw [tids_eq hT]; intro a ha
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
    exact (hhoist f hf).1
  have htp : (T.map Prod.fst).contains "providers" = false := by
    rw [tids_eq hT]
    simp only [List.contains_eq_any_beq, List.any_map, Bool.eq_false_iff, ne_eq, List.any_eq_true,
      not_exists, not_and, Function.comp, beq_iff_eq]
    intro f hf h; exact (hhoist f hf).2 h.symm
  obtain ⟨a, G, ha, hφ, hG, hsub⟩ := leafFacts_putBack_temporal hTh q.toExpr [] [] hql
    (fun _ h _ => by cases h) φ F hm
  obtain ⟨φ', hφ'⟩ := lookup_eq_some_of_contains ha
  rw [hφ', Option.getD_some] at hφ
  subst hφ
  obtain ⟨i, f, hfi, -, hR⟩ := exists_of_mem_forall₂ (leafFormulas_forall₂ hT) (mem_of_lookup hφ')
  obtain ⟨hfa, hfφ⟩ := hR
  simp only at hfa
  -- the field's rule is the rule that reads it
  have hreadk : (true, a) ∈ ((ruleReads l)[k]?).getD [] := by
    have hkeys := leafFactsW_keys (T.map Prod.fst) (Pr.map Prod.fst) htp [] q.toExpr
    have : a ∈ (leafFactsW ((T.map Prod.fst).contains ·) [] q.toExpr).map Prod.fst :=
      List.mem_map.mpr ⟨(a, G), hG, rfl⟩
    rw [hkeys, mem_temporalIds] at this
    rw [ruleReads_eq hT hPr]
    simpa [hk] using this
  have hi : i < l.temporalRules.length := by
    rw [hlen]; exact (List.getElem?_eq_some_iff.mp hfi).1
  obtain ⟨k', hk'⟩ : ∃ k', l.temporalRules[i]? = some k' := ⟨_, List.getElem?_eq_getElem hi⟩
  have hread' := htr i f k' hfi hk'
  rw [← hfa] at hread'
  have hrk : (ruleReads l)[k]? = some (hoistedReads (l.temporal.map (·.id)) (l.providers.map (·.id)) q.toExpr) := by
    simp [ruleReads, hk]
  have hk'len : k' < (ruleReads l).length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hread'
    cases hread'
  obtain ⟨xs', hxs'⟩ : ∃ xs', (ruleReads l)[k']? = some xs' := ⟨_, List.getElem?_eq_getElem hk'len⟩
  rw [hrk] at hreadk; rw [hxs'] at hread'
  simp only [Option.getD_some] at hreadk hread'
  have hkk : k' = k := index_unique_of_nodup_flatten hnd hxs' hrk hread' hreadk
  subst hkk
  refine ⟨i, f, k', q, hfi, hk', hk, rfl, hfφ, G, ?_, hsub⟩
  rw [← hfa]
  -- the port's facts for the leaf
  have hWk : leafFactsW ((l.temporal.map (·.id)).contains ·) [] (Dogwood.Spec.Conditions.toExpr q.condition) =
      leafFactsW ((T.map Prod.fst).contains ·) [] q.toExpr := by
    rw [leafFactsW_policy, tids_eq hT]
  apply loweredFacts_lookup hk (List.mem_of_getElem? hk')
  · unfold ruleFacts
    rw [hWk]
    apply mergeFacts_lookup_once _ hG
    rw [leafFactsW_keys (T.map Prod.fst) (Pr.map Prod.fst) htp []]
    apply temporalIds_nodup
    rw [tids_eq hT, pids_eq hPr]
    exact nodup_of_getElem?_flatten hnd hrk
  · intro k'' q'' hne hq''
    unfold ruleFacts
    apply mergeFacts_lookup_not_mem
    rw [← leafFactsW_policy, ← tids_eq hT,
      leafFactsW_keys (T.map Prod.fst) (Pr.map Prod.fst) htp [] q''.toExpr, mem_temporalIds]
    intro hin
    have hr'' : (ruleReads l)[k'']? = some (hoistedReads (l.temporal.map (·.id)) (l.providers.map (·.id)) q''.toExpr) := by
      simp [ruleReads, hq'']
    rw [tids_eq hT, pids_eq hPr] at hin
    exact hne (index_unique_of_nodup_flatten hnd hr'' hrk hin hreadk)

mutual

theorem mem_hoistedReads (tids pids : List String) : (x : Expr) → ∀ {b : Bool} {a : String},
    (b, a) ∈ hoistedReads tids pids x → (if b then tids else pids).contains a = true
  | .getAttr e a', b, a, h => by
    simp only [hoistedReads] at h
    split at h
    · rename_i hc; simp only [List.mem_singleton, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true] at hc; simpa using hc.2
    · split at h
      · rename_i _ hc; simp only [List.mem_singleton, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        simp only [Bool.and_eq_true] at hc; simpa using hc.2
      · exact mem_hoistedReads tids pids e h
  | .lit _, _, _, h | .var _, _, _, h | .temporal _, _, _, h | .provider _, _, _, h => by
    simp [hoistedReads] at h
  | .ite c t e, _, _, h => by
    simp only [hoistedReads, List.mem_append] at h
    rcases h with (h | h) | h
    · exact mem_hoistedReads tids pids c h
    · exact mem_hoistedReads tids pids t h
    · exact mem_hoistedReads tids pids e h
  | .and x y, _, _, h | .or x y, _, _, h | .binaryApp _ x y, _, _, h => by
    simp only [hoistedReads, List.mem_append] at h
    rcases h with h | h
    · exact mem_hoistedReads tids pids x h
    · exact mem_hoistedReads tids pids y h
  | .unaryApp _ x, _, _, h | .hasAttr x _, _, _, h | .extHasAttr x _ _, _, _, h => by
    simp only [hoistedReads] at h; exact mem_hoistedReads tids pids x h
  | .set xs, _, _, h | .call _ xs, _, _, h => by
    simp only [hoistedReads] at h; exact mem_hoistedReadsList tids pids xs h
  | .record axs, _, _, h => by
    simp only [hoistedReads] at h; exact mem_hoistedReadsRecord tids pids axs h

theorem mem_hoistedReadsList (tids pids : List String) : (xs : List Expr) → ∀ {b : Bool} {a : String},
    (b, a) ∈ hoistedReadsList tids pids xs → (if b then tids else pids).contains a = true
  | [], _, _, h => by simp [hoistedReadsList] at h
  | x :: xs, _, _, h => by
    simp only [hoistedReadsList, List.mem_append] at h
    rcases h with h | h
    · exact mem_hoistedReads tids pids x h
    · exact mem_hoistedReadsList tids pids xs h

theorem mem_hoistedReadsRecord (tids pids : List String) : (axs : List (String × Expr)) →
    ∀ {b : Bool} {a : String}, (b, a) ∈ hoistedReadsRecord tids pids axs →
      (if b then tids else pids).contains a = true
  | [], _, _, h => by simp [hoistedReadsRecord] at h
  | (_, x) :: axs, _, _, h => by
    simp only [hoistedReadsRecord, List.mem_append] at h
    rcases h with h | h
    · exact mem_hoistedReads tids pids x h
    · exact mem_hoistedReadsRecord tids pids axs h

end

/-- **Each provider leaf of the projection is a provider leaf of the lowered set**, read in its own
rule. -/
theorem provider_position (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hl : policiesLeafless l = true) (hn : namesOnce l = true) {p : Dogwood.Spec.Policy}
    (hp : p ∈ l.policies.map (putBackPolicy T Pr)) {c : Dogwood.Spec.Provider.Call} {F : List Guard}
    (hm : (.inr c, F) ∈ p.toExpr.leafFacts []) :
    ∃ (j : Nat) (g : LoweredProviderField) (k : Nat) (q : Dogwood.Spec.Policy),
      l.providers[j]? = some g ∧ l.providerRules[j]? = some k ∧ l.policies[k]? = some q ∧
      p = putBackPolicy T Pr q ∧ g.toCall = .ok c := by
  obtain ⟨-, hlen, hnd, -, hpr, -⟩ := namesOnce_spec hn
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  obtain ⟨k, hk⟩ := getElem?_of_mem' hq
  have hql := leafless_spec hl q hq
  have hleaf : Sum.inr c ∈ (putBackPolicy T Pr q).toExpr.leaves := by
    rw [← Dogwood.Thm.leafFacts_fst []]; exact List.mem_map.mpr ⟨_, hm, rfl⟩
  rw [putBackPolicy_toExpr, leaves_putBack _ _ _ hql] at hleaf
  obtain ⟨⟨b, a⟩, hr, hrl⟩ := List.mem_map.mp hleaf
  cases b with
  | true => simp [readLeaf] at hrl
  | false =>
    simp only [readLeaf, Sum.inr.injEq] at hrl
    have hpa := mem_hoistedReads _ _ _ hr
    simp only [Bool.false_eq_true, if_false] at hpa
    obtain ⟨c', hc'⟩ := lookup_eq_some_of_contains hpa
    rw [hc', Option.getD_some] at hrl
    subst hrl
    obtain ⟨i, g, hgi, -, hR⟩ := exists_of_mem_forall₂ (providerCalls_forall₂ hPr) (mem_of_lookup hc')
    obtain ⟨hga, hgc⟩ := hR
    simp only at hga
    have hi : i < l.providerRules.length := by
      rw [hlen]; exact (List.getElem?_eq_some_iff.mp hgi).1
    obtain ⟨k', hk'⟩ : ∃ k', l.providerRules[i]? = some k' := ⟨_, List.getElem?_eq_getElem hi⟩
    have hread' := hpr i g k' hgi hk'
    rw [← hga] at hread'
    have hrk : (ruleReads l)[k]? = some (hoistedReads (l.temporal.map (·.id)) (l.providers.map (·.id)) q.toExpr) := by
      simp [ruleReads, hk]
    have hk'len : k' < (ruleReads l).length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hread'
      cases hread'
    obtain ⟨xs', hxs'⟩ : ∃ xs', (ruleReads l)[k']? = some xs' := ⟨_, List.getElem?_eq_getElem hk'len⟩
    rw [hxs'] at hread'
    simp only [Option.getD_some] at hread'
    have hreadk : (false, a) ∈ hoistedReads (l.temporal.map (·.id)) (l.providers.map (·.id)) q.toExpr := by
      rw [← tids_eq hT, ← pids_eq hPr]; exact hr
    have hkk : k' = k := index_unique_of_nodup_flatten hnd hxs' hrk hread' hreadk
    subst hkk
    exact ⟨i, g, k', q, hgi, hk', hk, rfl, hgc⟩

/-! ## Views of the projection's environments -/

theorem acts_wf (hwf : l.schema.validateWellFormed = .ok ()) (hne : l.schema.environments ≠ []) :
    Map.WellFormed l.schema.acts := by
  obtain ⟨env, -, hacts, hw⟩ := wellFormed_of_validate hwf hne
  rw [← hacts]; exact hw.2.1.1

theorem hoistedNames_reserved (hn : namesOnce l = true) : ∀ a ∈ l.hoistedNames, isHoistedName a = true := by
  obtain ⟨-, -, -, -, -, hh⟩ := namesOnce_spec hn
  intro a ha
  unfold Lowered.hoistedNames at ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha; exact (hh f hf).1
  · split at ha
    · cases ha
    · simp only [List.mem_singleton] at ha; subst ha; exact isHoistedName_providers

theorem find?_filter_keep {β : Type} {L : List (String × β)} {q : String × β → Bool} {x : String}
    (hq : ∀ y ∈ L, y.1 = x → q y = true) : (L.filter q).find? (·.1 == x) = L.find? (·.1 == x) := by
  induction L with
  | nil => rfl
  | cons y L ih =>
    have ih' := ih (fun z hz => hq z (by simp [hz]))
    by_cases hyx : y.1 = x
    · rw [List.filter_cons_of_pos (hq y (by simp) hyx)]
      simp [hyx]
    · by_cases hqy : q y = true
      · rw [List.filter_cons_of_pos hqy]
        simp [hyx, ih']
      · rw [List.filter_cons_of_neg hqy, ih']
        simp [hyx]

theorem dropContext_find? {drop : List String} (hd : ∀ a ∈ drop, isHoistedName a = true)
    (e : ActionSchemaEntry) {x : String} (hx : isHoistedName x = false) :
    (dropContext drop e).context.find? x = e.context.find? x := by
  simp only [dropContext]
  rw [Map.make_find?_eq_list_find?, find?_filter_keep, ← map_find?_eq]
  intro y _ hy
  simp only [Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  intro hc
  have := hd _ (mem_of_contains hc)
  rw [hy, hx] at this; cases this

/-- **A request environment of the projection's action schema is one of the augmented schema's**,
seen as the crate's validator sees it. -/
theorem envView_of_mem (hwf : l.schema.validateWellFormed = .ok ()) (hne : l.schema.environments ≠ [])
    (hn : namesOnce l = true) (happ : appliesToDeclared l = true) {env : TypeEnv}
    (henv : env ∈ (specActionSchema l).environments) :
    ∃ (a : Cedar.Spec.EntityUID) (e : ActionSchemaEntry) (pt rt : Cedar.Spec.EntityType),
      l.schema.acts.find? a = some e ∧ pt ∈ e.appliesToPrincipal.toList ∧
      rt ∈ e.appliesToResource.toList ∧ env.reqty.action = a ∧ env.reqty.principal = pt ∧
      env.reqty.resource = rt ∧
      ∀ C' : TypingCtx, C'.env = env → EnvView C' l.schema ⟨a, e, pt, rt⟩ := by
  obtain ⟨a, e, pt, rt, hmem, hpt, hrt, rfl⟩ := (mem_specEnvironments hwf hne).mp henv
  have hfind : l.schema.acts.find? a = some e := Map.mem_toList_find? (acts_wf hwf hne) hmem
  refine ⟨a, e, pt, rt, hfind, hpt, hrt, rfl, rfl, rfl, fun C' hC => ?_⟩
  obtain ⟨env', events, mw, F⟩ := C'
  simp only at hC
  subst hC
  unfold appliesToDeclared at happ
  rw [List.all_eq_true] at happ
  have hd := happ (a, e) hmem
  simp only [Bool.and_eq_true, List.all_eq_true] at hd
  refine ⟨rfl, rfl, rfl, fun x hx => dropContext_find? (hoistedNames_reserved hn) e hx, rfl,
    fun uid => Map.contains_mapOnValues _, ?_⟩
  intro r ety hety
  cases r with
  | principal => exact hd.1 ety hety
  | resource => exact hd.2 ety hety

/-! ## Unpacking the assumptions -/

theorem leaf_mem_leaves {leaves : List (TemporalField × Formula)} (hL : leafFormulas l = .ok leaves)
    {j : Nat} {f : TemporalField} {φ : Formula} (hf : l.temporal[j]? = some f)
    (hφ : f.condition.condition.toFormula = .ok φ) : (f, φ) ∈ leaves := by
  unfold leafFormulas at hL
  have h₂ := List.mapM_ok_iff_forall₂.mp hL
  have hm := List.mem_of_getElem? hf
  obtain ⟨x, hx, hfx⟩ := forall₂_mem_left h₂ hm
  rw [hφ] at hfx
  simp only [pure, Except.pure, Except.ok.injEq] at hfx
  rw [hfx]; exact hx

theorem parseChecked_of {hp : leavesParseChecked l = true} {f : TemporalField} (hf : f ∈ l.temporal)
    {φ : Formula} (hφ : f.condition.condition.toFormula = .ok φ) : parseChecked φ = true := by
  unfold leavesParseChecked at hp
  rw [List.all_eq_true] at hp
  have := hp f hf
  rw [hφ] at this
  exact this

theorem noEmptyContext_of {hp : leavesNoEmptyContext l = true} {f : TemporalField} (hf : f ∈ l.temporal)
    {φ : Formula} (hφ : f.condition.condition.toFormula = .ok φ) : noEmptyContextF φ = true := by
  unfold leavesNoEmptyContext at hp
  rw [List.all_eq_true] at hp
  have := hp f hf
  rw [hφ] at this
  exact this

theorem coversScope_temporal (hs : scopesCovered l = true) {j : Nat} {f : TemporalField} {k : Nat}
    {q : Dogwood.Spec.Policy} (hf : l.temporal[j]? = some f) (hk : l.temporalRules[j]? = some k)
    (hq : l.policies[k]? = some q) : coversScope l q f.targetActions f.principal f.resource = true := by
  unfold scopesCovered at hs
  simp only [Bool.and_eq_true, List.all_eq_true] at hs
  have := hs.1 (f, k) (mem_zip_of_getElem? hf hk)
  simp only [hq] at this
  exact this

theorem coversScope_provider (hs : scopesCovered l = true) {j : Nat} {g : LoweredProviderField} {k : Nat}
    {q : Dogwood.Spec.Policy} (hg : l.providers[j]? = some g) (hk : l.providerRules[j]? = some k)
    (hq : l.policies[k]? = some q) : coversScope l q g.targetActions g.principal g.resource = true := by
  unfold scopesCovered at hs
  simp only [Bool.and_eq_true, List.all_eq_true] at hs
  have := hs.2 (g, k) (mem_zip_of_getElem? hg hk)
  simp only [hq] at this
  exact this

/-- A rule's scope admits an environment of the projection: the leaf's target actions and
narrowing do. -/
theorem covered {q : Dogwood.Spec.Policy} {targets : List (String × String)} {pc rc : ScopeConstraint}
    (h : coversScope l q targets pc rc = true) {env : TypeEnv} (henv : env ∈ (specActionSchema l).environments)
    (had : q.admits (specActionSchema l) env = true) :
    (∃ x ∈ targets, actionUidOf x.1 x.2 = env.reqty.action) ∧
      constraintAdmits l.schema pc env.reqty.principal = true ∧
      constraintAdmits l.schema rc env.reqty.resource = true := by
  unfold coversScope at h
  rw [List.all_eq_true] at h
  have := h env henv
  simp only [had, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem specEnvs_ne {env : TypeEnv} (henv : env ∈ (specActionSchema l).environments) :
    l.schema.environments ≠ [] := by
  intro hnil
  have h := augment_environments_nil (H := []) hnil
  have := Dogwood.Thm.augmentEnv_mem (H := []) henv
  rw [h] at this; cases this

/-- **An environment the rule's scope admits is a request environment the crate's validator checks
the leaf in**, seen alike. -/
theorem leafEnv {targets : List (String × String)} {pc rc : ScopeConstraint} {q : Dogwood.Spec.Policy}
    (hwf : l.schema.validateWellFormed = .ok ()) (hn : namesOnce l = true)
    (happ : appliesToDeclared l = true) (hcov : coversScope l q targets pc rc = true)
    {env : TypeEnv} (henv : env ∈ (specActionSchema l).environments)
    (had : q.admits (specActionSchema l) env = true) :
    ∃ e : ReqEnv, (e.uid, e.entry) ∈ targets.filterMap (fun x => action? l.schema x.1 x.2) ∧
      e.principal ∈ admittedTypes l.schema e.entry .principal pc ∧
      e.resource ∈ admittedTypes l.schema e.entry .resource rc ∧
      ∀ C' : TypingCtx, C'.env = env → EnvView C' l.schema e := by
  have hne := specEnvs_ne henv
  obtain ⟨a, e, pt, rt, hfind, hpt, hrt, ha, hp, hr, hview⟩ := envView_of_mem hwf hne hn happ henv
  obtain ⟨⟨x, hx, hxa⟩, hpc, hrc⟩ := covered hcov henv had
  refine ⟨⟨a, e, pt, rt⟩, ?_, ?_, ?_, hview⟩
  · apply List.mem_filterMap.mpr
    refine ⟨x, hx, ?_⟩
    simp only [action?, hxa, ha, hfind, Option.map_some]
  · simp only [admittedTypes, List.mem_filter, appliesTo]
    exact ⟨hpt, by rw [← hp]; exact hpc⟩
  · simp only [admittedTypes, List.mem_filter, appliesTo]
    exact ⟨hrt, by rw [← hr]; exact hrc⟩

/-! ## Provider declarations -/

theorem sigEq_eq {a b : Dogwood.Spec.Provider.Signature} (h : sigEq a b = true) : a = b := by
  obtain ⟨fa, aa, oa, ma⟩ := a
  obtain ⟨fb, ab, ob, mb⟩ := b
  unfold sigEq at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩ := h
  subst h₁ h₂ h₃
  congr 1
  induction ma generalizing mb with
  | nil => cases mb with
    | nil => rfl
    | cons _ _ => simp at h₄
  | cons x ma ih =>
    cases mb with
    | nil => simp at h₄
    | cons y mb =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h₄
      have hxy := h₅ (x, y) (by simp)
      obtain ⟨⟨⟨hn, ha⟩, hi⟩, ho⟩ := hxy
      obtain ⟨_, _, _, _⟩ := x
      obtain ⟨_, _, _, _⟩ := y
      simp only at hn ha hi ho
      subst hn ha hi ho
      rw [ih mb (fun p hp => h₅ p (List.mem_cons_of_mem _ hp)) h₄]

theorem declaration_of_findings {S : Schema} {g : LoweredProviderField}
    (h : providerLeafFindings S g = []) : ∃ d, g.declaration = some d := by
  unfold providerLeafFindings at h
  cases hd : g.declaration with
  | none => rw [hd] at h; simp at h
  | some d => exact ⟨d, rfl⟩

theorem providerTypes_of (h : providerTypesAgree l = true) {g : LoweredProviderField} (hg : g ∈ l.providers)
    {d : ProviderDecls.ProviderDecl} (hd : g.declaration = some d) {c : Dogwood.Spec.Provider.Call}
    (hc : g.toCall = .ok c) :
    (providerDeclsToSpec l.declarations l.schema).1.find? c.function =
        some (crateSignature g.entityTypeNames c.function d) ∧
      ∀ uid e, (uid, e) ∈ l.schema.acts.toList → ∀ q R, e.context.find? "providers" = some q →
        q.getType = .record R → ∀ q', R.find? g.id = some q' → some q'.getType = crateOutputType g d := by
  unfold providerTypesAgree at h
  rw [List.all_eq_true] at h
  have := h g hg
  rw [hd, hc] at this
  simp only [Bool.and_eq_true, List.all_eq_true] at this
  obtain ⟨h₁, h₂⟩ := this
  refine ⟨?_, fun uid e he q R hq hR q' hq' => ?_⟩
  · split at h₁
    · rename_i sig hsig; rw [hsig, sigEq_eq h₁]
    · cases h₁
  · have := h₂ (uid, e) he
    simp only [hq, hR, hq', Option.all_some, beq_iff_eq] at this
    exact this

/-! ## The Cedar part -/

mutual

theorem renameHoisted_nil (ren : Bool → String → Cedar.Spec.Attr) :
    (x : Cedar.Spec.Expr) → renameHoisted [] [] ren x = x
  | .getAttr e a => by simp [renameHoisted, renameHoisted_nil ren e]
  | .lit _ | .var _ => rfl
  | .ite a b c => by simp [renameHoisted, renameHoisted_nil ren a, renameHoisted_nil ren b,
      renameHoisted_nil ren c]
  | .and a b | .or a b | .binaryApp _ a b => by
    simp [renameHoisted, renameHoisted_nil ren a, renameHoisted_nil ren b]
  | .unaryApp _ a | .hasAttr a _ | .extHasAttr a _ _ => by
    simp [renameHoisted, renameHoisted_nil ren a]
  | .set xs | .call _ xs => by simp [renameHoisted, renameHoistedList_nil ren xs]
  | .record axs => by simp [renameHoisted, renameHoistedRecord_nil ren axs]

theorem renameHoistedList_nil (ren : Bool → String → Cedar.Spec.Attr) :
    (xs : List Cedar.Spec.Expr) → renameHoistedList [] [] ren xs = xs
  | [] => rfl
  | x :: xs => by simp [renameHoistedList, renameHoisted_nil ren x, renameHoistedList_nil ren xs]

theorem renameHoistedRecord_nil (ren : Bool → String → Cedar.Spec.Attr) :
    (axs : List (Cedar.Spec.Attr × Cedar.Spec.Expr)) → renameHoistedRecord [] [] ren axs = axs
  | [] => rfl
  | (a, x) :: axs => by simp [renameHoistedRecord, renameHoisted_nil ren x, renameHoistedRecord_nil ren axs]

end

theorem renamePolicy_nil (ren : Bool → String → Cedar.Spec.Attr) (p : Cedar.Spec.Policy) :
    renamePolicy [] [] ren p = p := by
  simp [renamePolicy, renameHoisted_nil]

theorem mem_policies_lowerFrom : (ps : Dogwood.Spec.Policies) → (k : Nat) → {p : Cedar.Spec.Policy} →
    p ∈ (Dogwood.Spec.Policies.lowerFrom k ps).1 → ∃ q ∈ ps, ∃ k', p = (q.lowerFrom k').1
  | [], _, _, h => by simp [Dogwood.Spec.Policies.lowerFrom] at h
  | q :: ps, k, p, h => by
    simp only [Dogwood.Spec.Policies.lowerFrom, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨q, by simp, k, rfl⟩
    · obtain ⟨q', hq', k', rfl⟩ := mem_policies_lowerFrom ps _ h
      exact ⟨q', by simp [hq'], k', rfl⟩

theorem policy_lowerFrom_ofCedar {q : Dogwood.Spec.Policy} (hq : q.toExpr.leaves = []) (k : Nat) :
    Expr.ofCedar (q.lowerFrom k).1.toExpr = q.toExpr := by
  rw [Dogwood.Thm.policy_lowerFrom]
  have h := eq_ofCedar_lowerFrom q.toExpr hq
  conv => rhs; rw [h]
  rw [h, Dogwood.Thm.lowerFrom_ofCedar, Dogwood.Thm.lowerFrom_ofCedar]

/-- The reads the context findings are about are the lowered rules' and the recorded ones. -/
theorem mem_validate_allReads {r : Bool × String} :
    r ∈ Validate.allReads l ↔ r ∈ loweredReads l ∨ r ∈ l.contextReads := by
  unfold Validate.allReads
  by_cases h : r ∈ l.contextReads <;> simp [List.mem_append, List.mem_filter, h]

theorem contextReads_nil (hc : contextFindings l = []) (hlv : hasLeaves l = true) :
    ∀ q ∈ l.policies, contextReads ⟨l.temporal.map (·.id), l.providers.map (·.id)⟩ q.toExpr = [] := by
  intro q hq
  unfold contextFindings at hc
  have hr : loweredReads l = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    have := List.filterMap_eq_nil_iff.mp hc x (mem_validate_allReads.mpr (Or.inl hx))
    obtain ⟨w, a⟩ := x
    cases w <;> simp [hlv] at this
  unfold loweredReads at hr
  exact List.flatMap_eq_nil_iff.mp hr q hq

theorem specNames_spec (h : specNamesAbsent l = true) :
    (∀ x ∈ l.schema.acts.toList, ∀ y ∈ x.2.context.toList, isSpecLeafName y.1 = false) ∧
      (∀ q ∈ l.policies, (contextAttrs q.toExpr).all (fun a => !isSpecLeafName a) = true) := by
  unfold specNamesAbsent at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun x hx y hy => ?_, fun q hq => ?_⟩
  · have := h.1 x hx y hy; simpa using this
  · rw [List.all_eq_true]; intro a ha
    have := h.2 q hq a ha; simpa using this

theorem mem_allReads_contains (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    {b : Bool} {a : String} (h : (b, a) ∈ allReads l) :
    (if b then T.map Prod.fst else Pr.map Prod.fst).contains a = true := by
  unfold allReads at h
  rw [ruleReads_eq hT hPr] at h
  obtain ⟨rs, hrs, hm⟩ := List.mem_flatten.mp h
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hrs
  exact mem_hoistedReads _ _ _ hm

/-- A provider read of the lowered set is the read of a declared provider leaf, which the port
checked, with the type the crate gives it. -/
theorem provider_read (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hA : Assumptions l) (hprovs : ∀ g ∈ l.providers, providerLeafFindings l.schema g = [])
    {a : String} (h : (false, a) ∈ allReads l) :
    ∃ g d, g ∈ l.providers ∧ g.declaration = some d ∧ g.toCall = .ok ((Pr.lookup a).getD default) ∧
      g.id = a ∧ ((Pr.lookup a).getD default).outputType? (providerDeclsToSpec l.declarations l.schema).1 =
        crateOutputType g d ∧ (crateOutputType g d).isSome ∧
      (providerDeclsToSpec l.declarations l.schema).1.find? ((Pr.lookup a).getD default).function =
        some (crateSignature g.entityTypeNames ((Pr.lookup a).getD default).function d) := by
  have hc := mem_allReads_contains hT hPr h
  simp only [Bool.false_eq_true, if_false] at hc
  obtain ⟨c, hcl⟩ := lookup_eq_some_of_contains hc
  rw [hcl, Option.getD_some]
  obtain ⟨i, g, hgi, -, hR⟩ := exists_of_mem_forall₂ (providerCalls_forall₂ hPr) (mem_of_lookup hcl)
  obtain ⟨hga, hgc⟩ := hR
  have hg := List.mem_of_getElem? hgi
  obtain ⟨d, hd⟩ := declaration_of_findings (hprovs g hg)
  obtain ⟨hD, -⟩ := providerTypes_of hA.providerTypes hg hd hgc
  obtain ⟨-, hout, hsome, -⟩ := provider_sound (hprovs g hg) hd hgc hD
  exact ⟨g, d, hg, hd, hgc, hga.symm, hout, hsome, hD⟩

theorem mapM_isSome {α β : Type} {f : α → Option β} : {xs : List α} → (∀ x ∈ xs, (f x).isSome = true) →
    (xs.mapM f).isSome = true
  | [], _ => rfl
  | x :: xs, h => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h x (by simp))
    obtain ⟨ys, hys⟩ := Option.isSome_iff_exists.mp (mapM_isSome (xs := xs) (fun x' hx' => h x' (by simp [hx'])))
    simp [List.mapM_cons, hy, hys]

/-! ## The clauses of validity -/

theorem mem_of_mem_zipIdx' {α : Type} {xs : List α} {x : α} {k : Nat} (h : (x, k) ∈ xs.zipIdx) : x ∈ xs := by
  have : x ∈ xs.zipIdx.map Prod.fst := List.mem_map.mpr ⟨(x, k), h, rfl⟩
  rwa [List.zipIdx_map_fst] at this

theorem nodup_map_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    {xs : List α} → xs.Nodup → (xs.map f).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_inj hf h.2⟩
    obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
    exact h.1 (hf _ _ hfy ▸ hy)

/-- The policy set the conformance projection gives a lowered set. -/
def projected (l : Lowered) (T : List (String × Formula))
    (Pr : List (String × Dogwood.Spec.Provider.Call)) (sigs : Dogwood.Spec.EventSchema) : PolicySet :=
  { policies := l.policies.map (putBackPolicy T Pr)
    schema := sigs
    actionSchema := specActionSchema l
    maxWindow := l.eventSchema.maxWindow.seconds
    maxHorizon := l.eventSchema.maxHorizon.map (·.seconds)
    providerDecls := (providerDeclsToSpec l.declarations l.schema).1
    externalTypes := CedarSchema.Resolve.externalEntityTypes l.augmentedSchema
    externalActions := CedarSchema.Resolve.externalActions l.augmentedSchema }

variable {sigs : Dogwood.Spec.EventSchema}

theorem projected_leafList (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hl : policiesLeafless l = true) : (projected l T Pr sigs).leafList = (allReads l).map (readLeaf T Pr) :=
  leafList_eq hT hPr hl _ _ _ _ _ _ _

theorem projected_leafTypes (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hA : Assumptions l) (hprovs : ∀ g ∈ l.providers, providerLeafFindings l.schema g = []) :
    (projected l T Pr sigs).hoistedTypes?.isSome = true := by
  unfold PolicySet.hoistedTypes?
  apply mapM_isSome
  intro ⟨lf, k⟩ hx
  have hlf : lf ∈ (projected l T Pr sigs).leafList := mem_of_mem_zipIdx' hx
  rw [projected_leafList hT hPr hA.leafless] at hlf
  obtain ⟨⟨b, a⟩, hr, rfl⟩ := List.mem_map.mp hlf
  cases b with
  | true => simp [readLeaf, PolicySet.leafType?]
  | false =>
    obtain ⟨g, d, -, -, -, -, hout, hsome, -⟩ := provider_read hT hPr hA hprovs hr
    simp only [readLeaf, PolicySet.leafType?, projected, Option.isSome_map]
    rw [hout]; exact hsome

theorem projected_hoistedNames (P : PolicySet) :
    P.hoistedNames = (List.range P.leafList.length).map leafAttr := rfl

theorem projected_namesNodup (P : PolicySet) : P.hoistedNames.Nodup := by
  rw [projected_hoistedNames]
  exact nodup_map_inj (fun _ _ h => leafAttr_inj h) List.nodup_range

theorem hoistedNames_spec (P : PolicySet) : ∀ a ∈ P.hoistedNames, isSpecLeafName a = true := by
  intro a ha
  rw [projected_hoistedNames] at ha
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
  exact isSpecLeafName_leafAttr k

theorem projected_namesFresh (hA : Assumptions l) :
    ∀ act ∈ (projected l T Pr sigs).actionSchema.acts.toList, ∀ a ∈ (projected l T Pr sigs).hoistedNames,
      act.2.context.find? a = none :=
  fun act hact a ha => specActionSchema_fresh hA.specNames act hact a (hoistedNames_spec _ a ha)

theorem hasLeaves_of_leafList (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hl : policiesLeafless l = true) (h : (projected l T Pr sigs).leafList ≠ []) : hasLeaves l = true := by
  rw [projected_leafList hT hPr hl] at h
  unfold hasLeaves
  by_contra hc
  simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, not_or, ne_eq,
    Decidable.not_not] at hc
  apply h
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  obtain ⟨⟨b, a⟩, hr, -⟩ := List.mem_map.mp hx
  have := mem_allReads_contains hT hPr hr
  rw [tids_eq hT, pids_eq hPr, hc.1, hc.2] at this
  cases b <;> simp at this

theorem projected_readsContext (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hA : Assumptions l) (hctx : contextFindings l = []) :
    (projected l T Pr sigs).leafList ≠ [] → ∀ p ∈ (projected l T Pr sigs).policies,
      p.toExpr.ReadsContext (projected l T Pr sigs).hoistedNames := by
  intro hL p hp
  have hlv := hasLeaves_of_leafList hT hPr hA.leafless hL
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rw [putBackPolicy_toExpr]
  obtain ⟨-, -, -, -, -, hh⟩ := namesOnce_spec hA.names
  have htp : (T.map Prod.fst).contains "providers" = false := by
    rw [tids_eq hT]
    simp only [List.contains_eq_any_beq, List.any_map, Bool.eq_false_iff, ne_eq, List.any_eq_true,
      not_exists, not_and, Function.comp, beq_iff_eq]
    intro f hf h; exact (hh f hf).2 h.symm
  have hr := contextReads_nil hctx hlv q hq
  rw [← tids_eq hT, ← pids_eq hPr] at hr
  exact readsContext_putBack (hoistedNames_spec _) htp q.toExpr hr ((specNames_spec hA.specNames).2 q hq)

theorem projected_hoistedTypes (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hA : Assumptions l) (hprovs : ∀ g ∈ l.providers, providerLeafFindings l.schema g = []) :
    ∃ H, (projected l T Pr sigs).hoistedTypes? = some H :=
  Option.isSome_iff_exists.mp (projected_leafTypes hT hPr hA hprovs)

/-- The type of each leaf's attribute: `Bool` for a temporal leaf, the crate's type for a provider
leaf. -/
theorem leafType_of_read (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hA : Assumptions l) (hprovs : ∀ g ∈ l.providers, providerLeafFindings l.schema g = [])
    {r : Bool × String} (hr : r ∈ allReads l) :
    ∃ ty, (projected l T Pr sigs).leafType? (readLeaf T Pr r) = some ty ∧
      (r.1 = true → ty = .bool .anyBool) ∧
      (r.1 = false → ∃ g d, g ∈ l.providers ∧ g.id = r.2 ∧ g.declaration = some d ∧
        crateOutputType g d = some ty) := by
  obtain ⟨b, a⟩ := r
  cases b with
  | true => exact ⟨.bool .anyBool, rfl, fun _ => rfl, fun h => by cases h⟩
  | false =>
    obtain ⟨g, d, hg, hd, -, hga, hout, hsome, -⟩ := provider_read hT hPr hA hprovs hr
    obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.mp hsome
    refine ⟨ty, ?_, ?_, ?_⟩
    · simp only [readLeaf, PolicySet.leafType?, projected]
      rw [hout, hty]
    · intro h; exact absurd h (by simp)
    · intro _; exact ⟨g, d, hg, hga, hd, hty⟩

theorem projected_standardAncestors (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hA : Assumptions l) (hwf : l.schema.validateWellFormed = .ok ())
    (hprovs : ∀ g ∈ l.providers, providerLeafFindings l.schema g = [])
    (hs : schemaFindings l = []) :
    (projected l T Pr sigs).allAugmentedSchema.standardAncestors = true := by
  obtain ⟨H, hH⟩ := projected_hoistedTypes (sigs := sigs) hT hPr hA hprovs
  unfold PolicySet.allAugmentedSchema
  rw [hH, Option.getD_some]
  unfold schemaFindings at hs
  exact augment_standardAncestors hwf (List.map_eq_nil_iff.mp hs)

theorem projected_wellFormed (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hA : Assumptions l) (hwf : l.schema.validateWellFormed = .ok ())
    (hprovs : ∀ g ∈ l.providers, providerLeafFindings l.schema g = []) :
    (projected l T Pr sigs).allAugmentedSchema.validateWellFormed = .ok () := by
  obtain ⟨H, hH⟩ := projected_hoistedTypes (sigs := sigs) hT hPr hA hprovs
  unfold PolicySet.allAugmentedSchema
  rw [hH, Option.getD_some]
  apply augment_wellFormed hwf
  intro x hx
  obtain ⟨hHeq, _⟩ := mapM_option_eq_map hH
  rw [hHeq] at hx
  obtain ⟨⟨lf, k⟩, hlk, rfl⟩ := List.mem_map.mp hx
  have hlf := mem_of_mem_zipIdx' hlk
  rw [projected_leafList hT hPr hA.leafless] at hlf
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hlf
  obtain ⟨ty, hty, hbool, hprov⟩ := leafType_of_read (sigs := sigs) hT hPr hA hprovs hr
  simp only [hty, Option.map_some, Option.getD_some, Cedar.Validation.Qualified.getType]
  obtain ⟨b, a⟩ := r
  cases b with
  | true =>
    rw [hbool rfl]
    exact ⟨by unfold CedarType.validateWellFormed; rfl, by unfold CedarType.validateLifted; rfl⟩
  | false =>
    obtain ⟨g, d, hg, -, hd, hout⟩ := hprov rfl
    have hw := hA.providerWellFormed
    unfold providerTypesWellFormed at hw
    rw [List.all_eq_true] at hw
    have := hw g hg
    simp only [hd] at this
    rw [hout] at this
    simp only [Option.all_some, Bool.and_eq_true] at this
    constructor
    · split at this
      · assumption
      · exact absurd this.1 (by simp)
    · obtain ⟨-, h2⟩ := this
      split at h2
      · assumption
      · cases h2

/-- Every leaf's id is read, under its kind. -/
theorem read_of_id (hA : Assumptions l) {b : Bool} {i : String}
    (h : i ∈ (if b then l.temporal.map (·.id) else l.providers.map (·.id))) : (b, i) ∈ allReads l := by
  obtain ⟨hlt, hlp, -, htr, hpr, -⟩ := namesOnce_spec hA.names
  cases b with
  | true =>
    simp only [if_true] at h
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp h
    obtain ⟨j, hj⟩ := getElem?_of_mem' hf
    have hjl : j < l.temporalRules.length := by rw [hlt]; exact (List.getElem?_eq_some_iff.mp hj).1
    have hk := htr j f _ hj (List.getElem?_eq_getElem hjl)
    unfold allReads
    cases hr : (ruleReads l)[l.temporalRules[j]]? with
    | none => rw [hr] at hk; cases hk
    | some xs => rw [hr] at hk; exact List.mem_flatten.mpr ⟨xs, List.mem_of_getElem? hr, hk⟩
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp h
    obtain ⟨j, hj⟩ := getElem?_of_mem' hg
    have hjl : j < l.providerRules.length := by rw [hlp]; exact (List.getElem?_eq_some_iff.mp hj).1
    have hk := hpr j g _ hj (List.getElem?_eq_getElem hjl)
    unfold allReads
    cases hr : (ruleReads l)[l.providerRules[j]]? with
    | none => rw [hr] at hk; cases hk
    | some xs => rw [hr] at hk; exact List.mem_flatten.mpr ⟨xs, List.mem_of_getElem? hr, hk⟩

theorem specRen_eq {r : Bool × String} (hr : r ∈ allReads l) :
    ∃ i, i < (allReads l).length ∧ (allReads l)[i]? = some r ∧ specRen l r.1 r.2 = leafAttr i := by
  refine ⟨(allReads l).idxOf r, List.idxOf_lt_length_iff.mpr hr, ?_, rfl⟩
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr hr), List.getElem_idxOf]

/-- **An action's context in the specification's augmented schema relates to the crate's** as the
renaming of hoisted reads needs. -/
theorem ctxRel_projected (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hA : Assumptions l) (hprovs : ∀ g ∈ l.providers, providerLeafFindings l.schema g = [])
    {H : List (Cedar.Spec.Attr × QualifiedType)} (hH : (projected l T Pr sigs).hoistedTypes? = some H)
    {uid : Cedar.Spec.EntityUID} {e : ActionSchemaEntry} (he : (uid, e) ∈ l.schema.acts.toList) :
    CtxRel (T.map Prod.fst) (Pr.map Prod.fst) (specRen l) isSpecLeafName e.context
      (augmentEntry H (dropContext l.hoistedNames e)).context := by
  obtain ⟨hHeq, -⟩ := hoistedTypes_eq hH
  have hspec := (specNames_spec hA.specNames).1 (uid, e) he
  -- the crate's context, with the hoisted attributes dropped, names no leaf attribute
  have hL1 : ∀ a, isSpecLeafName a = true →
      (dropContext l.hoistedNames e).context.toList.find? (·.1 == a) = none := by
    intro a ha
    apply find?_of_not_mem
    intro hm
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
    have := (List.mem_filter.mp (Map.mem_make_mem_list hy)).1
    rw [hspec y this] at ha; cases ha
  have hkeys : (H.map (·.1)).Nodup := by rw [hHeq, leafTypes_keys]; exact projected_namesNodup _
  have hHnames : ∀ x ∈ H, isSpecLeafName x.1 = true := by
    intro x hx
    have : x.1 ∈ H.map Prod.fst := List.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hHeq, leafTypes_keys] at this
    exact hoistedNames_spec _ _ this
  -- the specification's attribute of the `i`-th read
  have hleaf : ∀ r ∈ allReads l, ∀ ty, (projected l T Pr sigs).leafType? (readLeaf T Pr r) = some ty →
      (augmentEntry H (dropContext l.hoistedNames e)).context.find? (specRen l r.1 r.2) =
        some (.required ty) := by
    intro r hr ty hty
    obtain ⟨i, hi, hri, hren⟩ := specRen_eq hr
    rw [hren]
    simp only [augmentEntry]
    rw [make_append_find?, hL1 _ (isSpecLeafName_leafAttr i), Option.none_or]
    have hil : i < (projected l T Pr sigs).leafList.length := by
      rw [projected_leafList hT hPr hA.leafless, List.length_map]; exact hi
    have hli : (projected l T Pr sigs).leafList[i] = readLeaf T Pr r := by
      simp only [projected_leafList hT hPr hA.leafless, List.getElem_map]
      rw [List.getElem?_eq_some_iff] at hri
      obtain ⟨_, h2⟩ := hri
      rw [h2]
    rw [hHeq, find?_of_mem (by rw [leafTypes_keys]; exact projected_namesNodup _) (mem_leafTypes hil)]
    simp [hli, hty]
  refine ⟨fun a ha q hq => ?_, fun a ha q R q' hq hR hq' => ?_, fun b hbt hbp hbr => ?_⟩
  · -- a temporal leaf
    rw [tids_eq hT] at ha
    have hr := read_of_id (b := true) hA (by simpa using ha)
    obtain ⟨ty, hty, hb, -⟩ := leafType_of_read (sigs := sigs) hT hPr hA hprovs hr
    have hty' := hb rfl
    subst hty'
    rw [hleaf _ hr _ hty]
    -- the crate's attribute is a `Bool`
    have htb := hA.temporalBool
    unfold temporalAttrsBool at htb
    rw [List.all_eq_true] at htb
    have := htb (uid, e) he
    rw [List.all_eq_true] at this
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
    have := this f hf
    simp only [hq, Option.all_some, beq_iff_eq] at this
    rw [this]
  · -- a provider leaf
    rw [pids_eq hPr] at ha
    have hr := read_of_id (b := false) hA (by simpa using ha)
    obtain ⟨ty, hty, -, hp⟩ := leafType_of_read (sigs := sigs) hT hPr hA hprovs hr
    obtain ⟨g, d, hg, hga, hd, hout⟩ := hp rfl
    rw [hleaf _ hr _ hty]
    obtain ⟨pc, -, hpc⟩ := forall₂_mem_left (providerCalls_forall₂ hPr) hg
    obtain ⟨-, hrec⟩ := providerTypes_of hA.providerTypes hg hd hpc.2
    have := hrec uid e he q R hq hR q' (by rw [hga]; exact hq')
    rw [hout] at this
    simp only [Option.some.injEq] at this
    rw [this]
  · -- any other attribute
    have hbH : H.find? (·.1 == b) = none := by
      apply find?_of_not_mem
      intro hm
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
      rw [hHnames x hx] at hbr; cases hbr
    simp only [augmentEntry]
    rw [make_append_find?, hbH, Option.or_none, ← map_find?_eq]
    simp only [dropContext]
    rw [Map.make_find?_eq_list_find?, find?_filter_keep, ← map_find?_eq]
    intro y _ hy
    simp only [Bool.not_eq_true']
    rw [Bool.eq_false_iff]
    intro hc
    have hd := mem_of_contains hc
    rw [hy] at hd
    unfold Lowered.hoistedNames at hd
    rcases List.mem_append.mp hd with hd | hd
    · rw [← tids_eq hT] at hd; exact hbt hd
    · split at hd
      · cases hd
      · simp only [List.mem_singleton] at hd; exact hbp hd

theorem validate_envs_ne {ps : Cedar.Spec.Policies} {S : Schema} (hps : ps ≠ [])
    (h : Cedar.Validation.validate ps S = .ok ()) : S.environments ≠ [] := by
  intro hnil
  obtain ⟨p, ps', rfl⟩ := List.exists_cons_of_ne_nil hps
  simp only [Cedar.Validation.validate] at h
  unfold Cedar.Validation.typecheckPolicyWithEnvironments at h
  rw [hnil] at h
  simp only [List.mapM_nil] at h
  cases hc : Cedar.Validation.checkEntities S p.toExpr with
  | error e => simp [hc, Except.mapError, bind, Except.bind] at h
  | ok u =>
    simp [hc, Except.mapError, bind, Except.bind, pure, Except.pure, Cedar.Validation.allFalse] at h

theorem cedarPolicies_ne (h : l.policies ≠ []) : cedarPolicies l ≠ [] := by
  unfold cedarPolicies
  obtain ⟨q, qs, hq⟩ := List.exists_cons_of_ne_nil h
  rw [hq]
  simp [Dogwood.Spec.Policies.lowerFrom]

theorem mapOnValues_self {m : Map Cedar.Spec.EntityUID ActionSchemaEntry}
    {g : ActionSchemaEntry → ActionSchemaEntry} (h : ∀ x ∈ m.toList, g x.2 = x.2) : m.mapOnValues g = m := by
  obtain ⟨L⟩ := m
  simp only [Map.mapOnValues, Map.toList_mk_id] at h ⊢
  congr 1
  conv => rhs; rw [← List.map_id L]
  apply List.map_congr_left
  intro x hx
  obtain ⟨k, v⟩ := x
  simp [h (k, v) hx]

theorem make_toList_wf {β : Type} {m : Map Cedar.Spec.Attr β} (hm : m.WellFormed) : Map.make m.toList = m := by
  rw [Map.make_eq_mk.mp (Map.wf_iff_sorted.mp hm), Map.mk_toList_id]

/-- Without leaves, the specification's augmented schema is the crate's. -/
theorem augmented_of_noLeaves (hwf : l.schema.validateWellFormed = .ok ()) (hne : l.schema.environments ≠ [])
    (ht : l.temporal = []) (hp : l.providers = []) :
    Dogwood.Spec.Schema.augment (specActionSchema l) [] = l.schema := by
  rw [augmentedSpec_eq hwf hne]
  have hdrop : l.hoistedNames = [] := by simp [Lowered.hoistedNames, ht, hp]
  rw [hdrop]
  obtain ⟨env, -, hacts, hw⟩ := wellFormed_of_validate hwf hne
  have hwfa := hw.2.1
  rw [hacts] at hwfa
  have hself : l.schema.acts.mapOnValues (fun e => augmentEntry [] (dropContext [] e)) = l.schema.acts := by
    apply mapOnValues_self
    intro ⟨uid, e⟩ he
    have hfind := Map.mem_toList_find? hwfa.1 he
    have hew := hwfa.2.1 uid e hfind
    have hctxwf : e.context.WellFormed := by
      have := hew.2.2.2.2.2.2.1
      cases this with
      | record_wf h₁ _ => exact h₁
    have hfl : List.filter (fun (_ : Cedar.Spec.Attr × QualifiedType) => true) e.context.toList =
        e.context.toList := List.filter_eq_self.mpr (by simp)
    simp only [augmentEntry, dropContext, List.contains_nil, Bool.not_false, List.append_nil]
    rw [hfl, make_toList_wf hctxwf, make_toList_wf hctxwf]
  rw [hself]

/-- **The schema is complete**: a policy set with a rule declares no name `external`, when Cedar's
validator reports nothing. -/
theorem projected_complete (hcedar : cedarFindings l = []) :
    (projected l T Pr sigs).policies ≠ [] →
      (projected l T Pr sigs).externalTypes = [] ∧ (projected l T Pr sigs).externalActions = [] := by
  intro hp
  have hpol : l.policies ≠ [] := by simpa [projected] using hp
  simp only [projected]
  unfold cedarFindings at hcedar
  rw [if_neg (by simpa [List.isEmpty_iff] using hpol)] at hcedar
  split at hcedar
  · rename_i hinc
    simp only [incompleteNames, List.isEmpty_iff, List.append_eq_nil_iff, List.map_eq_nil_iff]
      at hinc
    obtain ⟨h₁, h₂⟩ := hinc
    refine ⟨?_, ?_⟩
    · rw [← List.length_eq_zero_iff, ← List.length_mergeSort (le := fun a b =>
        CedarSchema.nameLe (nameText a) (nameText b)), h₁]; rfl
    · rw [← List.length_eq_zero_iff, ← List.length_mergeSort (le := uidLe), h₂]; rfl
  · exfalso
    unfold incompleteFindings at hcedar
    exact hpol (List.map_eq_nil_iff.mp hcedar)

/-- **The Cedar part**: Cedar's validator accepts the specification's lowering against its
augmented schema, when it accepts the crate's against the crate's. -/
theorem projected_cedar (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hA : Assumptions l) (hwf : l.schema.validateWellFormed = .ok ())
    (hcedar : cedarFindings l = []) (hctx : contextFindings l = [])
    (hprovs : ∀ g ∈ l.providers, providerLeafFindings l.schema g = []) :
    Cedar.Validation.validate (projected l T Pr sigs).lowered (projected l T Pr sigs).allAugmentedSchema = .ok () := by
  by_cases hpol : l.policies = []
  · simp [projected, hpol, PolicySet.lowered, Dogwood.Spec.Policies.lowerFrom, Cedar.Validation.validate]
    rfl
  have hval : Cedar.Validation.validate (cedarPolicies l) l.schema = .ok () := by
    unfold cedarFindings at hcedar
    have : l.policies.isEmpty = false := by simpa using hpol
    rw [if_neg (by simp [this])] at hcedar
    split at hcedar
    · split at hcedar
      · assumption
      · cases hcedar
    · exfalso
      unfold incompleteFindings at hcedar
      exact hpol (List.map_eq_nil_iff.mp hcedar)
  have hne := validate_envs_ne (cedarPolicies_ne hpol) hval
  obtain ⟨-, -, hnd, -, -, hh⟩ := namesOnce_spec hA.names
  obtain ⟨H, hH⟩ := projected_hoistedTypes (sigs := sigs) hT hPr hA hprovs
  have hlow : (projected l T Pr sigs).lowered =
      (cedarPolicies l).map (renamePolicy (T.map Prod.fst) (Pr.map Prod.fst) (specRen l)) :=
    lowered_eq hT hPr hA.leafless hnd
  have hsch : (projected l T Pr sigs).allAugmentedSchema =
      Dogwood.Spec.Schema.augment (specActionSchema l) H := by
    unfold PolicySet.allAugmentedSchema; rw [hH]; rfl
  rw [hlow, hsch]
  by_cases hlv : hasLeaves l = true
  · rw [augmentedSpec_eq hwf hne]
    refine validate_renameHoisted (reserved := isSpecLeafName) (S₁ := l.schema)
      (f := fun e => augmentEntry H (dropContext l.hoistedNames e)) ?_ ?_ rfl rfl (fun _ => ⟨rfl, rfl, rfl⟩)
      ?_ (acts_wf hwf hne) ?_ ?_ hval
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
  · have ht : l.temporal = [] := by
      unfold hasLeaves at hlv
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, not_or, ne_eq,
        Decidable.not_not] at hlv
      exact hlv.1
    have hp : l.providers = [] := by
      unfold hasLeaves at hlv
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, not_or, ne_eq,
        Decidable.not_not] at hlv
      exact hlv.2
    have hT0 : T.map Prod.fst = [] := by rw [tids_eq hT, ht]; rfl
    have hP0 : Pr.map Prod.fst = [] := by rw [pids_eq hPr, hp]; rfl
    have hH0 : H = [] := by
      obtain ⟨hHeq, -⟩ := hoistedTypes_eq hH
      rw [hHeq]
      unfold PolicySet.leafTypes
      rw [projected_leafList hT hPr hA.leafless]
      have : allReads l = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro ⟨b, a⟩ hr
        have := mem_allReads_contains hT hPr hr
        rw [hT0, hP0] at this
        cases b <;> simp at this
      rw [this]; rfl
    rw [hT0, hP0, hH0, augmented_of_noLeaves hwf hne ht hp]
    have : (cedarPolicies l).map (renamePolicy [] [] (specRen l)) = cedarPolicies l := by
      conv => rhs; rw [← List.map_id (cedarPolicies l)]
      exact List.map_congr_left (fun p _ => renamePolicy_nil _ p)
    rw [this]
    exact hval

theorem derived_spec (h : derivedFacts l = true) : ∀ ev ∈ l.eventSchema.events,
    (∀ x ∈ ev.leafFields, isSpliced x.1 = true →
      (((l.schema.acts.find? (actionUid ev.namespace ev.action)).map (·.context)).bind (pathType · x.1)).isSome) ∧
    (∀ pin ∈ ev.pins, ev.leafFields.any (·.1 == pin.fieldPath) = true) := by
  unfold derivedFacts at h
  rw [List.all_eq_true] at h
  intro ev hev
  have := h ev hev
  simp only [Bool.and_eq_true, List.all_eq_true] at this
  refine ⟨fun x hx hs => ?_, this.2⟩
  have := this.1 x hx
  simp only [hs, Bool.not_true, Bool.false_or] at this
  exact this

theorem mem_envs_of {targets : List (String × String)} {pc rc : ScopeConstraint} {e : ReqEnv}
    (ht : (e.uid, e.entry) ∈ targets.filterMap (fun x => action? l.schema x.1 x.2))
    (hp : e.principal ∈ admittedTypes l.schema e.entry .principal pc)
    (hr : e.resource ∈ admittedTypes l.schema e.entry .resource rc) :
    e ∈ (targets.filterMap fun x => action? l.schema x.1 x.2).flatMap (fun x =>
      (admittedTypes l.schema x.2 .principal pc).flatMap fun p =>
        (admittedTypes l.schema x.2 .resource rc).map fun r => (⟨x.1, x.2, p, r⟩ : ReqEnv)) := by
  rw [List.mem_flatMap]
  refine ⟨(e.uid, e.entry), ht, ?_⟩
  rw [List.mem_flatMap]
  exact ⟨e.principal, hp, List.mem_map.mpr ⟨e.resource, hr, rfl⟩⟩

theorem leafFindings_tp {C : LeafCtx} {φ : Formula} (h : leafFindings C φ = []) : checkTpDependence φ = [] := by
  unfold leafFindings at h
  simp only [List.append_eq_nil_iff] at h
  exact h.1.1.1.2

/-- **The temporal part**: every temporal leaf of the projection is valid. -/
theorem projected_temporal (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hS : typedSignatures l.eventSchema l.schema = .ok sigs) (hA : Assumptions l)
    (hwf : l.schema.validateWellFormed = .ok ()) {leaves : List (TemporalField × Formula)}
    (hL : leafFormulas l = .ok leaves)
    (htemp : ∀ x ∈ leaves, leafFindings (leafCtx l (loweredFacts l) x.1) x.2 = []) :
    ∀ p ∈ (projected l T Pr sigs).policies, ∀ φ F, (.inl φ, F) ∈ p.toExpr.leafFacts [] →
      (projected l T Pr sigs).LeafValid p F φ := by
  intro p hp φ F hm
  obtain ⟨j, f, k, q, hfj, hkj, hqk, rfl, hφ, G, hG, hsub⟩ :=
    temporal_position hT hPr hA.leafless hA.names hp hm
  have hfin := htemp (f, φ) (leaf_mem_leaves hL hfj hφ)
  have hfm := List.mem_of_getElem? hfj
  have hpc := parseChecked_of (hp := hA.parse) hfm hφ
  have hnec := noEmptyContext_of (hp := hA.noEmptyContext) hfm hφ
  refine ⟨fun env henv => ?_, ?_, ?_⟩
  · simp only [PolicySet.envsOf, List.mem_filter] at henv
    obtain ⟨henv, had⟩ := henv
    have hcov := coversScope_temporal hA.scopes hfj hkj hqk
    obtain ⟨e, het, hep, her, hview⟩ := leafEnv hwf hA.names hA.appliesTo hcov henv had
    have he : e ∈ (leafCtx l (loweredFacts l) f).envs := mem_envs_of het hep her
    apply leaf_wellTyped hfin hpc hnec he
    exact {
      toEnvView := hview _ rfl
      maxWindow := rfl
      facts := by
        intro g hg hr
        simp only [leafCtx, hG, Option.getD_some] at hg
        exact hsub g hg hr
      events := fun a kd ev hev => events_agree hS (derived_spec hA.derived) hev }
  · have : Dogwood.Eval.isSafeB φ = true := by
      unfold parseChecked at hpc
      simp only [Bool.and_eq_true] at hpc
      exact hpc.2
    exact (Dogwood.Thm.isSafeB_iff φ).mp this
  · exact (checkTpDependence_eq_nil_iff φ).mp (leafFindings_tp hfin)

theorem leafFindings_horizon {C : LeafCtx} {φ : Formula} (h : leafFindings C φ = [])
    {H : Int} (hc : C.horizonCap = some H) : φ.horizon .seconds ≤ H := by
  unfold leafFindings at h
  simp only [List.append_eq_nil_iff, Option.toList_eq_nil_iff] at h
  have hz := h.1.1.1.1.1.1.1.1.2
  simp only [horizonProblem, hc] at hz
  split at hz
  · cases hz
  · omega

/-- **The horizon**: every temporal leaf of the projection looks back at most `max_horizon`. -/
theorem projected_horizon (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hA : Assumptions l) {leaves : List (TemporalField × Formula)}
    (hL : leafFormulas l = .ok leaves)
    (htemp : ∀ x ∈ leaves, leafFindings (leafCtx l (loweredFacts l) x.1) x.2 = []) :
    ∀ H, (projected l T Pr sigs).maxHorizon = some H →
      ∀ φ ∈ (projected l T Pr sigs).temporalLeaves, φ.horizon .seconds ≤ H := by
  intro H hH φ hφ
  simp only [PolicySet.temporalLeaves, List.mem_flatMap, List.mem_filterMap] at hφ
  obtain ⟨p, hp, lf, hlf, hsome⟩ := hφ
  cases lf with
  | inr _ => cases hsome
  | inl ψ =>
    cases hsome
    obtain ⟨F, hm⟩ := Dogwood.Thm.exists_leafFacts hlf []
    obtain ⟨j, f, k, q, hfj, -, -, -, hφ', -, -, -⟩ :=
      temporal_position hT hPr hA.leafless hA.names hp hm
    have hfin := htemp (f, φ) (leaf_mem_leaves hL hfj hφ')
    exact leafFindings_horizon hfin hH

/-- **The provider part**: every provider leaf of the projection is declared and typed. -/
theorem projected_providers (hT : l.leafFormulas = .ok T) (hPr : l.providerCalls = .ok Pr)
    (hA : Assumptions l) (hwf : l.schema.validateWellFormed = .ok ())
    (hprovs : ∀ g ∈ l.providers, providerLeafFindings l.schema g = []) :
    ∀ p ∈ (projected l T Pr sigs).policies, ∀ c F, (.inr c, F) ∈ p.toExpr.leafFacts [] →
      c.Declared (projected l T Pr sigs).providerDecls ∧ ∀ env ∈ (projected l T Pr sigs).envsOf p,
        c.TypedIn ((projected l T Pr sigs).typingCtx env F) (projected l T Pr sigs).providerDecls := by
  intro p hp c F hm
  obtain ⟨j, g, k, q, hgj, hkj, hqk, rfl, hc⟩ := provider_position hT hPr hA.leafless hA.names hp hm
  have hgm := List.mem_of_getElem? hgj
  obtain ⟨d, hd⟩ := declaration_of_findings (hprovs g hgm)
  obtain ⟨hD, -⟩ := providerTypes_of hA.providerTypes hgm hd hc
  obtain ⟨hdecl, -, -, htyped⟩ := provider_sound (hprovs g hgm) hd hc hD
  refine ⟨hdecl, fun env henv => ?_⟩
  simp only [PolicySet.envsOf, List.mem_filter] at henv
  obtain ⟨henv, had⟩ := henv
  have hcov := coversScope_provider hA.scopes hgj hkj hqk
  obtain ⟨e, het, hep, her, hview⟩ := leafEnv hwf hA.names hA.appliesTo hcov henv had
  exact htyped _ e (mem_envs_of het hep her) (hview _ rfl)

end

/-! ## Soundness -/

/-- **The frontend's validator is sound.** If the earlier stages of the frontend accepted a policy
set, with the guarantees they give (`Assumptions`), and Cedar's schema construction accepted the
augmented schema (`l.schema.validateWellFormed = .ok ()`), and the validator reports no error on
the lowered set, then the specification's projection of the lowered set is valid. -/
theorem validate_sound {l : Lowered} {c : Conformance.Lowered} {fs : List Conformance.CrateFinding}
    (hc : l.toConformance = .ok c) (hv : validate l = .ok fs) (hacc : ∀ f ∈ fs, f.warning = true)
    (hA : Assumptions l) (hwf : l.schema.validateWellFormed = .ok ()) :
    c.policySet.Valid := by
  obtain ⟨T, Pr, sigs, hT, hPr, hS, hP⟩ := toConformance_ok hc
  obtain ⟨leaves, hL, hcedar, hctx, htemp, hprovs⟩ := validate_parts hv hacc
  rw [hP]
  refine PolicySet.ValidAll.toValid {
    leafTypes := projected_leafTypes (sigs := sigs) hT hPr hA hprovs
    namesNodup := projected_namesNodup _
    namesFresh := projected_namesFresh (T := T) (Pr := Pr) (sigs := sigs) hA
    readsContext := projected_readsContext hT hPr hA hctx
    wellFormed := projected_wellFormed hT hPr hA hwf hprovs
    standardAncestors := projected_standardAncestors hT hPr hA hwf hprovs (validate_schema hv hacc)
    complete := projected_complete hcedar
    cedar := projected_cedar hT hPr hA hwf hcedar hctx hprovs
    temporal := projected_temporal hT hPr hS hA hwf hL htemp
    providers := projected_providers hT hPr hA hwf hprovs
    horizon := projected_horizon hT hPr hA hL htemp }

end Dogwood.Thm.Frontend

