import Dogwood.Frontend.Driver
import Dogwood.Thm.Frontend.CedarPrint

/-!
# Theorems about the multi-entry lowering and the stable ids

* Lowering one entry, without a distincter or stable ids, and merging it is the single-entry
  lowering (`lowerEntries_one`): the crate's `lower` is `merge(base, vec![lower_entry(…)])`, and
  the Lean port of `lower_many` agrees with its port of `lower` on one entry.
* The stable ids an assignment yields are one per policy, each valid, and distinct
  (`assignIds_length`, `assignIds_valid`); a valid id is a nonempty string of
  at most 128 bytes of the portable alphabet (`validatePolicyId_ok`).
* The distincter checks: no repeat when `firstRepeat` finds none (`firstRepeat_nodup`).
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend
open Dogwood.Frontend.Ids

/-! ## One entry -/

/-- Merging one entry into nothing keeps its results as they are. -/
theorem mergedEntries_add_nil (e : Entry) :
    MergedEntries.add {} e = .ok
      { policies := e.lowered.cedarified.policies
        contextFields := e.lowered.cedarified.contextFields
        providerFields := e.lowered.cedarified.providerFields
        ruleIds := e.lowered.cedarified.ruleIds
        ruleKeys := e.lowered.cedarified.ruleKeys
        temporalRules := e.lowered.cedarified.temporalRules
        providerRules := e.lowered.cedarified.providerRules
        referencedEnums := e.lowered.cedarified.referencedEnums
        enumNames := e.lowered.cedarified.enumNames
        pinned := e.pinned
        contextReads := Cedarify.authoredReads e.input.expanded } := by
  simp [MergedEntries.add, unionSorted, extendSorted, bind, Except.bind, pure, Except.pure]

/-- Lowering one entry without a distincter or stable ids against the base, and merging it, is
the single-entry lowering `lowerParsed` (crate: `lower` is `merge(base, vec![lower_entry(…)])`). -/
theorem lowerEntries_one (i : Inputs) (e : Surface.PolicySet) :
    (do let b ← Base.derive i.eventSchema i.actionSchema i.providers
        let r ← lowerEntries b [{ expanded := e }] false
        pure r.1) = lowerParsed i e := by
  simp only [lowerParsed, Base.derive, lowerEntries, lowerEach, lowerEntry, mergeEntries,
    Cedarify.cedarify, tagEntry, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure,
    Except.pure, Except.map]
  cases Derive.derive i.eventSchema i.actionSchema with
  | error => rfl
  | ok d =>
  simp only
  cases universalPins d with
  | error => rfl
  | ok pins =>
  simp only
  cases decisionKinds d with
  | error => rfl
  | ok kinds =>
  simp only
  cases Macros.rejectArrays e with
  | error => rfl
  | ok u =>
  simp only
  cases Cedarify.cedarifyFull e i.actionSchema i.providers with
  | error => rfl
  | ok w =>
  simp only
  cases List.mapM (fun f => LeafPasses.injectPins d f.temporal.condition) w.cedarified.contextFields with
  | error => rfl
  | ok pinned =>
  simp only [List.foldlM, mergedEntries_add_nil, MergedEntries.cedarified, bind, Except.bind, pure,
    Except.pure]
  cases Augment.augment i.actionSchema i.providers w.cedarified.referencedEnums
    (withConditions w.cedarified.contextFields pinned) w.cedarified.providerFields with
  | error => rfl
  | ok a =>
  simp only
  cases List.mapM LeafPasses.unorderTimepoints pinned with
  | error => rfl
  | ok x =>
  simp only
  cases List.mapM (LeafPasses.relativize d pins) x with
  | error => rfl
  | ok r =>
  simp only
  cases Augment.resolveProviders i.providers w.cedarified.enumNames w.cedarified.providerFields with
  | error => rfl
  | ok p =>
  simp only
  cases Result.atStage Stage.compileSchema (CedarSchema.resolve a) with
  | error => rfl
  | ok S => rfl

/-! ## Stable ids -/

/-- Positional ids are no ids. -/
theorem assignIds_positional (ps : List Surface.Policy) : assignIds ps .positional = .ok none := rfl

/-- A valid policy id is nonempty, at most 128 bytes long, and of the portable alphabet. -/
theorem validatePolicyId_ok {id : String} (h : validatePolicyId id = .ok ()) :
    id ≠ "" ∧ id.utf8ByteSize ≤ maxPolicyIdLen ∧ ∀ c ∈ id.toList, isIdChar c = true := by
  unfold validatePolicyId at h
  by_cases h₁ : id.isEmpty
  · simp [h₁] at h
  · by_cases h₂ : id.utf8ByteSize > maxPolicyIdLen
    · simp [h₁, h₂] at h
    · simp only [h₁, h₂, Bool.false_eq_true, ↓reduceIte] at h
      refine ⟨fun he => by simp [he] at h₁, by omega, ?_⟩
      intro c hc
      cases hf : id.toList.find? (fun c => !isIdChar c) with
      | some c' => simp [hf] at h
      | none =>
        have := List.find?_eq_none.mp hf c hc
        simpa using this

/-- What `checkIds` establishes: every id valid, none repeated, and none among `seen`. -/
theorem checkIds_ok {spans : List Span} {seen : List (String × Nat)} {k : Nat} {ids : List String}
    (h : checkIds spans seen k ids = .ok ()) :
    (∀ id ∈ ids, validatePolicyId id = .ok ()) ∧ ids.Nodup ∧ ∀ id ∈ ids, seen.lookup id = none := by
  induction ids generalizing seen k with
  | nil => simp
  | cons id rest ih =>
    simp only [checkIds, bind, Except.bind] at h
    cases hv : validatePolicyId id with
    | error r => simp [hv] at h
    | ok u =>
      cases hl : seen.lookup id with
      | some first => simp [hv, hl, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
      | none =>
        simp only [hv, hl, pure, Except.pure] at h
        obtain ⟨hvalid, hnodup, hfresh⟩ := ih h
        refine ⟨?_, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · cases u; exact hv
          · exact hvalid x hx
        · refine List.nodup_cons.mpr ⟨fun hmem => ?_, hnodup⟩
          have := hfresh id hmem
          simp [List.lookup_append, hl] at this
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hl
          · have := hfresh x hx
            simp only [List.lookup_append] at this
            cases hs : seen.lookup x with
            | none => rfl
            | some v => simp [hs] at this

/-- The ids an assignment yields: one per policy. -/
theorem assignIds_length {ps : List Surface.Policy} {src : IdSource} {ids : List String}
    (h : assignIds ps src = .ok (some ids)) : ids.length = ps.length := by
  cases src with
  | positional => simp [assignIds] at h
  | annotation =>
    simp only [assignIds, bind, Except.bind] at h
    cases hm : (ps.zipIdx).mapM (fun (p, k) => annotationId k p) with
    | error e => simp [hm] at h
    | ok xs =>
      simp only [hm] at h
      cases hc : checkIds (ps.map (·.span)) [] 0 xs with
      | error e => simp [hc] at h
      | ok u =>
        simp [hc, pure, Except.pure] at h
        subst h
        simpa using mapM_except_length _ _ _ hm
  | explicit xs =>
    simp only [assignIds, bind, Except.bind] at h
    by_cases hlen : (xs.length != ps.length) = true
    · simp [hlen] at h
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at h
      cases hc : checkIds (ps.map (·.span)) [] 0 xs with
      | error e => simp [hc] at h
      | ok u =>
        simp [hc] at h
        subst h
        simpa using hlen

/-- The ids an assignment yields are valid policy ids and distinct. -/
theorem assignIds_valid {ps : List Surface.Policy} {src : IdSource} {ids : List String}
    (h : assignIds ps src = .ok (some ids)) :
    (∀ id ∈ ids, validatePolicyId id = .ok ()) ∧ ids.Nodup := by
  cases src with
  | positional => simp [assignIds] at h
  | annotation =>
    simp only [assignIds, bind, Except.bind] at h
    cases hm : (ps.zipIdx).mapM (fun (p, k) => annotationId k p) with
    | error e => simp [hm] at h
    | ok xs =>
      simp only [hm] at h
      cases hc : checkIds (ps.map (·.span)) [] 0 xs with
      | error e => simp [hc] at h
      | ok u =>
        simp [hc, pure, Except.pure] at h
        subst h
        have := checkIds_ok hc
        exact ⟨this.1, this.2.1⟩
  | explicit xs =>
    simp only [assignIds, bind, Except.bind] at h
    by_cases hlen : (xs.length != ps.length) = true
    · simp [hlen] at h
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at h
      cases hc : checkIds (ps.map (·.span)) [] 0 xs with
      | error e => simp [hc] at h
      | ok u =>
        simp [hc] at h
        subst h
        have := checkIds_ok hc
        exact ⟨this.1, this.2.1⟩

/-! ## Distincters -/

/-- When `firstRepeat` finds no repeat, the distincters are distinct, and none is among
`seen`. -/
theorem firstRepeat_nodup {seen ds : List String} (h : firstRepeat seen ds = none) :
    ds.Nodup ∧ ∀ d ∈ ds, d ∉ seen := by
  induction ds generalizing seen with
  | nil => simp
  | cons d rest ih =>
    simp only [firstRepeat, List.contains_iff_mem] at h
    by_cases hd : d ∈ seen
    · simp [hd] at h
    · simp only [hd, ↓reduceIte] at h
      obtain ⟨hn, hs⟩ := ih h
      refine ⟨List.nodup_cons.mpr ⟨fun hm => hs d hm (List.mem_cons_self ..), hn⟩, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hd
      · exact fun hm => hs x hx (List.mem_cons_of_mem _ hm)

end Dogwood.Thm.Frontend
