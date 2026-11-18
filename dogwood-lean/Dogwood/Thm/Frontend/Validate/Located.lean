import Dogwood.Thm.Frontend.Validate.Converse

/-!
# The located findings are the validator's

`Validate.validateLocated` reports each finding of `Validate.validate` with where the crate reports
it (`Validate.Located`). It finds the same findings, in the same order
(`validateLocated_findings`): the provider leaves' located checks find the same messages as
`providerLeafFindings` (`providerLeafLocated_messages`), and Cedar's located finding is
`cedarFindings`' (`cedarLocated_findings`).
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.Validate

/-- The method chain's located checks find `chainProblems`' messages. -/
theorem chainLocated_messages (C : ProviderCtx) (decl : ProviderDecls.ProviderDecl) (base : Nat) :
    ∀ (p : ProviderDecls.ParamType) (ms : List Provider.MethodCall),
      (chainLocated C decl base p ms).map (·.1) = chainProblems C decl p ms
  | _, [] => by simp [chainLocated, chainProblems]
  | p, m :: ms => by
    unfold chainLocated chainProblems
    split
    · simp [chainLocated_messages C decl base p ms]
    · split
      · simp
      · simp only [List.map_append, List.map_map]
        rw [chainLocated_messages C decl base _ ms]
        simp [Function.comp_def]

/-- A provider leaf's located checks find `providerLeafFindings`' messages. -/
theorem providerLeafLocated_messages (S : Cedar.Validation.Schema) (f : LoweredProviderField) :
    (providerLeafLocated S f).map (·.1) = providerLeafFindings S f := by
  unfold providerLeafLocated providerLeafFindings
  split
  · rfl
  · split
    · simp [Function.comp_def]
    · simp only [List.map_append, List.map_map, List.map_flatMap, chainLocated_messages]
      simp [Function.comp_def]

/-- Cedar's located finding is `cedarFindings`'. -/
theorem cedarLocated_findings (l : Lowered) : (cedarLocated l).map (·.finding) = cedarFindings l := by
  unfold cedarLocated cedarFindings
  split
  · rfl
  · split
    · cases Cedar.Validation.validate (cedarPolicies l) l.schema with
      | ok u => cases u; rfl
      | error e => simp [Function.comp_def]
    · rw [List.map_map]
      exact List.zipIdx_map_fst 0 _

/-- Findings located per element of an indexed list, forgotten, are the findings per element. -/
theorem zipIdx_flatMap_map {α β γ : Type} (fin : β → γ) (G : α → Nat → List β) (H : α → List γ)
    (h : ∀ x j, (G x j).map fin = H x) :
    ∀ (xs : List α) (n : Nat), ((xs.zipIdx n).flatMap fun p => G p.1 p.2).map fin = xs.flatMap H
  | [], _ => rfl
  | x :: xs, n => by
    simp only [List.zipIdx_cons, List.flatMap_cons, List.map_append, h]
    rw [zipIdx_flatMap_map fin G H h xs (n + 1)]

/-- **The located findings are the validator's**, in its order. -/
theorem validateLocated_findings (l : Lowered) :
    (validateLocated l).map (·.map (·.finding)) = validate l := by
  unfold validateLocated validate
  cases hL : leafFormulas l with
  | error e => rfl
  | ok leaves =>
    simp only [bind, Except.bind, pure, Except.pure, Except.map, List.map_append,
      cedarLocated_findings, List.map_map]
    have ht := zipIdx_flatMap_map (fun (x : Located) => x.finding)
      (fun (x : TemporalField × Dogwood.Spec.Temporal.Formula) (j : Nat) =>
        (leafFindings (leafCtx l (loweredFacts l) x.1) x.2).map fun m =>
          ({ finding := finding "temporal" m, rule := l.temporalRules[j]?,
             span := some x.1.condition.span } : Located))
      (fun x => (leafFindings (leafCtx l (loweredFacts l) x.1) x.2).map (finding "temporal"))
      (fun x j => by simp [Function.comp_def]) leaves 0
    have hp := zipIdx_flatMap_map (fun (x : Located) => x.finding)
      (fun (f : LoweredProviderField) (j : Nat) =>
        (providerLeafLocated l.schema f).map fun (m, sp) =>
          ({ finding := finding "provider" m, rule := l.providerRules[j]?, span := some sp } : Located))
      (fun f => (providerLeafFindings l.schema f).map (finding "provider"))
      (fun f j => by
        dsimp only
        rw [← providerLeafLocated_messages, List.map_map, List.map_map]
        rfl) l.providers 0
    rw [ht, hp]
    simp only [providerWarnings, Function.comp_def]
    split <;> simp

end Dogwood.Thm.Frontend
