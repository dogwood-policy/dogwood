import Dogwood.Frontend.Types
import Dogwood.Conformance.Harness
import Dogwood.Frontend.Validate.Cedar
import Dogwood.Frontend.Validate.Assumptions

/-!
# The validator (WP6)

The crate's `Validator::validate` (`validate.rs`, `validate_impl`) on a lowered set, in its
order:

1. Cedar's validator on the lowered rules, against the augmented schema
   (`Validate.cedarFindings`), and the schema's well-formedness as the specification requires it
   (`Validate.schemaFindings`);
2. the reads of the request context lowering does not preserve (`Validate.contextFindings`);
3. the temporal dialect on each temporal leaf, as authored after pin injection, with the facts
   its position establishes (`Validate.leafFindings`);
4. the provider dialect on each provider leaf (`Validate.providerLeafFindings`), and its warnings
   of a declared type that falls back to `String`, once per run of leaves from one source
   (`Validate.providerWarnings`);
5. one warning when a leaf uses arithmetic, which the build of the crate the conformance run uses
   accepts (`experimental-arithmetic`).

A finding is `{code, message, warning}`, with the crate's codes (`cedar`, `schema`, `context`,
`temporal`, `provider`); the harness compares the categories of the two sides' findings
(`Conformance.crateCategory`). The lowered set is valid for the crate when no finding is an
error.

A temporal leaf is checked on its specification form (`Condition.toFormula`); a leaf without one
(a transient form that macro expansion removes, an array constant that lowering rejects) is not
a lowered set's, and is an error of this stage.
-/

namespace Dogwood.Frontend.Validate

open Dogwood.Spec.Temporal (Formula)

mutual

def hasArithF : Formula → Bool
  | .and φ ψ | .since φ _ ψ => hasArithF φ || hasArithF ψ
  | .not φ | .formerly _ φ | .previous _ φ | .exist _ φ => hasArithF φ
  | .pred _ _ args => hasArithArgs args
  | .cmp _ l r => hasArithT l || hasArithT r
  | .tp _ => false

def hasArithT : Dogwood.Spec.Temporal.Term → Bool
  | .arith _ _ _ => true
  | .agg (.count _ body) | .agg (.sum _ _ body) => hasArithF body
  | _ => false

def hasArithArgs : List (Dogwood.Spec.Path × Dogwood.Spec.Temporal.Term) → Bool
  | [] => false
  | (_, t) :: args => hasArithT t || hasArithArgs args

end

/-- The ids of an enum entity type in the order the augmented schema declares them. -/
def fragmentEnum (frag : CedarSchema.Fragment) (ety : Cedar.Spec.EntityType) : Option (List String) :=
  let ns : Option String := if ety.path.isEmpty then none else some ("::".intercalate ety.path)
  match frag.find? (·.1 == ns) with
  | some (_, nd) =>
    match nd.entityTypes.lookup ety.id with
    | some ⟨.enum choices, _, _⟩ => some choices
    | _ => none
  | none => none

/-- The checking context of a temporal leaf of the lowered set. -/
def leafCtx (l : Lowered) (facts : List (String × List Dogwood.Spec.Temporal.Guard))
    (f : TemporalField) : LeafCtx where
  schema := l.schema
  events := l.eventSchema
  cap := l.eventSchema.maxWindow.seconds
  capText := renderWindow ⟨l.eventSchema.maxWindow.amount.toInt, l.eventSchema.maxWindow.unit⟩
  horizonCap := l.eventSchema.maxHorizon.map (·.seconds)
  horizonUnit := (l.eventSchema.maxHorizon.map (·.unit)).getD .hours
  horizonCapText :=
    (l.eventSchema.maxHorizon.map fun h => renderWindow ⟨h.amount.toInt, h.unit⟩).getD ""
  targets := f.targetActions.filterMap fun (ns, id) => action? l.schema ns id
  principal := f.principal
  resource := f.resource
  facts := (facts.lookup f.id).getD []
  declaredEnum := fragmentEnum l.augmentedSchema

/-- The leaves of the lowered set, in their specification form. -/
def leafFormulas (l : Lowered) : Result (List (TemporalField × Formula)) :=
  l.temporal.mapM fun f =>
    match f.condition.condition.toFormula with
    | .ok φ => pure (f, φ)
    | .error e =>
      throw { stage := .validate, category := .other
              message := s!"temporal leaf `{f.id}` has no specification form: {e}" }

/-- The runs of consecutive leaves whose rules come from one source (crate `source_runs`):
`leafRules` gives each leaf's rule, `sources` each rule's source (none: one source). -/
def sourceRuns {α : Type} (sources : List Nat) (leafRules : List Nat) (leaves : List α) :
    List (List α) :=
  let tagged := (leaves.zip (leafRules ++ List.replicate leaves.length 0)).map fun (x, k) =>
    (x, sources[k]?.getD 0)
  (tagged.splitBy fun a b => a.2 == b.2).map (·.map (·.1))

/-- A finding, with the rule it is about (its index in the lowered set) and its span in that
rule's source, when the crate reports it at one: a temporal leaf's findings at the leaf (the
crate's are at the offending node inside it, which the specification form of the leaf does not
locate), a provider leaf's at the invocation or the method (as the crate's), Cedar's at the rule
(the crate's at the subexpression Cedar's diagnostic labels, which cedar-lean's do not carry). -/
structure Located where
  finding : Conformance.CrateFinding
  rule : Option Nat := none
  span : Option Span := none

/-- `xs` without each element whose key an earlier element already has. -/
def firstOccurrencesBy {α : Type} (key : α → String) (xs : List α) : List α :=
  xs.foldl (init := []) fun acc x => if acc.any (key · == key x) then acc else acc ++ [x]

/-- The provider dialect's warnings, located at the invocation of the first leaf of its run that
reports each: each leaf's fallback warnings, once per run of leaves from one source (crate
`ProviderDialect::validate`, its `warned` set). -/
def providerWarningsLocated (l : Lowered) : List Located :=
  let leaves := l.providers.zipIdx.map fun (f, j) => (f, l.providerRules[j]?)
  (sourceRuns l.ruleSources l.providerRules leaves).flatMap fun run =>
    firstOccurrencesBy (·.finding.message) (run.flatMap fun (f, rule) =>
      (leafFallbacks f).map fun m =>
        { finding := finding "provider" m true, rule,
          span := some (rebaseBody f.bodyBase f.invocation.span) })

/-- The provider dialect's warnings (`providerWarningsLocated`). -/
def providerWarnings (l : Lowered) : List Conformance.CrateFinding :=
  (providerWarningsLocated l).map (·.finding)

/-- Every finding of the crate's validator on the lowered set, with its dialect code
(`temporal`, `provider`, `cedar`, `schema`, `context`), its message, and whether it is a warning. -/
def validate (l : Lowered) : Result (List Conformance.CrateFinding) := do
  let leaves ← leafFormulas l
  let facts := loweredFacts l
  let temporal := leaves.flatMap fun (f, φ) =>
    (leafFindings (leafCtx l facts f) φ).map (finding "temporal")
  let providers := l.providers.flatMap fun f =>
    (providerLeafFindings l.schema f).map (finding "provider")
  let warnings := providerWarnings l ++ if leaves.any (hasArithF ·.2) then
      [finding "temporal" "arithmetic operators are experimental and may change in a future release" true]
    else []
  return cedarFindings l ++ schemaFindings l ++ contextFindings l ++ temporal ++ providers ++ warnings

/-- The rule a finding of Cedar's validator is about. -/
def cedarRule (l : Lowered) : Cedar.Validation.ValidationError → Option Nat
  | .typeError pid _ | .levelError pid | .impossiblePolicy pid => l.ruleIds.idxOf? pid

/-- `cedarFindings`, located at the rule. -/
def cedarLocated (l : Lowered) : List Located :=
  if l.policies.isEmpty then []
  else if (incompleteNames l).isEmpty then
    match Cedar.Validation.validate (cedarPolicies l) l.schema with
    | .ok () => []
    | .error e =>
      { finding := finding "cedar" (cedarMessages l e).1, rule := cedarRule l e } ::
        (cedarMessages l e).2.map fun m => { finding := finding "cedar" m, rule := cedarRule l e }
  else (incompleteFindings l).zipIdx.map fun (f, i) => { finding := f, rule := some i }

/-- `validate`, each finding located where the crate reports it, as far as the lowered set
locates it (`Located`): the same findings (`Thm.Frontend.validateLocated_findings`). -/
def validateLocated (l : Lowered) : Result (List Located) := do
  let leaves ← leafFormulas l
  let facts := loweredFacts l
  let plain := fun (fs : List Conformance.CrateFinding) => fs.map fun f => ({ finding := f } : Located)
  let temporal := leaves.zipIdx.flatMap fun ((f, φ), j) =>
    (leafFindings (leafCtx l facts f) φ).map fun m =>
      ({ finding := finding "temporal" m, rule := l.temporalRules[j]?,
         span := some f.condition.span } : Located)
  let providers := l.providers.zipIdx.flatMap fun (f, j) =>
    (providerLeafLocated l.schema f).map fun (m, sp) =>
      ({ finding := finding "provider" m, rule := l.providerRules[j]?, span := some sp } : Located)
  let arith : List Located := if leaves.any (hasArithF ·.2) then
      [{ finding := finding "temporal" "arithmetic operators are experimental and may change in a future release" true
         rule := (leaves.findIdx? (hasArithF ·.2)).bind (l.temporalRules[·]?)
         span := (leaves.find? (hasArithF ·.2)).map (·.1.condition.span) }]
    else []
  return cedarLocated l ++ plain (schemaFindings l) ++ plain (contextFindings l) ++ temporal ++
    providers ++ (providerWarningsLocated l ++ arith)

/-- The lowered set passes validation: no finding is an error. -/
def accepts (l : Lowered) : Bool :=
  match validate l with
  | .ok fs => fs.all (·.warning)
  | .error _ => false

end Dogwood.Frontend.Validate
