import Dogwood.Frontend.Diff
import Dogwood.Frontend.CedarPrint

/-! # Checks of the differential harness: Cedar's printing of the lowered rules

Each check runs on the crate's own inputs to cedarify (its expanded set, the action schema, the
provider declarations) and compares Cedar's printing of the Lean frontend's rules with the
crate's:

* `est`: each rule's policy JSON (`stages.cedarify.ok.policies[i].est`);
* `cedarText`: each rule's text (`…policies[i].text`);
* `ruleCanonical`: each rule's canonical text (`stages.identity.ok.ruleCanonical`), with the
  crate's enum names;
* `revisions`: each rule's revision, from the Lean canonical texts and the leaf encodings of the
  crate's pinned leaves, against the crate's (`stages.identity.ok.ruleRevisions`, and the public
  pipeline's, `outcome.lowered.ruleRevisions`, when it lowered the bundle).
-/

namespace Dogwood.Frontend.Diff.Print

open Lean (Json)

/-- The field `key` of each rule of the crate's cedarify observable, kept as JSON. -/
def cratePolicies (key : String) (r : Result Json) : Result (List Json) :=
  r.bind fun j => match j.getObjVal? "policies" with
    | .ok (.arr ps) => .ok (ps.toList.map fun p => (p.getObjVal? key).toOption.getD Json.null)
    | _ => .error { stage := .cedarify, category := .export, message := "no policies recorded" }

/-- The crate's inputs to cedarify, and its observable of cedarify as JSON. -/
def cedarifyInputs (b : BundleExport) :
    Except Missing (Surface.PolicySet × CedarSchema.Fragment × Option ProviderDecls.Declarations ×
      Result Json) := do
  let e ← b.stageOk (α := Surface.PolicySet) .expand
  let frag ← b.input (α := CedarSchema.Fragment) "actionSchema"
  let decls ← b.input? (α := ProviderDecls.Declarations) "providers"
  return (e, frag, decls, ← b.stage (α := Json) .cedarify)

/-- The first of two verdicts that is not an agreement, or an agreement. -/
def both (v w : Verdict) : Verdict :=
  match v with
  | .agree | .agreeUpToRenaming => w
  | _ => v

def checks : List Check := [
  { name := "est", owner := "gaps", run := fun o b => withInputs (cedarifyInputs b)
      fun (e, frag, decls, crate) =>
      compare o ((Cedarify.cedarifyFull e frag decls).map fun w => CedarPrint.policiesEst e w.cedar)
        (cratePolicies "est" crate) },
  { name := "cedarText", owner := "gaps", run := fun o b => withInputs (cedarifyInputs b)
      fun (e, frag, decls, crate) =>
      compare o ((Cedarify.cedarifyFull e frag decls).map fun w =>
          (CedarPrint.policiesText e w.cedar).map Json.str)
        (cratePolicies "text" crate) },
  { name := "ruleCanonical", owner := "gaps", run := fun o b => withInputs (do
      let e ← b.stageOk (α := Surface.PolicySet) .expand
      let decls ← b.input? (α := ProviderDecls.Declarations) "providers"
      let c ← b.stageOk (α := Cedarified) .cedarify
      return (e, decls, c, ← b.stage (α := Identity) .identity)) fun (e, decls, c, crate) =>
      compare o (CedarPrint.ruleCanonical e decls c.enumNames) (crate.map (·.ruleCanonical)) },
  { name := "revisions", owner := "gaps", run := fun o b => withInputs (do
      let e ← b.stageOk (α := Surface.PolicySet) .expand
      let decls ← b.input? (α := ProviderDecls.Declarations) "providers"
      let c ← b.stageOk (α := Cedarified) .cedarify
      let pinned ← b.stageOk (α := List Surface.Temporal.Condition) .injectPins
      return (e, decls, c, pinned, ← b.stage (α := Identity) .identity))
      fun (e, decls, c, pinned, crate) =>
      let lean : Result (List String) := do
        let canonical ← CedarPrint.ruleCanonical e decls c.enumNames
        let leaves ← RuleIdentity.leaves c (withConditions c.contextFields pinned)
        pure (RuleIdentity.ruleRevisions canonical leaves)
      let staged := compare o lean (crate.map (·.ruleRevisions))
      let pipeline := match b.crateOutcome with
        | .ok (.lowered r) => compare o lean (.ok r.ruleRevisions)
        | _ => .agree
      both staged pipeline }
]

end Dogwood.Frontend.Diff.Print
