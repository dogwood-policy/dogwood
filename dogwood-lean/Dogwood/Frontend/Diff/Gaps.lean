import Dogwood.Frontend.Diff
import Dogwood.Frontend.Pipeline

/-!
# Checks of the differential harness: stable ids and the one-call pipeline

* `assignIds`: the stable ids (`Ids.assignIds`) of the crate's expanded set, from the `@id`
  annotations and from the bundle's explicit ids, against the crate's `assign_ids`;
* `lowerAll`: `Driver.lowerAll` on the bundle's parsed inputs (with its ids and distincter)
  against the crate's public pipeline on its sources: the whole lowered set
  (`outcome.lowered.full`), or the rejection;
* `lowerAllFindings`: the categories of the validator's findings on the set `lowerAll` lowers,
  against the crate's validator on its own lowering (as `validate` compares them);
* `lowerAllMessages`: the same findings other than Cedar's, by code and message, the errors in
  order and the warnings in order (Cedar's own findings are cedar-lean's text on the Lean side);
* `lowerMany`: `Driver.lowerManyAll` on several policy sets against the crate's `lower_many`.

An error is compared by its category, its message (except Cedar's own messages, and a parser's,
which the parsers' outputs carry from the export), the entry it belongs to, and, for a stable-id
error, its kind, policy and id; and by its span with `--spans`.
-/

namespace Dogwood.Frontend.Diff.Gaps

open Lean (Json FromJson ToJson fromJson? toJson)

/-- A key of an object, `null` when absent. -/
def getD (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD .null

/-- A result, encoded as the export records one. -/
def resultJson {α : Type} [ToJson α] : Result α → Json
  | .ok v => Json.mkObj [("ok", toJson v)]
  | .error e => Json.mkObj [("error", toJson e)]

/-- The parts of an error the checks compare. A parser's error is the export's own (the crate's
public pipeline reports a parser's errors without one span). -/
def errorParts (o : Options) (messages : Bool) (e : Json) : Json :=
  Json.mkObj ([("category", getD e "category"), ("entry", getD e "entry"),
    ("policyId", getD e "policyId")] ++
    (if messages then [("message", getD e "message")] else []) ++
    (if o.spans && getD e "category" != .str "parse" then [("span", getD e "span")] else []))

/-- Whether an error's message is the crate's own for both sides: not Cedar's (a schema Cedar
rejects, a policy set Cedar rejects) and not a parser's (whose message the export writes). -/
def comparesMessage (crate : Json) : Bool :=
  match getD crate "category" with
  | .str "parse" | .str "cedarSchema" | .str "policySet" => false
  | _ => true

/-- Compare two encoded results: an error by its parts, a value by its encoding. -/
def compareJson (o : Options) (lean crate : Json) (messages : Bool := true) : Verdict :=
  match getD lean "error", getD crate "error" with
  | .null, .null =>
    let a := prep o (getD lean "ok")
    let b := prep o (getD crate "ok")
    if a == b then .agree else .disagree ((firstDiff "" a b).getD "the encodings differ")
  | .null, e => .disagree s!"Lean ok ≠ crate error {shorten e}"
  | e, .null => .disagree s!"Lean error {shorten e} ≠ crate ok"
  | e, e' =>
    let a := errorParts o messages e
    let b := errorParts o messages e'
    if a == b then .agree else .disagree s!"Lean {shorten e} ≠ crate {shorten e'}"

/-- The crate's public pipeline's outcome, as a result: the rejection, or the whole lowered
set. -/
def outcomeResult (outcome : Json) : Except Missing Json :=
  match outcome.getObjVal? "rejected", outcome.getObjVal? "lowered" with
  | .ok e, _ => pure (Json.mkObj [("error", e)])
  | _, .ok l => match l.getObjVal? "full" with
    | .ok f => pure (Json.mkObj [("ok", f)])
    | .error _ => throw (.undecodable "outcome" "no whole lowered set")
  | _, _ => throw (.notRun "outcome")

/-- The Lean side's lowered set, out of its outcome. -/
def leanLowered (out : Json) : Json :=
  match getD out "error" with
  | .null => Json.mkObj [("ok", getD (getD out "ok") "lowered")]
  | e => Json.mkObj [("error", e)]

/-- The categories of an encoded list of findings, sorted. -/
def categories (fs : List Conformance.CrateFinding) : List String :=
  ((fs.filterMap Conformance.crateCategory).map (·.name)).eraseDups.mergeSort
    (fun a b => decide (a ≤ b))

/-- The findings other than Cedar's, by code and message: the errors, then the warnings, each in
order. -/
def messages (fs : List Conformance.CrateFinding) : List String × List String :=
  let text := fun (f : Conformance.CrateFinding) => f.code ++ ": " ++ f.message
  let own := fs.filter (·.code != "cedar")
  ((own.filter (!·.warning)).map text, (own.filter (·.warning)).map text)

/-- The first position at which two lists of messages differ. -/
def firstMessageDiff (what : String) : List String → List String → Option String
  | [], [] => none
  | a :: _, [] => some s!"{what}: only Lean reports `{a.take 200}`"
  | [], b :: _ => some s!"{what}: only the crate reports `{b.take 200}`"
  | a :: as, b :: bs =>
    if a == b then firstMessageDiff what as bs
    else some s!"{what}: Lean `{a.take 300}` ≠ crate `{b.take 300}`"

def checks : List Check := [
  { name := "assignIds", owner := "gaps", run := fun o b => withInputs (do
      let e ← b.stageOk (α := Surface.PolicySet) .expand
      let st ← b.stageOk (α := Json) .assignIds
      return (e, st)) fun (e, st) =>
      let annotation := compareJson o (resultJson (Ids.assignIds e.policies .annotation)) (getD st "annotation")
      let explicit := match getD st "explicit", Driver.idSourceOfJson (getD b.inputs "ids") with
        | .null, _ => Verdict.agree
        | crate, .ok src => compareJson o (resultJson (Ids.assignIds e.policies src)) crate
        | _, .error why => .undecodable why
      match annotation, explicit with
      | .agree, .agree => .agree
      | .disagree d, _ => .disagree s!"annotation: {d}"
      | _, .disagree d => .disagree s!"explicit: {d}"
      | .undecodable w, _ | _, .undecodable w => .undecodable w
      | v, _ => v },
  { name := "lowerAll", owner := "gaps", run := fun o b =>
      if b.many != .null then .skipped "several policy sets" else
      withInputs (outcomeResult b.outcome) fun crate =>
      compareJson o (leanLowered (Driver.lowerAll b.inputs)) crate
        (messages := comparesMessage (getD crate "error")) },
  { name := "lowerAllFindings", owner := "gaps", run := fun _ b =>
      if b.many != .null then .skipped "several policy sets" else
      if getD b.inputs "ids" != .null || getD b.inputs "distincter" != .null then
        .skipped "lowered with ids or a distincter"
      else withInputs (do
        match ← b.conformanceOutcome with
        | .lowered c => return c.crateFindings
        | .rejected st m => throw (.notRun s!"conformance record (rejected at {st}: {m.take 80})"))
        fun crate =>
        let out := Driver.lowerAll b.inputs
        match getD (getD (getD out "ok") "findings") "ok" with
        | .null => .disagree s!"Lean has no findings: {shorten out}"
        | fs => match fromJson? (α := List Conformance.CrateFinding) fs with
          | .error why => .undecodable why
          | .ok lean =>
            if categories lean == categories crate then .agree
            else .disagree s!"categories: Lean {categories lean} ≠ crate {categories crate}" },
  { name := "lowerAllMessages", owner := "gaps", run := fun _ b =>
      if b.many != .null then .skipped "several policy sets" else
      if getD b.inputs "ids" != .null || getD b.inputs "distincter" != .null then
        .skipped "lowered with ids or a distincter"
      else withInputs (do
        match ← b.conformanceOutcome with
        | .lowered c => return c.crateFindings
        | .rejected st m => throw (.notRun s!"conformance record (rejected at {st}: {m.take 80})"))
        fun crate =>
        let out := Driver.lowerAll b.inputs
        match getD (getD (getD out "ok") "findings") "ok" with
        | .null => .disagree s!"Lean has no findings: {shorten out}"
        | fs => match fromJson? (α := List Conformance.CrateFinding) fs with
          | .error why => .undecodable why
          | .ok lean =>
            let (le, lw) := messages lean
            let (ce, cw) := messages crate
            match (firstMessageDiff "errors" le ce).or (firstMessageDiff "warnings" lw cw) with
            | none => .agree
            | some d => .disagree d },
  { name := "lowerMany", owner := "gaps", run := fun o b =>
      if b.many == .null then .skipped "one policy set" else
      let inputs := getD b.many "inputs"
      withInputs (outcomeResult (getD b.many "outcome")) fun crate =>
      compareJson o (leanLowered (Driver.lowerManyAll inputs)) crate
        (messages := comparesMessage (getD crate "error")) }
]

end Dogwood.Frontend.Diff.Gaps
