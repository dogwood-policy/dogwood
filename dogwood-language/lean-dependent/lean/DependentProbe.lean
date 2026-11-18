import Dogwood.Frontend.Pipeline
import Std.Data.HashMap

/-!
# A dependent crate's own Lean code over the Lean frontend's library

The test crate `dogwood-lean-dependent` compiles this module against the Lean library of the
`dogwood-language` crate (its `.olean` files, which that crate's build publishes), and links it
with that crate's archive, which holds the library's code and the one Lean runtime of the
process.

`run` lowers a policy set with the library's pipeline (`Driver.lowerFull`), from the JSON the
crate's `frontend_export::inputs` returns, and answers the lowered set's Cedar part as Cedar
prints it (`Full.cedar`), with the number of rules of each effect, counted in a hash map of Lean's
standard library (code the frontend's library does not use itself). `lower` answers the whole
lowered set (`Full.toJson`), or the pipeline's outcome, which the crate rebuilds its lowered set
from (`frontend::lowered_from_lean`).
-/

namespace DependentProbe

open Lean (Json)
open Dogwood.Frontend.Driver

/-- The name of a rule's effect. -/
def effectName : Cedar.Spec.Effect → String
  | .permit => "permit"
  | .forbid => "forbid"

/-- The number of rules of each effect, in the order of the effects' names. -/
def effects (f : Full) : Json :=
  let counts : Std.HashMap String Nat := f.rules.foldl (init := {}) fun m (p, _) =>
    m.insert (effectName p.effect) (m.getD (effectName p.effect) 0 + 1)
  let sorted := counts.toList.mergeSort fun a b => decide (a.1 ≤ b.1)
  Json.mkObj (sorted.map fun (k, n) => (k, Lean.toJson n))

/-- Lower the policy set the export's inputs `input` describe: `{"ok": {"cedar", "effects"}}`,
or `{"error": message}`. -/
def run (input : String) : String :=
  let reply : Json := match Json.parse input with
    | .error why => Json.mkObj [("error", Json.str s!"not JSON: {why}")]
    | .ok j =>
      match sharedOfJson j, entryOfJson j with
      | .ok s, .ok e =>
        match lowerFull s e with
        | .ok f => Json.mkObj [("ok", Json.mkObj [("cedar", f.cedar), ("effects", effects f)])]
        | .error (err, _) => Json.mkObj [("error", Json.str err.message)]
      | .error why, _ | _, .error why => Json.mkObj [("error", Json.str why)]
  reply.compress

/-- The C entry point: `run` on an owned string. -/
@[export dogwood_dependent_probe]
def probe (input : String) : IO String := pure (run input)

/-- The pipeline's inputs in the export's inputs `input`: the shared inputs, and the one entry
(`inputs`), or the entries (`inputs_many`, with `entries`). -/
def inputsOf (input : String) : Except String (SharedInput × Option EntryInput × List EntryInput) := do
  let j ← Json.parse input
  let s ← sharedOfJson j
  match j.getObjVal? "entries" with
  | .ok es => return (s, none, ← (← es.getArr?).toList.mapM entryOfJson)
  | .error _ => return (s, some (← entryOfJson j), [])

/-- Lower the policy set, or the sets, the export's inputs `input` describe with the library's
pipeline (`lowerFull`, or `lowerManyFull`), and answer the outcome as the library encodes it
(`outcomeToJson`: the lowered set and the validator's findings, or the error), or, with `bare`,
the lowered set alone (`Full.toJson`): what the language crate's `frontend::lowered_from_lean`
decodes. An input that does not decode is a `bug`. -/
def lower (bare : Bool) (input : String) : String :=
  match inputsOf input with
  | .error why => (Json.mkObj [("bug", Json.str why)]).compress
  | .ok (s, one, many) =>
    let r := match one with
      | some e => lowerFull s e
      | none => lowerManyFull s many
    match bare, r with
    | true, .ok f => f.toJson.compress
    | _, _ => (outcomeToJson r).compress

/-- The C entry points: `lower` on an owned string. -/
@[export dogwood_dependent_lower]
def lowerOutcome (input : String) : IO String := pure (lower false input)

@[export dogwood_dependent_lower_bare]
def lowerBare (input : String) : IO String := pure (lower true input)

end DependentProbe
