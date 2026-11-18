import Dogwood.Frontend.Diff
import Dogwood.Frontend.Diff.Print
import Dogwood.Frontend.Diff.Schema
import Dogwood.Frontend.Diff.Gaps

/-!
# The differential checker of the Lean frontend

`frontend-diff [--check NAME]… [--bundle TEXT] [--spans] [--diffs N] [--baseline FILE]…
FILE.json…` reads each bundle group that `bridge/ --frontend` exported and runs every check of
`Dogwood.Frontend.Diff` (or only those named with `--check`) on every bundle (or only those whose
name contains `--bundle`), printing a table per group. A baseline lists the expected
disagreements, as `<group> | <bundle> | <check>` lines, the group being the file's name without
its extension. The checker exits with status 1 if a check disagrees in a way no baseline lists,
or a record does not decode, and 2 if a file cannot be read.
-/

open Lean Dogwood.Frontend Dogwood.Frontend.Diff

/-- Every check: the stage checks, then those of the printing, schema and pipeline modules. -/
def allChecks : List Check := Diff.checks ++ Diff.Print.checks ++ Diff.Schema.checks ++ Diff.Gaps.checks

structure Args where
  checks : List String := []
  bundle : Option String := none
  baselines : List String := []
  files : List String := []
  options : Diff.Options := {}

def parseArgs : List String → Args → Except String Args
  | [], a => pure a
  | "--check" :: c :: rest, a => parseArgs rest { a with checks := a.checks ++ [c] }
  | "--bundle" :: t :: rest, a => parseArgs rest { a with bundle := some t }
  | "--baseline" :: f :: rest, a => parseArgs rest { a with baselines := a.baselines ++ [f] }
  | "--spans" :: rest, a => parseArgs rest { a with options := { a.options with spans := true } }
  | "--diffs" :: n :: rest, a => match n.toNat? with
    | some k => parseArgs rest { a with options := { a.options with diffs := k } }
    | none => throw s!"--diffs needs a number, not {n}"
  | f :: rest, a =>
    if f.startsWith "--" then throw s!"unknown flag {f}" else parseArgs rest { a with files := a.files ++ [f] }

def main (argv : List String) : IO UInt32 := do
  let args ← match parseArgs argv {} with
    | .ok a => pure a
    | .error e => IO.eprintln s!"frontend-diff: {e}"; return 2
  if args.files.isEmpty then
    IO.eprintln "usage: frontend-diff [--check NAME]… [--bundle TEXT] [--spans] [--diffs N] [--baseline FILE]… FILE.json…"
    return 2
  let unknown := args.checks.filter fun c => !allChecks.any (·.name == c)
  unless unknown.isEmpty do
    IO.eprintln s!"frontend-diff: unknown checks {unknown}; the checks are {allChecks.map (·.name)}"
    return 2
  let selected := if args.checks.isEmpty then allChecks else allChecks.filter (args.checks.contains ·.name)
  let mut baseline : Baseline := []
  for f in args.baselines do
    baseline := baseline ++ parseBaseline (← IO.FS.readFile f)
  let mut ok := true
  for path in args.files do
    let group := (System.FilePath.mk path).fileStem.getD path
    let text ← match ← (IO.FS.readFile path).toBaseIO with
      | .ok t => pure t
      | .error e => IO.eprintln s!"frontend-diff: {path}: {e}"; return 2
    let json ← match Json.parse text with
      | .ok j => pure j
      | .error e => IO.eprintln s!"frontend-diff: {path}: {e}"; return 2
    let records ← match json.getArr? with
      | .ok a => pure a.toList
      | .error e => IO.eprintln s!"frontend-diff: {path}: {e}"; return 2
    let mut bundles : List BundleExport := []
    for r in records do
      match BundleExport.ofJson r with
      | .ok b =>
        if args.bundle.all fun t => (b.name.splitOn t).length > 1 then bundles := bundles ++ [b]
      | .error e => IO.eprintln s!"frontend-diff: {path}: a record does not decode: {e}"; ok := false
    let (text, good) := report args.options baseline group selected bundles
    IO.println text
    ok := ok && good
  return if ok then 0 else 1
