import Dogwood.Conformance.Json

/-!
# The conformance checker

`conformance [--baseline FILE] [--write-baseline FILE] [--write-categories FILE] FILE.json…`
reads each bundle group that `bridge/` exported, compares every bundle with the specification
(`Dogwood.Conformance.Harness`), and prints a report per group. The baseline lists the
disagreements that are expected, as `<group> | <bundle> | <key>` lines, the group being the
file's name without its extension. The checker exits with status 1 if a lowered bundle disagrees
with the specification in a way the baseline does not list, and 2 if no file is given or a file
cannot be read or decoded. `--write-baseline` writes the baseline that lists every disagreement
of the run. `--write-categories` writes, for each lowered bundle, one JSON line with the
categories of the specification's findings and of the crate's, and the crate's findings no
category covers, so that a summary can tell a bundle one side accepts from one both reject for
different reasons.
-/

open Lean Dogwood.Conformance

/-- One JSON line per lowered bundle of a group: the categories of each side's findings, and
the messages of the crate's error findings no category covers. -/
def categoryLines (group : String) (cases : List Case) : List String :=
  cases.filterMap fun c =>
    match c.outcome with
    | .lowered l =>
      let names := fun (fs : List Dogwood.Eval.Finding) => Json.arr (fs.map (Json.str ·.name)).toArray
      some (Json.mkObj [("group", group), ("bundle", c.name), ("spec", names l.specCategories),
        ("crate", names l.crateCategories),
        ("uncategorized", Json.arr ((l.uncategorized.map (·.message)).map Json.str).toArray),
        ("findings", Json.arr ((l.crateFindings.filter (!·.warning)).map fun f =>
          Json.str s!"{f.code}: {f.message.take 300}").toArray)]).compress
    | .rejected _ _ => none

/-- Check one group; whether every disagreement is one the baseline lists, the baseline lines
of its disagreements, and its category lines. -/
def check (baseline : Baseline) (path : System.FilePath) :
    IO (Bool × List String × List String) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let cases ← IO.ofExcept (fromJson? (α := List Case) json)
  let group := path.fileStem.getD path.toString
  let r := report (baseline.forGroup group) cases
  IO.println s!"== {group}\n{r.render}"
  return (r.unexpected.isEmpty, baselineLines group cases, categoryLines group cases)

def main (args : List String) : IO UInt32 := do
  let rec parse : List String → Option String → Option String → Option String → List String →
      Option String × Option String × Option String × List String
    | "--baseline" :: f :: rest, _, w, c, fs => parse rest (some f) w c fs
    | "--write-baseline" :: f :: rest, b, _, c, fs => parse rest b (some f) c fs
    | "--write-categories" :: f :: rest, b, w, _, fs => parse rest b w (some f) fs
    | f :: rest, b, w, c, fs => parse rest b w c (fs ++ [f])
    | [], b, w, c, fs => (b, w, c, fs)
  let (baselineFile, writeFile, categoriesFile, files) := parse args none none none []
  let baseline ← match baselineFile with
    | some f => do pure (parseBaseline (← IO.FS.readFile f))
    | none => pure []
  if files.isEmpty then
    IO.eprintln "usage: conformance [--baseline FILE] [--write-baseline FILE] [--write-categories FILE] FILE.json…"
    return 2
  let mut ok := true
  let mut lines : List String := []
  let mut cats : List String := []
  for a in files do
    try
      let (good, ls, cs) ← check baseline a
      ok := good && ok
      lines := lines ++ ls
      cats := cats ++ cs
    catch e =>
      IO.eprintln s!"conformance: {a}: {e}"
      return (2 : UInt32)
  if let some w := writeFile then
    IO.FS.writeFile w (String.intercalate "\n" lines ++ "\n")
  if let some w := categoriesFile then
    IO.FS.writeFile w (String.intercalate "\n" cats ++ "\n")
  return if ok then 0 else 1
