import Lake
open Lake DSL

/-
The Cedar formal specification (cedar-lean), pinned to the release that
matches the `cedar-policy` / `cedar-policy-core` 4.14.0 the in-tree
`dogwood-language` crate builds against. `bridge/Cargo.toml` pins the same
release on the Cargo side, and `conformance/run.sh` checks that they agree.
-/
require Cedar from git
  "https://github.com/cedar-policy/cedar-spec" @ "v4.14.0" / "cedar-lean"

package DogwoodSpec where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Dogwood

/-- Conformance checks against the in-tree crate: the harness, the JSON form of
the bundles `bridge/` exports, and the checker (see `conformance/README.md`).
Not a default target. -/
lean_lib DogwoodConformance where
  globs := #[.submodules `Dogwood.Conformance]

/-- The conformance checker, `lake exe conformance FILE.json…`. Building it
compiles C, so it is not a default target either. -/
lean_exe conformance where
  root := `Dogwood.Conformance.Main

/-- The differential checker of the Lean frontend against the crate's frontend export,
`lake exe frontend-diff FILE.json…` (see `conformance/frontend-run.sh`). Not a default target. -/
lean_exe «frontend-diff» where
  root := `Dogwood.Frontend.DiffMain

/-- The modules of Batteries that only extend the elaborator: tactics, linters, code actions,
commands and attributes. The frontend runs none of their code; they are in its import closure
because the data modules of Batteries, which cedar-lean imports, import them for their proofs.
Their initializers register elaborator state (options, environment extensions, attributes),
and they import Lean's elaborator, whose initializers are what keeps most of `libLean.a` linked.
`Batteries.Recycling.MonadSatisfying` is with them: it defines `SatisfiesM`, which the data
modules use in their proofs only, and its `MonadSatisfying` instances call `Batteries.Lean`. -/
def elaboratorOnly : List Lean.Name :=
  [`Batteries.Tactic, `Batteries.Linter, `Batteries.CodeAction, `Batteries.Util, `Batteries.Lean,
   `Batteries.Recycling.MonadSatisfying]

/-- The Lean frontend as one static library, `.lake/build/lib/libDogwoodFrontendFfi.a`, for the
`dogwood-language` crate's `lean-frontend` feature: the object files of
`Dogwood.Frontend.Library` (the library's root: the C entry points of `Dogwood.Frontend.Ffi` and
the modules a dependent crate's own Lean code builds on) and of every module it imports
transitively, from this package and from its dependencies (cedar-lean, Batteries), except the
modules `elaboratorOnly` names, whose imports are not followed either. For each of those that a kept module imports, the library holds an
initializer that does nothing, of each of its three kinds (`frontendFfi/stubs.c`), so that the kept modules' initializers
do not reach the elaborator's. Every symbol the kept modules use is still resolved at link time:
a kept module that used a definition of a left-out one would not link. Lean's own `Init`, `Std`
and `Lean` are not in the library: they come from the toolchain's static libraries, which the
crate's build merges with this one. `lake build frontendFfi`; it compiles C, so it is not a
default target. -/
target frontendFfi pkg : System.FilePath := do
  let some root ← findModule? `Dogwood.Frontend.Library
    | error "the module `Dogwood.Frontend.Library` is not in the workspace"
  let leftOut (mod : Module) := elaboratorOnly.any (·.isPrefixOf mod.name)
  let mut kept : Array Module := #[]
  let mut stubbed : Array Module := #[]
  let mut seen : Lean.NameSet := {}
  let mut todo := #[root]
  while h : 0 < todo.size do
    let mod := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains mod.name then continue
    seen := seen.insert mod.name
    if leftOut mod then
      stubbed := stubbed.push mod
    else
      kept := kept.push mod
      todo := todo ++ (← (← mod.imports.fetch).await)
  let mut objs := #[]
  for mod in kept do
    for facet in mod.nativeFacets false do
      objs := objs.push (← facet.fetch mod)
  let dir := pkg.buildDir / "frontendFfi"
  IO.FS.createDirAll dir
  -- Lean 4.34 gives each module three initializers, `initialize_`, `runtime_initialize_` and
  -- `meta_initialize_`, and an importing module calls the first two of each import.
  let stubs := String.join (stubbed.toList.flatMap fun mod =>
    ["", "runtime_", "meta_"].map fun kind =>
      s!"LEAN_EXPORT lean_object *{kind}initialize_{mod.dynlibName}(uint8_t builtin) \{\n" ++
      "  (void)builtin;\n  return lean_io_result_mk_ok(lean_box(0));\n}\n")
  let src := dir / "stubs.c"
  let text := "/* Initializers of the modules the library leaves out (lakefile `elaboratorOnly`). */\n" ++
    "#include <lean/lean.h>\n" ++ stubs
  -- Rewritten only when it changes, so that the object's trace is stable.
  if (← (IO.FS.readFile src).toBaseIO).toOption != some text then
    IO.FS.writeFile src text
  let stubO ← buildO (dir / "stubs.o") (← inputTextFile src)
    #["-I", (← getLeanIncludeDir).toString, "-fPIC"] #["-O2"] (← getLeanCc)
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "DogwoodFrontendFfi") (objs.push stubO)
