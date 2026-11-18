/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Lake
open Lake DSL

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require "leanprover" / "doc-gen4" @ git "v4.34.1"

require "leanprover-community" / "batteries" @ git "v4.34.0"

package Cedar

@[default_target]
lean_lib Cedar where
  defaultFacets := #[LeanLib.staticFacet]

@[default_target]
lean_lib SymCC where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib Cedar.SymCC where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib DiffTest where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib UnitTest where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib SymTest where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib Protobuf where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib CedarProto where
  defaultFacets := #[LeanLib.staticFacet]

lean_lib CedarFFI where
  defaultFacets := #[LeanLib.staticFacet]

lean_exe CedarUnitTests where
  root := `UnitTest.Main

lean_exe CedarSymTests where
  root := `SymTest.Main

lean_exe Cli where
  root := `Cli.Main

-- Check that a .lean file imports all files in its corresponding directory
partial def checkThmFile (module : String) (paths : List System.FilePath) : IO Nat := do
  let path := paths.head!
  let dir := path.withExtension ""
  if ← dir.isDir then
    let contents ← paths.mapM IO.FS.readFile
    let mod_files ← dir.readDir
    let mut exitCode := 0

    for file in mod_files.toList do
      let file_name := file.fileName
      if file_name.endsWith ".lean" then
        let subModule := s!"{module}.{file_name.dropEnd 5}"
        let expectedImport := s!"import {subModule}\n"
        if contents.all λ content => (content.replace expectedImport "" == content) then
          IO.println s!"{path} missing import: {expectedImport}"
          exitCode := 1
        let subExitCode ← checkThmFile subModule [dir / file_name]
        if subExitCode != 0 then
          exitCode := subExitCode

    return exitCode
  else
    return 0

/--
Check that Cedar.Thm imports all top level proofs recursively.

USAGE:
  lake run checkThm
  lake lint
-/
@[lint_driver]
script checkThm do
  let exitCode ← checkThmFile "Cedar.Thm" [⟨"Cedar/Thm.lean"⟩, ⟨"SymCC.lean"⟩]
  return ⟨exitCode⟩
