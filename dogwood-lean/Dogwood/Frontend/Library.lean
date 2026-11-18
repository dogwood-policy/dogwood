import Dogwood.Frontend.Ffi
import Dogwood.Frontend.Driver
import Dogwood.Frontend.Pipeline
import Dogwood.Frontend.Validate
import Dogwood.Frontend.Conformance
import Dogwood.Frontend.Json
import Dogwood.Frontend.Export
import Dogwood.Frontend.Identity
import Dogwood.Spec.EventSchema

/-!
# The Lean frontend's library

The root of the static library the `dogwood-language` crate links with its `lean-frontend`
feature (the lakefile's `frontendFfi` target): the library holds this module and every module
it imports, transitively, except the elaborator-only modules of Batteries the lakefile names.

Besides the crate's own entry points (`Dogwood.Frontend.Ffi`), the module imports the parts of
the frontend and of the specification that a dependent crate's own Lean code builds on: the
pipeline (`Driver`, `Pipeline`), the validator (`Validate`), the projection onto the
specification (`Conformance`), the JSON encoding of the parsers' outputs (`Json`, `Export`), the
identity hashes (`Identity`) and the event schema of the specification (`Spec.EventSchema`).

The crate's runtime initializes this module, and so every module of the library, once per
process, before it ends Lean's initialization (`dogwood_lean_init` in
`dogwood-language/src/lean_frontend/shim.c`). A dependent that compiles its own Lean modules
against the library may import any module of the library; when it initializes its own root
module afterwards, the initializers of the library's modules have already run, and are no-ops.
-/
