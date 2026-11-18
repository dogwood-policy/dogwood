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

module

public import Cedar.Thm.Data.Control
public import Lean.Elab.Tactic.Basic

/-!
This file contains general-purpose proof tactics that are shared across
the Cedar theorems and not tied to any specific subsystem.
--/

namespace Cedar.Thm

/--
This tactic simplifies assumptions of the form `do (let x ← expr ...)` by
performing a `cases` and `simp` on `expr`.

Optionally, `as h` names the case-analysis hypothesis (avoiding a subsequent `rename_i`).
-/
syntax "simp_do_let" term (" as " ident)? (" at " ident)? : tactic

macro_rules
| `(tactic| simp_do_let $e as $h:ident $[at $loc:ident]?) =>
  `(tactic| cases $h:ident : $e <;>
    simp only [$h:ident, Except.bind_err, Except.bind_ok, reduceCtorEq] $[at $loc:ident]?)
| `(tactic| simp_do_let $e $[at $loc:ident]?) =>
  `(tactic| cases h' : $e <;>
    simp only [h', Except.bind_err, Except.bind_ok, reduceCtorEq] $[at $loc:ident]?)
