import Dogwood.Frontend.Pipeline

/-!
# The C entry points of the Lean frontend

The `dogwood-language` crate, built with its `lean-frontend` feature, links this module and
everything it imports as one static library (the lakefile's `frontendFfi` target) and calls the
`@[export]` functions below through a small C shim (`dogwood-language/src/lean_frontend/shim.c`).
The crate encodes the parsers' outputs, calls an entry point, and decodes the result into its
own types.

Each entry point is a one-call function of `Dogwood.Frontend.Pipeline` on JSON text:

* `dogwood_frontend_lower`: `Driver.lowerAllStr`, one policy set parsed, given its ids, lowered
  (under its distincter, if any) and validated (crate `ParsedPolicySet::parse`, `with_ids`,
  `lower` or `lower_with_distincter`, `Validator::validate`);
* `dogwood_frontend_lower_many`: `Driver.lowerManyAllStr`, several policy sets lowered
  together (crate `lower_many`) and validated;
* `dogwood_frontend_parse`: `Driver.parseAllStr`, the first phase alone, for the stable ids
  (crate `with_ids`).

The JSON formats are `Pipeline`'s: the parsers' outputs in the encoding of the crate's frontend
export, and the whole lowered set with the validator's findings, or the error.

## Contract

Every entry point has the C type `lean_object *(lean_object *)`:
* the argument is an owned Lean `String` (Lean 4.34's code generator treats exported parameters
  as owned, so `@&` is deliberately not used);
* the result is an owned `IO String` result that is always `ok`: every failure is reported
  inside the string, `{"bug": "<message>"}` when Lean code panicked.

## Panics

A Lean `panic!` (also `a[i]!` out of bounds, `get!` on `none`, …) does not unwind: the runtime
prints `PANIC at …` to the thread's stderr and continues with a default value, which would
silently corrupt the result. Each entry point therefore runs its computation with stderr
redirected to a buffer (`IO.setStderr` is thread-local) and reports a `bug` if a panic message
was captured. Output that is not a panic message is forwarded to the real stderr. This relies on
the runtime's default `exit on panic = false` and on `LEAN_ABORT_ON_PANIC` being unset; with
either changed, a panic terminates the process.
-/

namespace Dogwood.Frontend.Ffi

open Lean (Json)

/-- Run the pure computation `f ()` with the thread's stderr captured: its value, or why it has
none (it panicked, or raised an IO error). `@[noinline]` and the thunk keep the computation
inside the redirected window. -/
@[noinline] def capture {α : Type} (f : Unit → α) : IO (Except String α) := do
  let buf ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let old ← IO.setStderr (IO.FS.Stream.ofBuffer buf)
  let r ← try
      let out ← IO.lazyPure f
      pure (.ok out)
    catch e =>
      pure (.error s!"IO error in the Lean frontend: {e}")
    finally
      let _ ← IO.setStderr old
  let captured := String.fromUTF8? (← buf.get).data |>.getD "<non-UTF-8 stderr output>"
  if (captured.splitOn "PANIC").length > 1 then
    return .error s!"the Lean frontend panicked: {captured.trimAsciiEnd.toString}"
  if !captured.isEmpty then
    IO.eprint captured
  return r

/-- The reply of a computation that failed in Lean itself. -/
def bug (message : String) : String :=
  (Json.mkObj [("bug", Json.str message)]).compress

/-- Run `f ()` under `capture`: its reply, or a `bug` reply. -/
def guarded (f : Unit → String) : IO String := do
  match ← capture f with
  | .ok out => return out
  | .error m => return bug m

/-- Round-trip probe: returns its input unchanged. -/
@[export dogwood_frontend_ping]
def ping (input : String) : IO String := pure input

/-- Parse, give ids, lower and validate one policy set (`Driver.lowerAllStr`). -/
@[export dogwood_frontend_lower]
def lower (input : String) : IO String :=
  guarded fun _ => Driver.lowerAllStr input

/-- Parse and give ids to several policy sets, lower them together and validate the result
(`Driver.lowerManyAllStr`). -/
@[export dogwood_frontend_lower_many]
def lowerMany (input : String) : IO String :=
  guarded fun _ => Driver.lowerManyAllStr input

/-- Parse one policy set and give it its ids, the first phase alone (`Driver.parseAllStr`). -/
@[export dogwood_frontend_parse]
def parse (input : String) : IO String :=
  guarded fun _ => Driver.parseAllStr input

/-- Test hook: panics when its input is `"panic"`, so the tests can check that a Lean panic
surfaces as a `bug` instead of a default value. -/
def panicProbeCore (s : String) : String :=
  if s == "panic" then panic! "panic probe" else s

@[export dogwood_frontend_panic_probe]
def panicProbe (input : String) : IO String :=
  guarded fun _ => (Json.mkObj [("ok", Json.str (panicProbeCore input))]).compress

end Dogwood.Frontend.Ffi
