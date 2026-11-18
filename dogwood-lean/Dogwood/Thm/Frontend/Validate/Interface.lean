import Dogwood.Frontend.Validate

/-!
# The validator's soundness: the definitions its parts are stated with

The soundness theorem of the frontend's validator (`Dogwood.Thm.Frontend.validate_sound`) is
proved in parts, each about one side of what the crate's validator checks, against an abstract
view of the specification's typing context:

* **views** (`EnvView`, `ViewAgrees`): the specification's typing context of a temporal leaf, in
  a request environment, sees the augmented schema as the crate's validator does: the same entity
  types, the same actions, the same context attributes outside lowering's reserved names, the
  same event signatures, the same `max_window` cap, and at least the facts the crate computes,
  outside the paths lowering reserves;
* **the renaming of hoisted reads** (`renameHoisted`): the crate lowers a leaf to
  `context.<id>` (temporal) or `context.providers.<id>` (provider); the specification lowers the
  `k`-th leaf to `context.__dogwood_leaf_<k>`. `renameOk` is what the crate's context-read check
  guarantees of the lowered rules, and `CtxRel` how an action's context in the crate's augmented
  schema relates to the specification's.
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.Validate
open Dogwood.Spec (Path)
open Dogwood.Spec.Temporal
open Cedar.Validation (CedarType Schema ActionSchemaEntry RecordType QualifiedType TypeEnv)
open Cedar.Spec (Attr EntityUID)

/-! ## Views -/

/-- Whether a fact is about a path whose head lowering reserves: the crate's validator resolves no
such path. -/
def _root_.Dogwood.Spec.Temporal.Guard.reservedHead : Guard → Bool
  | .context (h :: _) => isHoistedName h
  | .context [] => true
  | .scope _ _ => false

/-- The specification's typing context sees the request environment `e` of the augmented schema
`S` as the crate's validator does: the same scope types and action, the same context attributes
outside lowering's reserved names, the same entity types and actions, and entity types declared
for the action's principal and resource. -/
structure EnvView (C' : TypingCtx) (S : Schema) (e : ReqEnv) : Prop where
  principal : C'.env.reqty.principal = e.principal
  resource : C'.env.reqty.resource = e.resource
  action : C'.env.reqty.action = e.uid
  context : ∀ a, isHoistedName a = false → C'.env.reqty.context.find? a = e.entry.context.find? a
  ets : C'.env.ets = S.ets
  acts : ∀ uid, C'.env.acts.contains uid = S.acts.contains uid
  declared : ∀ r ety, ety ∈ appliesTo e.entry r → S.ets.contains ety = true

/-- A derived event and the specification's signature of it agree: the same declared fields,
with the same types; a spliced field typed by the action's context; the same pins, each of a
declared field. -/
structure SigAgrees (S : Schema) (a : EntityUID) (ev : DerivedEvent) (sig : Dogwood.Spec.EventSignature) :
    Prop where
  fields : ∀ p, fieldType? S ev p = (sig.field? p).map (some ·.ty)
  leaf : ∀ p, lookupPath ev p = .leaf → (sig.field? p).isSome
  spliced : ∀ p fd, isSpliced p = true → sig.field? p = some fd →
    ∃ t, splicedFieldType? S a p = some t ∧ fd.ty = .cedar t
  pins : ev.pins.mapM Dogwood.Frontend.Pin.toSpec = .ok sig.pins
  pinFields : ∀ pin ∈ ev.pins, (sig.field? pin.fieldPath).isSome

/-- The specification's typing context of a temporal leaf sees the request environment `e` as the
crate's validator, with the leaf's checking context `C`, does. -/
structure ViewAgrees (C' : TypingCtx) (C : LeafCtx) (e : ReqEnv) : Prop extends
    EnvView C' C.schema e where
  maxWindow : C'.maxWindow = C.cap
  facts : ∀ g ∈ C.facts, g.reservedHead = false → g ∈ C'.facts
  events : ∀ a k ev, eventOf? C.events a k = some ev →
    ∃ sig, C'.events.signature? a k = some sig ∧ SigAgrees C.schema a ev sig

/-! ## The renaming of hoisted reads -/

/-- `context`, as a Cedar expression. -/
def isContextC : Cedar.Spec.Expr → Bool
  | .var .context => true
  | _ => false

/-- `context.providers`, as a Cedar expression. -/
def isContextProvidersC : Cedar.Spec.Expr → Bool
  | .getAttr (.var .context) "providers" => true
  | _ => false

mutual

/-- The crate's reads of hoisted leaves renamed: `context.<id>` of a temporal leaf `id ∈ tids`
becomes `context.<ren true id>`, and `context.providers.<id>` of a provider leaf `id ∈ pids`
becomes `context.<ren false id>`. The tests are in the conformance projection's order
(`putBack`). -/
def renameHoisted (tids pids : List String) (ren : Bool → String → Attr) :
    Cedar.Spec.Expr → Cedar.Spec.Expr
  | .getAttr e a =>
    if isContextC e && tids.contains a then .getAttr (.var .context) (ren true a)
    else if isContextProvidersC e && pids.contains a then .getAttr (.var .context) (ren false a)
    else .getAttr (renameHoisted tids pids ren e) a
  | .lit p => .lit p
  | .var v => .var v
  | .ite c t e =>
    .ite (renameHoisted tids pids ren c) (renameHoisted tids pids ren t) (renameHoisted tids pids ren e)
  | .and a b => .and (renameHoisted tids pids ren a) (renameHoisted tids pids ren b)
  | .or a b => .or (renameHoisted tids pids ren a) (renameHoisted tids pids ren b)
  | .unaryApp op e => .unaryApp op (renameHoisted tids pids ren e)
  | .binaryApp op a b => .binaryApp op (renameHoisted tids pids ren a) (renameHoisted tids pids ren b)
  | .hasAttr e a => .hasAttr (renameHoisted tids pids ren e) a
  | .extHasAttr e a as => .extHasAttr (renameHoisted tids pids ren e) a as
  | .set xs => .set (renameHoistedList tids pids ren xs)
  | .record axs => .record (renameHoistedRecord tids pids ren axs)
  | .call f xs => .call f (renameHoistedList tids pids ren xs)

def renameHoistedList (tids pids : List String) (ren : Bool → String → Attr) :
    List Cedar.Spec.Expr → List Cedar.Spec.Expr
  | [] => []
  | x :: xs => renameHoisted tids pids ren x :: renameHoistedList tids pids ren xs

def renameHoistedRecord (tids pids : List String) (ren : Bool → String → Attr) :
    List (Attr × Cedar.Spec.Expr) → List (Attr × Cedar.Spec.Expr)
  | [] => []
  | (a, x) :: axs => (a, renameHoisted tids pids ren x) :: renameHoistedRecord tids pids ren axs

end

/-- A lowered rule with its hoisted reads renamed: its scope reads no context. -/
def renamePolicy (tids pids : List String) (ren : Bool → String → Attr) (p : Cedar.Spec.Policy) :
    Cedar.Spec.Policy :=
  { p with condition := p.condition.map fun c => { c with body := renameHoisted tids pids ren c.body } }

mutual

/-- What the crate's context-read check guarantees of a lowered rule, in a policy set with a leaf:
it reads `context` only through attributes; it reads a temporal leaf's attribute only as lowering
does (`context.<id>`, never tested with `has`), and `providers` only as lowering does
(`context.providers.<id>`, `id` a provider leaf); and it reads no attribute `reserved` holds of
(the specification's leaf names). -/
def renameOk (tids pids : List String) (reserved : Attr → Bool) : Cedar.Spec.Expr → Bool
  | .var v => v != .context
  | .getAttr e a =>
    if isContextC e then tids.contains a || (a != "providers" && !reserved a)
    else if isContextProvidersC e && pids.contains a then true
    else renameOk tids pids reserved e
  | .hasAttr e a =>
    if isContextC e then !tids.contains a && a != "providers" && !reserved a
    else renameOk tids pids reserved e
  -- An extended `has` also reads its operand's attribute `a` (Cedar types `e has a.b` through
  -- `e.a`), which must not be a hoisted read.
  | .extHasAttr e a _ =>
    if isContextC e then !tids.contains a && a != "providers" && !reserved a
    else !(isContextProvidersC e && pids.contains a) && renameOk tids pids reserved e
  | .lit _ => true
  | .ite c t e => renameOk tids pids reserved c && renameOk tids pids reserved t &&
      renameOk tids pids reserved e
  | .and a b | .or a b | .binaryApp _ a b =>
    renameOk tids pids reserved a && renameOk tids pids reserved b
  | .unaryApp _ e => renameOk tids pids reserved e
  | .set xs | .call _ xs => renameOkList tids pids reserved xs
  | .record axs => renameOkRecord tids pids reserved axs

def renameOkList (tids pids : List String) (reserved : Attr → Bool) : List Cedar.Spec.Expr → Bool
  | [] => true
  | x :: xs => renameOk tids pids reserved x && renameOkList tids pids reserved xs

def renameOkRecord (tids pids : List String) (reserved : Attr → Bool) :
    List (Attr × Cedar.Spec.Expr) → Bool
  | [] => true
  | (_, x) :: axs => renameOk tids pids reserved x && renameOkRecord tids pids reserved axs

end

/-- How an action's context record type in the crate's augmented schema (`C₁`) relates to the
specification's (`C₂`): a temporal leaf's attribute, where the crate declares it, has its type at
the specification's name, required; a provider leaf's field of the `providers` record, where the
crate declares it, likewise; and every other attribute outside lowering's names and the
specification's is the same. -/
structure CtxRel (tids pids : List String) (ren : Bool → String → Attr) (reserved : Attr → Bool)
    (C₁ C₂ : RecordType) : Prop where
  temporal : ∀ a ∈ tids, ∀ q, C₁.find? a = some q → C₂.find? (ren true a) = some (.required q.getType)
  provider : ∀ a ∈ pids, ∀ q R q', C₁.find? "providers" = some q → q.getType = .record R →
    R.find? a = some q' → C₂.find? (ren false a) = some (.required q'.getType)
  other : ∀ b, b ∉ tids → b ≠ "providers" → reserved b = false → C₂.find? b = C₁.find? b

/-- The context of an action of the action schema the conformance projection reads off the
augmented schema: without the attributes `drop` (the projection's `actionSchemaJson`). -/
def dropContext (drop : List String) (e : ActionSchemaEntry) : ActionSchemaEntry :=
  { e with context := Cedar.Data.Map.make (e.context.toList.filter fun (k, _) => !drop.contains k) }

end Dogwood.Thm.Frontend
