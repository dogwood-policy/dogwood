import Dogwood.Thm.Frontend.Validate.TypingComplete
import Dogwood.Thm.Frontend.Validate.Converse
import Dogwood.Thm.TypingDecide
import Dogwood.Thm.ScopesDecide

/-!
# The temporal exceptions of the validator's completeness are needed

`leaf_complete` holds only on leaves that meet the crate's stricter rules. Each example here is a
temporal leaf and a checking context that meet every premise of `leaf_complete` but one rule, on
which the crate's validator reports a finding, though the leaf is well-typed in every request
environment, in a typing context of the specification that sees the environment exactly as the
crate's validator does:

* `noReservedHeadReadsF`: a read of a `context.<path>` whose head is a name lowering reserves;
* `actionsApart`: an entity literal of an entity type named `Action`;
* `pinHeadsUnreserved`: a pin that correlates its field with a `context.<path>` whose head is a
  name lowering reserves.

The first two leaves are `exists (t : Timepoint). tp(t) && l == r`, which monitors time and
needs no event; the last is a predicate under `formerly`. Every Boolean check is decided by the
kernel (`decide +kernel`).
-/

namespace Dogwood.Thm.Frontend.Counterexamples

open Dogwood.Frontend Dogwood.Frontend.Validate
open Dogwood.Spec.Temporal
open Cedar.Validation (CedarType Schema ActionSchemaEntry RecordType QualifiedType TypeEnv
  EntitySchemaEntry)
open Cedar.Spec (EntityType EntityUID)
open Cedar.Data (Map Set)

/-! ## Scaffolding -/

/-- A checking context with no derived event and no facts, for the actions `targets`. -/
def leafCtxOf (S : Schema) (targets : List (EntityUID × ActionSchemaEntry)) : LeafCtx where
  schema := S
  events := ⟨[], default, default⟩
  cap := 86400
  capText := "24h"
  targets := targets
  principal := .any
  resource := .any
  facts := []

/-- The specification's typing context of the request environment `e`, with the context record
type `ctx`. -/
def specCtxOf (C : LeafCtx) (ctx : RecordType) (e : ReqEnv) : TypingCtx :=
  ⟨{ ets := C.schema.ets, acts := C.schema.acts,
     reqty := { principal := e.principal, action := e.uid, resource := e.resource, context := ctx } },
   [], C.cap, []⟩

/-- The specification sees a request environment of a context without events or facts exactly as
the crate's validator does, when its context agrees with the action's outside reserved names and
the action admits declared entity types only. -/
theorem viewExact_of_empty (S : Schema) (targets : List (EntityUID × ActionSchemaEntry))
    (ctx : RecordType) (e : ReqEnv)
    (hctx : ∀ a, isHoistedName a = false → ctx.find? a = e.entry.context.find? a)
    (hdecl : ((appliesTo e.entry .principal).all S.ets.contains &&
      (appliesTo e.entry .resource).all S.ets.contains) = true) :
    ViewExact (specCtxOf (leafCtxOf S targets) ctx e) (leafCtxOf S targets) e where
  principal := rfl
  resource := rfl
  action := rfl
  context := hctx
  ets := rfl
  acts := fun _ => rfl
  declared := by
    simp only [Bool.and_eq_true, List.all_eq_true] at hdecl
    intro r ety h
    cases r
    · exact hdecl.1 ety h
    · exact hdecl.2 ety h
  maxWindow := rfl
  facts := fun _ hg => by cases hg
  events := fun _ _ _ hev => by simp [eventOf?, leafCtxOf] at hev
  factsExact := fun _ hg => by cases hg
  leafIff := fun _ _ _ hev => by simp [eventOf?, leafCtxOf] at hev
  sigOnly := fun _ _ hs => by simp [specCtxOf, Dogwood.Spec.EventSchema.signature?] at hs

/-- `exists (t : Timepoint). tp(t) && l == r`. -/
def atNow (l r : Term) : Formula :=
  .exist ⟨"t", .timepoint⟩ (.and (.tp "t") (.cmp .eq l r))

def userTy : EntityType := ⟨"User", []⟩
def botTy : EntityType := ⟨"Bot", []⟩
def actA : EntityUID := ⟨⟨"Action", []⟩, "a"⟩

def standardWith (attrs : RecordType) : EntitySchemaEntry := .standard ⟨Set.empty, attrs, none⟩

/-! ## A context path under a reserved name -/

def sRecord : RecordType := Map.mk [("s", .required .string)]

/-- The action `a`, on a `User` by a `User`, whose context declares `providers.s`. -/
def entryProv : ActionSchemaEntry :=
  ⟨Set.mk [userTy], Set.mk [userTy], Set.empty, Map.mk [("providers", .required (.record sRecord))]⟩

def schemaProv : Schema where
  ets := Map.mk [(userTy, standardWith Map.empty)]
  acts := Map.mk [(actA, entryProv)]

def ctxProv : LeafCtx := leafCtxOf schemaProv [(actA, entryProv)]

def phiProv : Formula := atNow (.context ["providers", "s"]) (.context ["providers", "s"])

theorem envs_prov : ctxProv.envs = [⟨actA, entryProv, userTy, userTy⟩] := rfl

/-- **A context path under a reserved name.** `context.providers.s == context.providers.s` is
well-typed where the action's context declares `providers.s`; the crate's validator resolves no
context path whose head lowering reserves, and reports it. Every other premise of
`leaf_complete` holds. -/
example :
    phiProv.MonitorsTime ∧ ctxProv.envs ≠ [] ∧
      (∀ e ∈ ctxProv.envs, ∃ C', ViewExact C' ctxProv e ∧ phiProv.WellTyped C' []) ∧
      actionsApart ctxProv.schema = true ∧
      pinHeadsUnreserved ctxProv.events = true ∧
      noReservedHeadReadsF phiProv = false ∧ leafFindings ctxProv phiProv ≠ [] := by
  refine ⟨(Dogwood.Thm.monitorsTimeB_iff _).mp (by decide +kernel), by decide +kernel, ?_,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  rw [envs_prov]
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  exact ⟨_, viewExact_of_empty schemaProv _ entryProv.context _ (fun _ _ => rfl) (by decide +kernel),
    (Dogwood.Thm.Formula.check_eq_nil_iff _ _ _).mp (by decide +kernel)⟩

/-! ## An entity type named `Action` -/

def actionTy : EntityType := ⟨"Action", []⟩

/-- An entity type named `Action` beside the action `a`. -/
def schemaApart : Schema where
  ets := Map.mk [(actionTy, standardWith Map.empty), (userTy, standardWith Map.empty)]
  acts := Map.mk [(actA, entryProv)]

def ctxApart : LeafCtx := leafCtxOf schemaApart [(actA, entryProv)]

def phiApart : Formula := atNow (.entity ⟨actionTy, "b"⟩) (.entity ⟨actionTy, "b"⟩)

theorem envs_apart : ctxApart.envs = [⟨actA, entryProv, userTy, userTy⟩] := rfl

/-- **An entity type named `Action`.** `Action::"b"` is a valid entity of the declared entity
type `Action`, which the specification types; the crate's validator checks a literal of a type
named `Action` against the actions, and reports `Action::"b"` as an undeclared action. Every other
premise of `leaf_complete` holds. -/
example :
    phiApart.MonitorsTime ∧ ctxApart.envs ≠ [] ∧
      (∀ e ∈ ctxApart.envs, ∃ C', ViewExact C' ctxApart e ∧ phiApart.WellTyped C' []) ∧
      noReservedHeadReadsF phiApart = true ∧
      pinHeadsUnreserved ctxApart.events = true ∧
      actionsApart ctxApart.schema = false ∧ leafFindings ctxApart phiApart ≠ [] := by
  refine ⟨(Dogwood.Thm.monitorsTimeB_iff _).mp (by decide +kernel), by decide +kernel, ?_,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  rw [envs_apart]
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  exact ⟨_, viewExact_of_empty schemaApart _ entryProv.context _ (fun _ _ => rfl) (by decide +kernel),
    (Dogwood.Thm.Formula.check_eq_nil_iff _ _ _).mp (by decide +kernel)⟩

/-! ## A pin under a reserved name -/

def fRecord : RecordType := Map.mk [("f", .required .string)]

/-- The action `a`, on a `User` by a `User`, whose context declares `input.f` and `providers.s`. -/
def entryPin : ActionSchemaEntry :=
  ⟨Set.mk [userTy], Set.mk [userTy], Set.empty,
   Map.mk [("input", .required (.record fRecord)), ("providers", .required (.record sRecord))]⟩

def schemaPin : Schema where
  ets := Map.mk [(userTy, standardWith Map.empty)]
  acts := Map.mk [(actA, entryPin)]

/-- The pin of `input.f` to `context.providers.s`. -/
def pinPin : Pin := { fieldPath := ["input", "f"], contextPath := ["providers", "s"], root := .context }

/-- The event `Action::"a"::k`, with the field `input.f`, spliced from the action's context, and
its pin. -/
def evPin : DerivedEvent :=
  { «namespace» := ["Action"], action := "a", kind := "k", decision := true,
    fields := [("input", .group [("f", .leaf (.cedar "String"))])], pins := [pinPin] }

def eventsPin : DerivedEventSchema := ⟨[evPin], default, default⟩

def ctxPin : LeafCtx := { leafCtxOf schemaPin [(actA, entryPin)] with events := eventsPin }

/-- The specification's signature of the event. -/
def sigsPin : Dogwood.Spec.EventSchema :=
  [{ action := actA, kind := "k", decision := true, pins := [⟨["input", "f"], .context ["providers", "s"]⟩],
     fields := [{ path := ["input", "f"], ty := .cedar .string, required := true }] }]

theorem leafFields_pin : evPin.leafFields = [(["input", "f"], .cedar "String")] := by
  simp [DerivedEvent.leafFields, evPin, DerivedFieldNode.leaves]

theorem typed_pin : typedSignatures eventsPin schemaPin = .ok sigsPin := by
  simp only [typedSignatures, eventsPin, List.map_cons, List.map_nil, DerivedEvent.signature,
    leafFields_pin]
  decide +kernel

theorem fieldType_pin : fieldType? schemaPin evPin ["input", "f"] = some (some (.cedar .string)) := by
  simp only [fieldType?, eventFields, leafFields_pin]
  decide +kernel

theorem pinsAt_pin : pinsAt ctxPin actA "k" ≠ [] := by
  have hev : eventOf? ctxPin.events actA "k" = some evPin := rfl
  have hpins : evPin.pins = [pinPin] := rfl
  have hacts : ctxPin.actions = [(actA, entryPin)] := rfl
  have hsch : ctxPin.schema = schemaPin := rfl
  have href : pinRefSorts? ctxPin entryPin pinPin = none := by decide +kernel
  have hfp : pinPin.fieldPath = ["input", "f"] := rfl
  simp only [pinsAt, hev, hpins, List.flatMap_cons, List.flatMap_nil, List.append_nil, hsch, hfp,
    fieldType_pin, hacts, List.filterMap_cons, href, List.filterMap_nil]
  simp

def phiPin : Formula := .formerly ⟨1, .hours⟩ (.pred actA "k" [])

theorem envs_pin : ctxPin.envs = [⟨actA, entryPin, userTy, userTy⟩] := rfl

/-- **A pin under a reserved name.** The event's pin correlates its field `input.f` with
`context.providers.s`, which the action's context declares, required, as a `String`: the
specification's pin rule holds, and `formerly within 1h Action::"a"::k{}` is well-typed; the crate's
validator resolves no pin path whose head lowering reserves, and reports the pin. Every other
premise of `leaf_complete` holds. -/
example :
    phiPin.MonitorsTime ∧ ctxPin.envs ≠ [] ∧
      (∀ e ∈ ctxPin.envs, ∃ C', ViewExact C' ctxPin e ∧ phiPin.WellTyped C' []) ∧
      noReservedHeadReadsF phiPin = true ∧
      actionsApart ctxPin.schema = true ∧
      pinHeadsUnreserved ctxPin.events = false ∧ leafFindings ctxPin phiPin ≠ [] := by
  refine ⟨(Dogwood.Thm.monitorsTimeB_iff _).mp (by decide +kernel), by decide +kernel, ?_,
    by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  · rw [envs_pin]
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    let C' : TypingCtx :=
      { specCtxOf ctxPin entryPin.context ⟨actA, entryPin, userTy, userTy⟩ with events := sigsPin }
    have hdf : ∀ ev ∈ eventsPin.events,
        (∀ x ∈ ev.leafFields, isSpliced x.1 = true →
          (((schemaPin.acts.find? (actionUid ev.namespace ev.action)).map (·.context)).bind
            (pathType · x.1)).isSome) ∧
        (∀ pin ∈ ev.pins, ev.leafFields.any (·.1 == pin.fieldPath) = true) := by
      intro ev hev
      simp only [eventsPin, List.mem_singleton] at hev
      subst hev
      rw [leafFields_pin]
      decide +kernel
    have hres : ∀ ev ∈ ctxPin.events.events,
        ev.leafFields.all (fun x => lookupPath ev x.1 == .leaf) = true := by
      intro ev hev
      simp only [ctxPin, eventsPin, List.mem_singleton] at hev
      subst hev
      rw [leafFields_pin]
      decide +kernel
    have hv : ViewAgrees C' ctxPin ⟨actA, entryPin, userTy, userTy⟩ :=
      { principal := rfl
        resource := rfl
        action := rfl
        context := fun _ _ => rfl
        ets := rfl
        acts := fun _ => rfl
        declared := by
          intro r ety h
          cases r <;> simp only [appliesTo, entryPin, Set.toList, Set.elts, List.mem_singleton] at h <;>
            subst h <;> decide +kernel
        maxWindow := rfl
        facts := fun _ hg => by cases hg
        events := fun _ _ _ hev => events_agree typed_pin hdf hev }
    exact ⟨C', viewExact_of (C := ctxPin) (C' := C') hv (fun _ hg => by cases hg) typed_pin hres,
      (Dogwood.Thm.Formula.check_eq_nil_iff _ _ _).mp (by decide +kernel)⟩
  · intro h
    simp only [leafFindings, List.append_eq_nil_iff] at h
    have hv := h.2
    simp only [phiPin, validityF, validityAt, validityArgs, argsAtoms, List.flatMap_nil,
      List.nil_append, eraseDups_eq_nil_iff, List.append_eq_nil_iff] at hv
    exact pinsAt_pin hv.1.1

/-! ## No longer an exception: a scope attribute of two types (survey S2)

The crate's validator used to reject a scope attribute with a different type on two entity types
an action admits, as ambiguous. It now types the path in each request environment, as Cedar and
the specification do, so the port reports nothing on such a leaf that is well typed in each. -/

/-- The action `a`, whose principal may be a `User` or a `Bot`, on a `User`. -/
def entryS2 : ActionSchemaEntry := ⟨Set.mk [botTy, userTy], Set.mk [userTy], Set.empty, Map.empty⟩

/-- `level` is a `String` on a `Bot` and a `Long` on a `User`. -/
def schemaS2 : Schema where
  ets := Map.mk [(botTy, standardWith (Map.mk [("level", .required .string)])),
    (userTy, standardWith (Map.mk [("level", .required .int)]))]
  acts := Map.mk [(actA, entryS2)]

def ctxS2 : LeafCtx := leafCtxOf schemaS2 [(actA, entryS2)]

/-- `principal.level == principal.level`: a `String` comparison for a `Bot`, a `Long` one for a
`User`. The port reports nothing. -/
example :
    leafFindings ctxS2 (atNow (.scope .principal ["level"]) (.scope .principal ["level"])) = [] := by
  decide +kernel

/-- `principal.level == 5` is wrong for a `Bot`, and the port reports it. -/
example : leafFindings ctxS2 (atNow (.scope .principal ["level"]) (.long 5)) ≠ [] := by
  decide +kernel

end Dogwood.Thm.Frontend.Counterexamples
