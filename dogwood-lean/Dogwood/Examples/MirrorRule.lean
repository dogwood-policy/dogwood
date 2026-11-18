import Dogwood.Examples.Common
import Dogwood.Eval.Decision

/-!
# The strict mirror rule: forged and scope-less history

Regression examples for the strict mirror rule (`Dogwood.Spec.Mirrored`). Each trace is
ingested as `Log.submit` ingests it: an event that does not conform is rejected and enters no
history, and each accepted event is decided by the verified evaluator over the events accepted so
far (`run`; `Dogwood.Thm.conformsB_iff` and `Dogwood.Thm.authorize_eq` tie both to the
specification). If the rule held vacuously when the request side did not resolve, every expected
outcome below would differ; the comment on each case gives that outcome.

* **(a) Forgery under the default schema.** Scope-less events that log `callerPrincipal: alice`
  are rejected, and Alice's request is allowed. Under a vacuous rule they would enter her history
  and fill her rate limit, and her request would be denied.
* **(b) Forgery when the pin is not universal.** `Read` events pin `callerPrincipal` and `Login`
  events do not, so no pin is universal. Pin injection still compares the forged events' logged
  `callerPrincipal` with Alice's principal, so under a vacuous rule they would fill her rate
  limit. They are rejected.
* **(c) Scope-less history is rejected.** A `Login::response` without a principal does not
  conform, and Alice's `Read` is denied; under a vacuous rule it would count as her login. With
  the scope attached, the read is allowed.
* **(d) A request that omits a universal pin's context attribute.** Under `pin tenant =
  context.tenant`, requests that omit `context.tenant` but log `tenant` are rejected. Under a
  vacuous rule they would see no history, their own included, and never be limited.
* **(e) A principal pin under another name.** Under `pin actor = principal` on every kind, the pin
  is a universal symmetric pin, whatever its field is called. Mallory's requests that log
  `actor: alice` do not conform, and do not fill Alice's rate limit. If symmetry were decided by
  the field's name, the pin would be neither checked nor a partition key, the forged requests
  would fill her rate limit, and her request would be denied.
-/

namespace Dogwood.Examples.MirrorRule

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Examples
open Cedar.Spec (EntityUID Value Attr Entities)
open Cedar.Data (Map Set)

def showReason : FailClosed → String
  | .noPrincipal => "noPrincipal" | .noResource => "noResource"
  | .nonconformingEvent => "nonconformingEvent" | .nonconformingContext => "nonconformingContext"
  | .nonconformingEntities => "nonconformingEntities" | .missingScopeEntity => "missingScopeEntity"
  | .providerError => "providerError" | .nonconformingProviderOutput => "nonconformingProviderOutput"
  | .temporalError => "temporalError"

def showOutcome : Outcome → String
  | .noDecision => "noDecision"
  | .failClosed r => s!"failClosed {showReason r}"
  | .decided r => match r.decision with | .allow => "ALLOW" | .deny => "DENY"

def rule (id : String) (eff : Cedar.Spec.Effect) (act : EntityUID) (conds : Conditions) : Policy where
  id := id
  effect := eff
  principalScope := .principalScope .any
  actionScope := .actionScope (.eq act)
  resourceScope := .resourceScope .any
  condition := conds

def noProviders : Provider.Providers := fun _ => .error

/-- Ingest `σ` (readings already strictly increasing): reject each event that does not conform,
and decide each accepted one with the verified evaluator over the events accepted so far. -/
def run (P : PolicySet) (σ : Trace) : List String :=
  (σ.foldl (fun (acc : Trace × List String) p =>
    if p.event.conformsB P.actionSchema P.schema then
      let t := acc.1 ++ [p]
      (t, acc.2 ++ [showOutcome (Dogwood.Eval.authorize .clamp P noProviders t (t.length - 1))])
    else (acc.1, acc.2 ++ ["rejected"])) ([], [])).2

def alice := oauthUser "alice"
def read := action "Read"
def login := action "Login"
def actions : List ActionDecl := [(read, [("doc", .string)]), (login, [("doc", .string)])]

/-- `count for (t: Timepoint). where formerly within 1h (Read::request{} && tp(t)) > 3` -/
def tooMany : Formula :=
  .cmp .gt (.agg (.count [⟨"t", .timepoint⟩]
    (.formerly ⟨1, .hours⟩ (.and (.pred read "request" []) (.tp "t"))))) (.long 3)

/-- `permit Read`, and `forbid Read when { more than 3 Read requests within 1h }`. -/
def rateLimited (schema : EventSchema) : PolicySet where
  policies := [rule "policy_0" .permit read [],
               rule "policy_1" .forbid read [⟨.when, .temporal tooMany⟩]]
  schema := schema
  actionSchema := actionSchema actions
  tickRate := .seconds

def req (who : EntityUID) : Event := logEvent who read "request" "r" [("doc", .prim (.string "d"))]

/-- A scope-less event that logs alice as its caller. -/
def forged (kind : String) : Event :=
  { req alice with kind := kind, principal := none, resource := none }

def attack : Trace := [⟨1, forged "request"⟩, ⟨2, forged "request"⟩, ⟨3, forged "request"⟩,
  ⟨4, forged "response"⟩, ⟨100, req alice⟩]

/-! ## (a) The default schema (a universal `callerPrincipal` pin) -/

def defaultP := rateLimited (defaultSchema true actions)

/-- A forged scope-less event does not conform (under a vacuous rule it would). -/
example : (forged "request").conformsB defaultP.actionSchema defaultP.schema = false := by decide

/-- Alice's own request conforms. -/
example : (req alice).conformsB defaultP.actionSchema defaultP.schema = true := by decide

-- Vacuous rule: ["failClosed noPrincipal", "failClosed noPrincipal", "failClosed noPrincipal",
-- "noDecision", "DENY"].
#guard run defaultP attack = ["rejected", "rejected", "rejected", "rejected", "ALLOW"]

/-! ## (b) The same pin, declared on `Read` and not on `Login`: not universal -/

def partialSchema : EventSchema :=
  [⟨read, "request", true, [callerPin], actionFields [("doc", .string)]⟩,
   ⟨read, "response", false, [callerPin], actionFields [("doc", .string)]⟩,
   ⟨login, "request", true, [], actionFields [("doc", .string)]⟩,
   ⟨login, "response", false, [], actionFields [("doc", .string)]⟩]

def partialP := rateLimited partialSchema

example : partialSchema.universalPins = [] := by decide

example : (forged "request").conformsB partialP.actionSchema partialP.schema = false := by decide

-- Vacuous rule: ["failClosed noPrincipal", "failClosed noPrincipal", "failClosed noPrincipal",
-- "noDecision", "DENY"]: the forged events would fill Alice's rate limit.
#guard run partialP attack = ["rejected", "rejected", "rejected", "rejected", "ALLOW"]

/-! ## (c) Scope-less history: a `Login::response` that carries no scope -/

/-- `permit Read when temporal { formerly within 1h Login::response{} }` -/
def readAfterLogin : PolicySet :=
  { defaultP with
    policies := [rule "policy_0" .permit read
      [⟨.when, .temporal (.formerly ⟨1, .hours⟩ (.pred login "response" []))⟩]] }

def loginResponse : Event :=
  { logEvent alice login "response" "l" [("doc", .prim (.string "d"))] with
    principal := none, resource := none }

example : loginResponse.conformsB readAfterLogin.actionSchema readAfterLogin.schema = false := by
  decide

-- Vacuous rule: ["noDecision", "ALLOW"].
#guard run readAfterLogin [⟨1, loginResponse⟩, ⟨100, req alice⟩] = ["rejected", "DENY"]

/-- With its scope attached, the response is Alice's login, and her read is allowed. -/
def loginResponseScoped : Event := { loginResponse with principal := some alice, resource := some gw1 }

#guard run readAfterLogin [⟨1, loginResponseScoped⟩, ⟨100, req alice⟩] = ["noDecision", "ALLOW"]

/-- Without a principal, and without a logged caller, the response breaks the pin instead. -/
def loginResponseBare : Event :=
  { loginResponse with logged := Map.make [
      ("input", .record (Map.make [("doc", .prim (.string "d"))])),
      ("callerResource", .prim (.entityUID gw1)),
      ("requestId", .prim (.string "l"))] }

example : loginResponseBare.conformsB readAfterLogin.actionSchema readAfterLogin.schema = false := by
  decide

/-! ## (d) A universal context pin whose attribute the request omits -/

section ContextPin
open Cedar.Validation (CedarType)

def mallory := oauthUser "mallory"
def ping := action "Ping"

def pingContext : Cedar.Validation.RecordType := Map.make [
  ("input", .required (.record (Map.make [("doc", .required .string)]))),
  ("tenant", .optional .string)]

def pingSchema : Cedar.Validation.Schema where
  ets := Map.make [
    (oauthUserType, .standard ⟨Set.empty, Map.make [("id", .required .string)], some .string⟩),
    (gatewayType, .standard ⟨Set.empty, Map.empty, none⟩)]
  acts := Map.make [(ping,
    { appliesToPrincipal := Set.make [oauthUserType], appliesToResource := Set.make [gatewayType],
      ancestors := Set.empty, context := pingContext })]

def tenantPin : Pin := ⟨["tenant"], .context ["tenant"]⟩

def pingFields : List FieldDecl :=
  [⟨["input", "doc"], .cedar .string, true⟩, ⟨["tenant"], .cedar .string, false⟩,
   ⟨["callerPrincipal"], .entities [oauthUserType], false⟩]

def tenantSchema : EventSchema :=
  [⟨ping, "request", true, [tenantPin], pingFields⟩, ⟨ping, "response", false, [tenantPin], pingFields⟩]

/-- `count for (t: Timepoint). where formerly within 1h tp(t) > 3` -/
def busy : Formula :=
  .cmp .gt (.agg (.count [⟨"t", .timepoint⟩] (.formerly ⟨1, .hours⟩ (.tp "t")))) (.long 3)

def anyAction (i : String) (eff : Cedar.Spec.Effect) (conds : Conditions) : Policy where
  id := i
  effect := eff
  principalScope := .principalScope .any
  actionScope := .actionScope .any
  resourceScope := .resourceScope .any
  condition := conds

def tenantP : PolicySet where
  policies := [anyAction "policy_0" .permit [], anyAction "policy_1" .forbid [⟨.when, .temporal busy⟩]]
  schema := tenantSchema
  actionSchema := pingSchema
  tickRate := .seconds

def pingEvent (ctxTenant : Option String) : Event where
  action := ping
  kind := "request"
  principal := some mallory
  resource := some gw1
  logged := Map.make [("input", .record (Map.make [("doc", .prim (.string "d"))])),
    ("tenant", .prim (.string "mallory-co")), ("callerPrincipal", .prim (.entityUID mallory))]
  context := Map.make ([("input", .record (Map.make [("doc", .prim (.string "d"))]))] ++
    match ctxTenant with | some t => [("tenant", .prim (.string t))] | none => [])
  entities := Map.empty

def flood (t : Option String) : Trace := (List.range 6).map fun (i : Nat) => ⟨Int.ofNat i + 1, pingEvent t⟩

-- Requests that carry the tenant are limited after three.
#guard run tenantP (flood (some "mallory-co")) = ["ALLOW", "ALLOW", "ALLOW", "DENY", "DENY", "DENY"]

-- Vacuous rule: ["ALLOW", "ALLOW", "ALLOW", "ALLOW", "ALLOW", "ALLOW"]: never limited.
#guard run tenantP (flood none) =
  ["rejected", "rejected", "rejected", "rejected", "rejected", "rejected"]

end ContextPin

/-! ## (e) A principal pin under another name -/

section RenamedPin

def actorPin : Pin := ⟨["actor"], .scope .principal []⟩

def actorFields : List FieldDecl :=
  actionFields [("doc", .string)] ++ [⟨["actor"], .entities [oauthUserType], false⟩]

def actorSchema : EventSchema :=
  [⟨read, "request", true, [actorPin], actorFields⟩,
   ⟨read, "response", false, [actorPin], actorFields⟩,
   ⟨login, "request", true, [actorPin], actorFields⟩,
   ⟨login, "response", false, [actorPin], actorFields⟩]

def actorP := rateLimited actorSchema

example : actorSchema.universalPins = [actorPin] := by decide

/-- `who`'s own Read request, logging `actor` as `actor`. -/
def actorReq (who actor : EntityUID) : Event :=
  { req who with logged := Map.make [
      ("input", .record (Map.make [("doc", .prim (.string "d"))])),
      ("actor", .prim (.entityUID actor)),
      ("callerPrincipal", .prim (.entityUID who)),
      ("callerResource", .prim (.entityUID gw1)),
      ("requestId", .prim (.string "r"))] }

def mallory' := oauthUser "mallory"

/-- Mallory's request that logs Alice as its actor does not conform. -/
example : (actorReq mallory' alice).conformsB actorP.actionSchema actorP.schema = false := by
  decide

example : (actorReq alice alice).conformsB actorP.actionSchema actorP.schema = true := by decide

def actorAttack : Trace :=
  (List.range 4).map (fun (i : Nat) => ⟨Int.ofNat i + 1, actorReq mallory' alice⟩) ++
    [⟨100, actorReq alice alice⟩]

-- Name-based symmetry: ["ALLOW", "ALLOW", "ALLOW", "ALLOW", "DENY"].
#guard run actorP actorAttack = ["rejected", "rejected", "rejected", "rejected", "ALLOW"]

end RenamedPin

/-! ## (f) A resource pin under another name

`pin site = resource` is symmetric, as `pin callerResource = resource` is: an event's `site` must
be its own resource. -/

section RenamedResourcePin

def gw2 : EntityUID := drupe "Gateway" "gw2"

def sitePin : Pin := ⟨["site"], .scope .resource []⟩

def siteFields : List FieldDecl :=
  actionFields [("doc", .string)] ++ [⟨["site"], .entities [gatewayType], false⟩]

def siteSchema : EventSchema :=
  [⟨read, "request", true, [sitePin], siteFields⟩, ⟨read, "response", false, [sitePin], siteFields⟩]

/-- Alice's Read request on `gw1`, logging `site` as `site`. -/
def siteReq (site : EntityUID) : Event :=
  { req alice with logged := Map.make [
      ("input", .record (Map.make [("doc", .prim (.string "d"))])),
      ("site", .prim (.entityUID site)),
      ("callerPrincipal", .prim (.entityUID alice)),
      ("callerResource", .prim (.entityUID gw1)),
      ("requestId", .prim (.string "r"))] }

def siteP := rateLimited siteSchema

example : siteSchema.universalPins = [sitePin] := by decide
example : (siteReq gw1).conformsB siteP.actionSchema siteP.schema = true := by decide
/-- A request on `gw1` that logs `gw2` as its site does not conform. -/
example : (siteReq gw2).conformsB siteP.actionSchema siteP.schema = false := by decide

end RenamedResourcePin

/-! ## (g) A context pin under another name

`pin sid = context.session` is symmetric, as `pin session = context.session` is: an event's
`sid` must be its own request's session. Mallory's requests in session `s2` that log `sid: s1`
do not conform, so they do not count against session `s1`'s limit. -/

section RenamedContextPin
open Cedar.Validation (CedarType)

def sessionSchema : Cedar.Validation.Schema where
  ets := (actionSchema actions).ets
  acts := Map.make [(read,
    { appliesToPrincipal := Set.make [oauthUserType], appliesToResource := Set.make [gatewayType],
      ancestors := Set.empty,
      context := Map.make [
        ("input", .required (.record (Map.make [("doc", .required .string)]))),
        ("session", .required .string)] })]

def sidPin : Pin := ⟨["sid"], .context ["session"]⟩

def sidFields : List FieldDecl :=
  actionFields [("doc", .string)] ++ [⟨["sid"], .cedar .string, false⟩]

def sidSchema : EventSchema :=
  [⟨read, "request", true, [sidPin], sidFields⟩, ⟨read, "response", false, [sidPin], sidFields⟩]

def sidP : PolicySet where
  policies := [rule "policy_0" .permit read [],
               rule "policy_1" .forbid read [⟨.when, .temporal tooMany⟩]]
  schema := sidSchema
  actionSchema := sessionSchema
  tickRate := .seconds

/-- `who`'s Read request in session `session`, logging `sid` as `sid`. -/
def sidReq (who : EntityUID) (session sid : String) : Event :=
  { req who with
    logged := Map.make [
      ("input", .record (Map.make [("doc", .prim (.string "d"))])),
      ("sid", .prim (.string sid)),
      ("callerPrincipal", .prim (.entityUID who)),
      ("callerResource", .prim (.entityUID gw1)),
      ("requestId", .prim (.string "r"))]
    context := Map.make [
      ("input", .record (Map.make [("doc", .prim (.string "d"))])),
      ("session", .prim (.string session))] }

example : sidSchema.universalPins = [sidPin] := by decide
example : (sidReq alice "s1" "s1").conformsB sidP.actionSchema sidP.schema = true := by decide
/-- A request in session `s2` that logs `s1` as its `sid` does not conform. -/
example : (sidReq mallory "s2" "s1").conformsB sidP.actionSchema sidP.schema = false := by decide

def sidAttack : Trace :=
  (List.range 4).map (fun (i : Nat) => ⟨Int.ofNat i + 1, sidReq mallory "s2" "s1"⟩) ++
    [⟨100, sidReq alice "s1" "s1"⟩]

-- Name-based symmetry: ["ALLOW", "ALLOW", "ALLOW", "ALLOW", "DENY"].
#guard run sidP sidAttack = ["rejected", "rejected", "rejected", "rejected", "ALLOW"]

-- Session `s1`'s own requests are limited after three.
#guard run sidP ((List.range 5).map fun (i : Nat) => ⟨Int.ofNat i + 1, sidReq alice "s1" "s1"⟩) =
  ["ALLOW", "ALLOW", "ALLOW", "DENY", "DENY"]

end RenamedContextPin

/-! ## (h) A pin to an attribute is not symmetric

`pin uid = principal.id` correlates a field with an attribute of the principal. It is not
symmetric: not a partition key, and its field need only be logged, whatever value it holds. -/

section AttributePin

def uidPin : Pin := ⟨["uid"], .scope .principal ["id"]⟩

def uidFields : List FieldDecl :=
  actionFields [("doc", .string)] ++ [⟨["uid"], .cedar .string, false⟩]

def uidSchema : EventSchema :=
  [⟨read, "request", true, [uidPin], uidFields⟩, ⟨read, "response", false, [uidPin], uidFields⟩]

def uidP := rateLimited uidSchema

/-- Alice's Read request, logging `uid` as `uid`, or no `uid`. -/
def uidReq (uid : Option String) : Event :=
  { req alice with logged := Map.make ([
      ("input", .record (Map.make [("doc", .prim (.string "d"))])),
      ("callerPrincipal", .prim (.entityUID alice)),
      ("callerResource", .prim (.entityUID gw1)),
      ("requestId", .prim (.string "r"))] ++
      match uid with | some u => [("uid", .prim (.string u))] | none => []) }

example : EventSchema.Pin.isSymmetric uidPin = false := by decide
example : uidSchema.universalPins = [] := by decide
/-- Any logged value conforms: the mirror rule does not apply. -/
example : (uidReq (some "someone-else")).conformsB uidP.actionSchema uidP.schema = true := by decide
/-- The pinned field must still be logged. -/
example : (uidReq none).conformsB uidP.actionSchema uidP.schema = false := by decide

end AttributePin

/-! ## (i) A caller field that a pin names follows its pin

`callerPrincipal` mirrors the request's principal only when no pin names it. Under
`pin callerPrincipal = principal.id`, an attribute pin, the field is not mirrored, so an event
may log another principal in it. -/

section PinnedCallerField

def callerIdPin : Pin := ⟨["callerPrincipal"], .scope .principal ["id"]⟩

def callerIdSchema : EventSchema :=
  [⟨read, "request", true, [callerIdPin], actionFields [("doc", .string)]⟩,
   ⟨read, "response", false, [callerIdPin], actionFields [("doc", .string)]⟩]

def callerIdP := rateLimited callerIdSchema

/-- Mallory's Read request that logs Alice as its caller. -/
def claimsAlice : Event := { req mallory with logged := (req alice).logged }

/-- Only the unpinned `callerResource` is mirrored. -/
example : (callerIdSchema.signature? read "request").map (·.mirrors.map (·.1)) =
    some [["callerResource"]] := by decide
/-- Not mirrored: the event conforms though it logs another principal. -/
example : claimsAlice.conformsB callerIdP.actionSchema callerIdP.schema = true := by decide
/-- Under the default schema, whose `callerPrincipal` pin is symmetric, it does not. -/
example : claimsAlice.conformsB callerIdP.actionSchema
    (defaultSchema true actions) = false := by decide

end PinnedCallerField

end Dogwood.Examples.MirrorRule
