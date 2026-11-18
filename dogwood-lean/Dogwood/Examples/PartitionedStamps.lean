import Dogwood.Examples.Common
import Dogwood.Thm.Partitioned

/-!
# Worked example: per-partition stamps and the single stamped log differ at a window's edge

The rule allows a read when the reader's login succeeded within the last second:

```text
permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1s Drupe::Action::"Login"::response{ input.user: context.input.user }
};
```

under the default (pinned) event schema, whose universal symmetric pin `callerPrincipal` makes
each principal a partition of its own. The authorizer's clock counts nanoseconds. Three events
arrive, with these clock readings:

| arrival | reading (ns) | event | partition |
|---|---|---|---|
| 0 | 0 | alice's login response | alice |
| 1 | 1 000 000 000 | bob's read request | bob |
| 2 | 1 000 000 000 | alice's read request | alice |

Bob's read and alice's read arrive at the same reading.

* **One log per partition, each stamped on its own** (`PolicySet.PartLeafHolds`). Alice's log
  holds her login at `0` and her read at `1 000 000 000`. The readings strictly increase, so the
  stamps are the readings. The login is exactly one second before the read, inside the closed
  window, and the read is allowed (`partitioned_allows`).
* **One log of all events** (`PolicySet.LeafHolds` over the stamped stream). Bob's read is stamped
  `1 000 000 000`, so alice's read, whose reading is not later, is stamped one nanosecond after it,
  `1 000 000 001`. Alice's login is then one nanosecond more than a second before her read, outside
  the window, and the read is denied (`single_log_denies`).

So the two semantics differ when readings do not strictly increase across partitions
(`semantics_differ`). Where they do strictly increase, on a stream suited to partitioned
evaluation, the two agree at each decision event (`Dogwood.Thm.partLeafHolds_iff_leafHolds`).
-/

namespace Dogwood.Examples.PartitionedStamps

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Thm Dogwood.Examples
open Cedar.Spec (EntityUID Value)

def login : EntityUID := action "Login"
def read : EntityUID := action "Read"

/-- An event of the user `name`, as its own principal, logging `input.user: name`. -/
def event (name : String) (a : EntityUID) (kind requestId : String) : Event :=
  logEvent (oauthUser name) a kind requestId [("user", .prim (.string name))]

/-- One second, in nanoseconds. -/
def second : Int := 1000000000

/-- Alice's login response, the first arrival. -/
def aliceLogin : Event := event "alice" login "response" "u1"

/-- Bob's read, the second arrival. -/
def bobRead : Event := event "bob" read "request" "u2"

/-- Alice's read, the third arrival and the decision. -/
def aliceRead : Event := event "alice" read "request" "u3"

/-- The arrivals, each with its clock reading in nanoseconds. -/
def arrivals : Trace := [⟨0, aliceLogin⟩, ⟨second, bobRead⟩, ⟨second, aliceRead⟩]

def actions : List ActionDecl := [(login, [("user", .string)]), (read, [("user", .string)])]

def schema : EventSchema := defaultSchema true actions

def φ : Formula :=
  .formerly ⟨1, .seconds⟩
    (.pred login "response" [(["input", "user"], .context ["input", "user"])])

/-- The one-rule policy set, with a clock that counts nanoseconds. -/
def policySet : PolicySet := { onePolicy read φ schema actions with tickRate := .nanos }

theorem universalPins_schema : schema.universalPins = [callerPin] := by decide

theorem pinsOf_login_response : schema.pinsOf login "response" = [callerPin] := by decide

/-- After pin injection, the login predicate also requires the request's principal. -/
theorem φ_injected : φ.injectPins schema =
    .formerly ⟨1, .seconds⟩ (.pred login "response"
      [(["input", "user"], .context ["input", "user"]), (["callerPrincipal"], .scope .principal [])]) := by
  simp [φ, Formula.injectPins, pinsOf_login_response, callerPin, PinRef.toTerm]

/-- Alice's login and her read are in one partition. -/
theorem key_aliceLogin : schema.partitionKey aliceLogin = schema.partitionKey aliceRead := by
  decide

/-- Bob's read is in another. -/
theorem key_bobRead : schema.partitionKey bobRead ≠ schema.partitionKey aliceRead := by
  decide

/-- **Alice's log**: her login at `0` and her read at one second. -/
theorem partitionLog_aliceRead :
    schema.partitionLog arrivals 2 aliceRead = [⟨0, aliceLogin⟩, ⟨second, aliceRead⟩] := by
  simp [EventSchema.partitionLog, EventSchema.keyLog, arrivals, key_aliceLogin, key_bobRead]

/-- The readings of alice's log strictly increase, so they are its stamps. -/
theorem stamp_aliceLog :
    Trace.stamp [⟨0, aliceLogin⟩, ⟨second, aliceRead⟩] = [⟨0, aliceLogin⟩, ⟨second, aliceRead⟩] :=
  stamp_of_strictlyIncreasing (by simp [Trace.StrictlyIncreasing, second])

/-- **The single stamped log**: alice's read, whose reading is bob's, is stamped one nanosecond
after it. -/
theorem stamp_arrivals :
    arrivals.stamp = [⟨0, aliceLogin⟩, ⟨second, bobRead⟩, ⟨second + 1, aliceRead⟩] := by
  simp only [arrivals, Trace.stamp, Trace.stamp.go, stampAfter, second, List.cons.injEq,
    TimePoint.mk.injEq, and_true]
  decide

variable (ι : ImplChoices)

/-- **Partitioned evaluation holds the leaf**: in alice's own log, her login is one second
before her read. -/
theorem partitioned_holds : policySet.PartLeafHolds ι arrivals 2 φ := by
  refine (partLeafHolds_iff (p := ⟨second, aliceRead⟩) rfl).mpr ?_
  show Sat ι .nanos (schema.partitionLog arrivals 2 aliceRead).stamp aliceRead (fun _ => True)
    Valuation.empty ((schema.partitionLog arrivals 2 aliceRead).length - 1) (φ.injectPins schema)
  rw [partitionLog_aliceRead, stamp_aliceLog, φ_injected]
  refine ⟨0, by decide, trivial, ⟨_, _, rfl, rfl, by decide, by decide⟩, ?_⟩
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact ⟨.prim (.string "alice"), by decide, rfl⟩
  · exact ⟨.prim (.entityUID (oauthUser "alice")), by decide, rfl⟩

/-- **The single stamped log fails the leaf**: there, alice's read is stamped one nanosecond
after bob's, and her login is one nanosecond more than a second before it. -/
theorem single_log_fails : ¬ policySet.LeafHolds ι arrivals.stamp 2 φ := by
  rintro ⟨p, hp, hs⟩
  rw [stamp_arrivals] at hp hs
  change Sat ι .nanos _ _ _ _ 2 (φ.injectPins schema) at hs
  rw [φ_injected] at hs
  obtain ⟨k, hk, _, ⟨pj, pk, hpj, hpk, _, hw⟩, ⟨p', hp', ha, hkd, _⟩⟩ := hs
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hpj
  subst hpj
  rw [hpk] at hp'
  cases hp'
  match k, hk with
  | 0, _ =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hpk
    subst hpk
    exact absurd hw (by decide)
  | 1, _ =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hpk
    subst hpk
    exact absurd ha (by decide)
  | 2, _ =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hpk
    subst hpk
    exact absurd ha (by decide)

/-- **The two semantics differ** on a stream whose readings do not strictly increase across
partitions. -/
theorem semantics_differ :
    policySet.PartLeafHolds ι arrivals 2 φ ∧ ¬ policySet.LeafHolds ι arrivals.stamp 2 φ :=
  ⟨partitioned_holds ι, single_log_fails ι⟩

/-! ## The decisions -/

variable (ω : Provider.Providers)

/-- Alice's read passes every check of the decision, whatever its stamp: its logged record, its
request, and its entity store conform. -/
theorem admits (ts : Int) :
    policySet.Admits policySet.policies ω ⟨ts, aliceRead⟩ (oauthUser "alice") gw1 :=
  have h := onePolicy_admitsB (a := read) (φ := φ) (schema := schema) (actions := actions)
    (ω := ω) (p := ⟨ts, aliceRead⟩) (pr := oauthUser "alice") (rs := gw1) rfl rfl rfl
    (by decide +kernel : aliceRead.conformsB (actionSchema actions) schema = true)
    (by decide +kernel :
      Eval.requestConformsB (actionSchema actions) (aliceRead.request (oauthUser "alice") gw1) = true)
    (by decide +kernel : succeeds (Cedar.Validation.validateEntities (actionSchema actions)
      ((onePolicy read φ schema actions).decisionEntities aliceRead)) = true)
    (by decide +kernel)
  ⟨h.kind, h.principal, h.resource, h.event, h.request, h.entities, h.scopes, h.providers,
    h.outputs⟩

/-- How the rule decides alice's read, at any position `n` of any trace that holds it: it allows
exactly when the leaf, valued by `θ`, holds under every completion of the reading. -/
theorem decision_aliceRead {σ : Trace} {n : Nat} {ts : Int} {θ : ImplChoices → Event → Leaves}
    {b : Bool} (hσ : σ[n]? = some ⟨ts, aliceRead⟩)
    (hθ : ∀ ι', ι'.Completes ι → (θ ι' aliceRead).temporal φ = b) :
    (policySet.decideWith policySet.policies ω σ n fun e pr rs =>
      ι.supervaluate fun ι' =>
        isAuthorized (θ ι' e) (e.request pr rs) (policySet.decisionEntities e)
          policySet.policies).decision? = some (if b then .allow else .deny) := by
  have hagree : ∀ ι', ι'.Completes ι → ∀ q ∈ policySet.policies,
      (θ ι' aliceRead).AgreeOn (constLeaves b) q.toExpr.leaves := by
    intro ι' hc q hq
    simp only [policySet, onePolicy, List.mem_singleton] at hq
    subst hq
    rw [temporalPermit_leaves]
    intro l hl
    simp only [List.mem_singleton] at hl
    subst hl
    exact hθ ι' hc
  have hresp : (ι.supervaluate fun ι' =>
      isAuthorized (θ ι' aliceRead) (aliceRead.request (oauthUser "alice") gw1)
        (policySet.decisionEntities aliceRead) policySet.policies) =
      some (isAuthorized (constLeaves b) (aliceRead.request (oauthUser "alice") gw1)
        (policySet.decisionEntities aliceRead) policySet.policies) := by
    rw [supervaluate_congr fun ι' hc => isAuthorized_congr (hagree ι' hc)]
    exact supervaluate_const _
  rw [decideWith_of_admits hσ (admits ω ts)]
  dsimp only
  rw [hresp]
  simp only [Outcome.decision?]
  rw [show policySet.policies = (onePolicy read φ schema actions).policies from rfl,
    response_temporalPermit]
  cases b <;> rfl

/-- **Under partitioned evaluation, alice's read is allowed**: her login is one second before
her read in her own log. -/
theorem partitioned_allows : (policySet.authorizePart ι ω arrivals 2).decision? = some .allow :=
  decision_aliceRead ι ω (θ := fun ι' e => policySet.partLeaves ι' ω arrivals 2 e) rfl
    fun ι' _ => @decide_eq_true _ (Classical.propDecidable _) (partitioned_holds ι')

/-- **Over the single stamped log, alice's read is denied**: there her login is one nanosecond
more than a second before her read. -/
theorem single_log_denies : (policySet.authorize ι ω arrivals.stamp 2).decision? = some .deny :=
  decision_aliceRead ι ω (θ := fun ι' e => policySet.leaves ι' ω arrivals.stamp 2 e)
    (by rw [stamp_arrivals]; rfl) fun ι' _ =>
      @decide_eq_false _ (Classical.propDecidable _) (single_log_fails ι')

end Dogwood.Examples.PartitionedStamps
