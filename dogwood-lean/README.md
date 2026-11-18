# dogwood-lean: the formal semantics of Dogwood

This directory is a formal specification of the Dogwood policy language, written in Lean 4. A Dogwood rule is a Cedar policy whose conditions may also contain two kinds of leaf that Cedar cannot express: a *temporal condition*, which looks back over the log of earlier events (`formerly`, `previous`, `since`, `count`, and `sum`, within time windows), and an *information-provider call*, which reads a fact computed at decision time. The specification states what every decision means, what validation guarantees, and what an implementation must do around a decision. It is the reference against which an implementation can be proved correct. For example, an implementation that keeps a separate log for each partition key would be proved correct by showing that every leaf verdict it commits is this specification's verdict under partitioned evaluation (`PolicySet.PartLeafHolds`) for the same history.

The specification describes Dogwood 1.2, the language of the crate in this repository, with the off-by-default Cargo feature `experimental-arithmetic` turned on (it allows `+`, `-`, and `*` in comparison operands). It builds on the Cedar formal specification, [cedar-lean](https://github.com/cedar-policy/cedar-spec/tree/main/cedar-lean), at release `v4.14.0`, the Cedar release the crate uses. Dogwood reuses Cedar's values, entities, operators, authorizer, and validator unchanged. The specification uses cedar-lean's definitions of the values, entities, operators, and validator, and restates Cedar's evaluator and authorizer, case for case, over Dogwood rules.

This page is the overview. [`REFERENCE.md`](REFERENCE.md) is the detailed reference: the specification's modules, rules, and main theorems, and its known differences from the crate.

## What the specification defines

The specification is a set of Lean definitions. This table lists its parts and their main definitions.

| Part | What it says | Main definitions |
|---|---|---|
| Rules | A rule is a Cedar static policy whose `when` and `unless` conditions may contain temporal leaves and provider leaves, as the crate's frontend outputs it after parsing, macro expansion, and the derivation of event signatures. | `Dogwood.Spec.Expr`, `Dogwood.Spec.Policy`, `Dogwood.Spec.Temporal.Formula` |
| The meaning of a temporal condition | A satisfaction relation over a trace of events. A condition at a timepoint reads only that timepoint and earlier ones, within time windows, and may quantify over values (a past-only metric first-order temporal logic). Windows are measured in ticks of a declared clock rate, nanoseconds by default. Under a pin such as the default schema's `callerPrincipal = principal`, a condition sees only the events of the current key (key-local semantics). | `Temporal.Sat`, `EventSchema.Visible` |
| Validity | What validation requires of a policy set. Cedar's validator must accept the rules with each leaf replaced by a context attribute, and each temporal leaf must be well typed, safe (every variable is range-restricted, so that it can take only finitely many values), and vary with the timepoint in each top-level conjunct and in each body of an operator, binder, or aggregate (a rule that rejects likely mistakes). | `PolicySet.Valid` |
| Runtime conformance | What the data a decision reads must be: the request, the entity store, each logged event, and each provider output. | `Event.Conforms`, `Canonical` |
| The decision | The outcome of an event at a timepoint of a trace. A fixed sequence of checks comes first, and each failing check fails the decision closed with a reason of its own. Then Cedar's authorizer decides, with each temporal leaf valued by the satisfaction relation and each provider leaf by the provider's output. | `PolicySet.authorize`, `PolicySet.decideWith` |
| Around the decision | Ingestion stamps each accepted event with `max(clock reading, last stamp + 1)` from the authorizer's own clock, and rejects an event that does not conform. A log of events and deployments gives policy updates their meaning. The event-log contract states what every run of an implementation, with any number of instances and retries, must guarantee. An accepted event resubmitted under its event id within the retry window is not logged again, and gets the original's answer or is rejected as unavailable. | `Log.submit`, `Log.decide`, `Run.Meets` |

The satisfaction relation quantifies over all values, so it is not itself a program. [What is executable](#what-is-executable) describes the programs that decide it.

## An example

The guide's `read_after_login` policy permits a `Read` only if a `Login` response for the same user was recorded within the last hour and, under the default event schema, by the same principal:

```
permit (principal, action == Drupe::Action::"Read", resource)
when temporal {
    formerly within 1h Drupe::Action::"Login"::response{ input.user: context.input.user }
};
```

**The default event schema.** Each action has three kinds of event. A `request` is a **decision event**. A `response` and an `error` are **history events**: they are recorded, and later decisions read them, but they ask for no decision. Every kind logs the action's inputs (a `response` also its outputs), `callerPrincipal`, `callerResource`, `requestId`, and `sessionId`, and declares the pin `callerPrincipal = principal`, which makes evidence key-local by principal (the crate's `configuration/event-schemas/pinned.dwschema`).

Over this trace, in seconds, the specification gives these outcomes, proved in `Dogwood.Examples.ReadAfterLogin`:

| Timepoint | Time | Event (principal `alice`) | Outcome |
|---|---|---|---|
| 0 | 0 | `Login::request` | Deny (no rule permits a `Login`) |
| 1 | 5 | `Login::response` | No decision (a history event) |
| 2 | 10 | `Read::request` | Allow (the login response at 5 is within the hour) |
| 3 | 7200 | `Read::request` | Deny (the login response is 7,195 seconds old) |

`context.input.user` is the user of the `Read` being decided, at every past timepoint `formerly` scans; the predicate matches a logged `Login` response whose `input.user` is that user. [`REFERENCE.md`](REFERENCE.md#temporal-conditions-have-a-satisfaction-semantics) gives the satisfaction relation clause by clause.

## What is executable

`Dogwood.Eval` holds decision procedures, and each one is proved equal to the relation it decides:

- the temporal evaluator `Eval.eval` searches the finitely many candidate values a safe condition can take, and decides the satisfaction relation on every safe condition (`eval_iff`);
- `Eval.authorize` and `Eval.replay` compute `PolicySet.authorize` at every timepoint of a trace, under a total reading of out-of-range results, for a policy set whose leaves are safe (`authorize_eq`, `replay_eq`);
- `PolicySet.validationFindings` lists the problems of a policy set, and is empty exactly when the policy set is valid (`validationFindings_eq_nil_iff`);
- `Event.conformsB` and the other Boolean checks decide runtime conformance (`conformsB_iff`) by structural checks, which let the worked examples prove their decisions with `decide`.

The evaluator searches exhaustively, so an aggregate costs time exponential in the number of variables it binds. It is a reference for comparison with the crate, not an enforcement engine. The conformance checker described below is built from these procedures.

## What is proved

Every theorem rests only on Lean's three standard axioms (`propext`, `Classical.choice`, and `Quot.sound`); no proof uses `sorry` or `native_decide`. `Axioms.lean` names every public theorem of the library, the frontend's included (it leaves out the conformance checker's modules), and `lake env lean Axioms.lean` prints the axioms of each.

| Property | Theorems |
|---|---|
| **Validation is sound.** For a valid policy set, at a decision whose checks pass, over a trace of conforming events, every rule evaluates to a Boolean or to a runtime error that validation cannot rule out, and the response is Cedar's on the lowered rules. Under a total reading, every operand of a comparison the response depends on resolves to a value, and every witness and aggregate row is typed. | `soundness`, `decision_sound`, `allow_sound_leaves` |
| **Safe conditions are monitorable.** In a safe condition, every quantified variable takes one of finitely many candidate values read off the trace, and every aggregate has a total. | `rr_sound`, `total_exists`, `sat_exist_iff` (module `Dogwood.Thm.Monitorable`) |
| **The evaluator computes the semantics.** | `eval_iff`, `authorize_eq`, `replay_eq` |
| **A condition looks back no further than its horizon,** on a trace whose timestamps never decrease (as a stamped log's strictly increase), so an implementation that prunes the events beyond the policy set's horizon decides as the specification does. | `sat_horizon`, `sat_drop_horizon`, `authorize_drop_horizon` |
| **A declared `max_horizon` bounds retention.** When the event schema declares `max_horizon`, validity caps every temporal leaf's horizon at it, so keeping the events of the last `max_horizon` suffices for every valid policy set. | `horizon_le_maxHorizon`, `authorize_drop_maxHorizon` |
| **Key-local semantics is evaluation over the decision's partition,** and every trace of conforming events can be partitioned by key. | `leafHolds_iff_partition`, `partitionable_of_strict` |
| **Partitioned evaluation, with one log per key, each stamped on its own, is the single-log semantics** if the schema has no universal symmetric pin, or if the clock readings strictly increase across a whole stream of conforming events. Otherwise the two can differ. In `PartitionedStamps`, an event that arrives with the same clock reading as the last event of another key is stamped one tick later in the single log than in its own key's log. | `partLeafHolds_iff_keyLog`, `partLeafHolds_iff_leafHolds_of_noPins`, `partLeafHolds_iff_leafHolds`, `authorizePart_eq_authorize`, `PartitionedStamps.semantics_differ` |
| **Decisions are past-only.** Later events, and later log entries, never change an earlier outcome. | `authorize_append`, `decide_append` |
| **Adding hoisted attributes to more actions is safe.** Validity checks the lowered rules against the action schema with each leaf's attribute added only to the actions its rule's action scope admits, as the crate does (up to its shared provider record and pure action groups, which change no verdict); any augmentation that adds each attribute at least there, and only leaf attributes, gives the same verdict. | `valid_iff_covers`, `valid_iff_validAll`, `validate_augmentWith_agree` |
| **Dogwood conservatively extends Cedar.** A policy set without leaves decides every decision event that passes the checks as Cedar decides its request. | `authorize_ofCedar` |
| **A pin cannot be bypassed.** A pinned predicate matches only events whose pinned fields hold the request's values. | `pin_enforced` |
| **Out-of-range results fail closed or do not matter.** Under a reading that reports errors, a decision either fails closed or agrees with every total reading that completes it; when every result is in range, all readings agree. | `authorize_dichotomy`, `authorize_readings_agree` |
| **The clock rate is a unit.** Counting time a constant factor finer, with every timestamp scaled, changes no decision. | `sat_scale`, `authorize_scale` |
| **Ingestion keeps the timestamp rule and conformance, and the event-log contract is consistent and usable.** Every log that ingestion builds has strictly increasing stamps and conforming events only; a single instance meets the contract; in a run that meets it, every answer is the decision at its position in the whole log, and a retry is not logged again and is answered as its original or rejected as unavailable. | `ingest_strictlyIncreasing`, `conforming_ingest`, `sequential_meets`, `Run.Meets.outcome_eq`, `Run.Meets.retry_not_logged`, `Run.Meets.retry_reply` |
| **An implementation that computes the leaves correctly decides as the specification does.** | `authorizeWith_eq` |

The worked examples (`Dogwood.Examples`) prove, from the specification, the verdicts recorded for four of the guide's example bundles. They restate most of the accept/reject unit tests of the crate's temporal checker, and they check the strict mirror rule and canonical values on cases of their own. One example (`PartitionedStamps`) shows a stream on which partitioned evaluation allows a read that the single stamped log denies. [`REFERENCE.md`](REFERENCE.md#theorems) lists the main theorems, and the lemmas a proof of an implementation can reuse.

## How the specification is kept in agreement with the crate

`conformance/run.sh` compares the specification with the `dogwood-language` crate in this repository. The bridge (`bridge/`) is a Rust program built on the crate. For each bundle (a policy set, its schemas, and its traces), it lets the crate parse, expand, lower, validate, and replay the bundle, and it exports what the specification needs as JSON: the typed event signatures, the action schema, the rules with each hoisted leaf turned back into the leaf it stands for, the crate's validation findings, and the crate's verdict at every event. The conformance checker, the Lean executable `conformance`, decodes the JSON. It compares the validation findings, by category, the verdict at every event, replayed with the verified evaluator, and which events ingestion keeps, and it checks that every predicate of every exported leaf carries the pins of its event. Because `authorize_eq` proves the evaluator equal to `PolicySet.authorize`, the comparison is with the specification itself, not only with a second implementation.

The run covers the guide's examples, six of the crate's test corpora (`passing/mixed`, `passing/macros`, `passing/temporal_only`, `passing/provider_only`, `expected_failures`, and `experimental`, under `dogwood-language/tests/`), and the 68 probes of [`conformance/probes`](conformance/probes/README.md), written for the specification's rules and for the edge cases of lowering. The run fails on any disagreement that [`conformance/baseline.txt`](conformance/baseline.txt) does not list. The crate's validator and `PolicySet.Valid` agree on every validation probe except `validation_context_read_own_leaf_name`, which the baseline lists. Each disagreement the baseline lists has one of these causes:

| Cause | Where it shows | Effect |
|---|---|---|
| The crate takes the caller's timestamps as given, in seconds. | 2 probes | One decision differs in each, on a trace whose recorded times do not strictly increase. |
| The crate adds a bare entity for a principal or resource the event does not supply. | 1 corpus bundle, 2 probes | The specification fails 4 decisions closed that the crate decides. |
| The crate reports an extra Cedar finding for an undeclared provider or method. | 2 corpus bundles | Validation only. |
| For an optional `datetime`, `duration` or `ipaddr` attribute that a temporal leaf reads with no `has` test, the crate reports the unsupported type as well as the missing guard. The specification reports the missing guard alone. | 1 probe | Validation only. Both reject the policy. |
| The bridge exports the lowered rule, in which a Cedar part's read of its own leaf's hoisted attribute is that leaf. The crate rejects the read, and the specification, which sees only the leaf, accepts the policy. | 1 probe | Validation only. |

With the scope-entity check skipped, the specification decides those four as the crate does. Apart from them, the verdicts agree at every replayed event but two, the stamping probes' decisions.

`Dogwood.Frontend` is a stage-by-stage port of the crate's frontend (everything after the parsers). It is not part of the specification. `conformance/frontend-run.sh` compares each stage with the crate's, from a JSON export of the crate's inputs and results at every stage (feature `frontend-export`; see [`conformance/README.md`](conformance/README.md#the-frontend-stage-by-stage)). The crate's off-by-default `lean-frontend` feature can also run the port in place of the Rust frontend, or run both and compare their results. One of the port's stages is the relativization rewrite of pinned leaves. `Dogwood.Thm.Frontend.relativization_correct` proves that, for a well-typed, safe leaf, the port's rewrite, evaluated with every timepoint visible, agrees with key-local semantics on traces whose timestamps strictly increase.

`conformance/gen-run.sh` runs both comparisons on random bundles (schemas, provider declarations, macros, rules, and traces; see [`conformance/README.md`](conformance/README.md#generated-runs)).

## Key rules of the specification

| Rule | What it means | Why |
|---|---|---|
| The authorizer stamps events. | A submission carries no timestamp. Ingestion stamps an accepted event from the authorizer's clock, in nanoseconds by default. | A submitter that chooses its own timestamps can push the clock forward and reset its rate limits. |
| The strict mirror rule. | An event's symmetrically pinned fields (pins to its principal, its resource, or a context attribute, whatever the field is called) and its unpinned caller fields must equal its own request-side values, and must be absent when the event has no such value. Under the default schema, every history event must therefore carry the scope of the key it reports on, and evidence about another principal is key-local. | Without it, a scope-less event could log `callerPrincipal: alice` and fill Alice's rate limit. |
| Canonical values. | Every set in an event's logged record and request context must be sorted and free of duplicates, so that equal sets are equal values. A logged `null` is an absent field, because Cedar has no `null`. A decimal is its numeric value, so `02.5` and `2.5` are the same value. An implementation canonicalizes an event before it checks it. | A set held in two orders is two different Cedar values, which a pin or a comparison would tell apart. |
| Decisions fail closed on bad data. | A decision fails closed, with a reason of its own, on a nonconforming event, request, entity store, or provider output; on a failing provider; when a temporal leaf of an applicable rule reads an attribute of a principal or resource the event does not supply; and, under a reading that reports errors, when the outcome depends on an erroring result. | Soundness at the request then needs, beyond the decision's own checks, only that the logged events conform, which ingestion guarantees (`decision_sound`, `conforming_ingest`). |
| Policy updates have two readings. | A rule deployed while events flow observes either the whole trace (retrospective) or only the events from its deployment on (prospective). The specification is parameterized by the reading (`UpdateReading`). | An implementation chooses one; the crate's is retrospective. |
| Out-of-range results are a parameter. | What a comparison sees when an aggregate total or an arithmetic result leaves the 64-bit range is a parameter (`ImplChoices`): compute exactly, clamp (the crate's choice), or report an error. | The guide leaves it implementation-defined. |

## What the specification does not cover

**Not specified.**

- The frontend: parsing, macro expansion, the derivation of event signatures, and the names of hoisted attributes.
- How a control plane checks a change before it deploys it, and changes to the event schema, the action schema, or the provider declarations.

**Specified, but not proved.**

- That the crate's evaluator computes satisfaction, which the conformance run tests.
- A partitioned counterpart of `authorizeWith_eq`, which a correctness proof for an implementation that keeps each key's log apart would need.
- Pruning under the prospective reading, and pruning a key's log under partitioned evaluation.
- That each monitor instance belongs to one rule across the log (`Log.InstancesStable`), which no theorem uses.

**Known limits of the definitions.**

- A pin that is not symmetric, that is a pin to an attribute of the principal or resource (`pin dept = principal.dept`), isolates nothing: its logged value is never checked.
- The check that a decision supplies the scope entities a leaf reads ignores `has` guards, and does not cover provider arguments.
- Nothing bounds how far stamps may run ahead of the clock.
- The entity data of an event is not required to be canonical; its logged record and request context are.

## Building and checking

The specification is a Lake project with its own toolchain (Lean 4.34.0, named in `lean-toolchain`). It is not part of the package's Cargo workspace. From the repository root:

```bash
dogwood-lean/scripts/check.sh                         # the specification, its theorems and examples, and the theorems' axioms
LEAN_CC=/path/to/cc dogwood-lean/conformance/run.sh   # the comparison with the crate
```

The script runs `lake build`, which fails when a module does not parse or a proof does not close. Lean reports a declaration left `sorry`ed as a warning (`` declaration uses `sorry` ``), not as an error, so the script fails on that warning. Then it runs `lake env lean Axioms.lean`, which prints the axioms of each theorem that `Axioms.lean` names. Only `propext`, `Classical.choice` and `Quot.sound` may appear, and the script fails on any other axiom (the axioms of a theorem that rests on a `sorry` include `sorryAx`). It also fails when the number of theorems reported is not the number that `Axioms.lean` names. The archive the Rust crate links is built from the frontend alone, which reaches neither the theorems nor the examples, so a build of the crate does not check them.

The first build fetches cedar-spec `v4.14.0` and Batteries from GitHub. Where the C compiler that Lean bundles does not run (on an older glibc), the conformance executable needs `LEAN_CC` set to another C compiler. [`REFERENCE.md`](REFERENCE.md#building) gives the details, including how the Lean side and the Cargo side are kept on the same Cedar release.

`vendor/` holds the modules of cedar-lean and Batteries that the specification and the Lean frontend import, so that the crate's `lean-frontend` feature builds without network access. [`REFERENCE.md`](REFERENCE.md#building) says when to regenerate it.

## Where to read more

| Document | What it holds |
|---|---|
| [`REFERENCE.md`](REFERENCE.md) | The detailed reference: the modules, the rules, the main theorems, and the differences from the crate. |
| [`conformance/README.md`](conformance/README.md), [`conformance/probes/README.md`](conformance/probes/README.md) | The comparison with the crate: its method, its limits, the known disagreements, and the probes. |
| [`../dogwood-docs/guide/08-formal-specification.md`](../dogwood-docs/guide/08-formal-specification.md) | The guide's semi-formal reference (BNF, lowering, validation, and authorization), which cites this specification for the typing rules and the decision's checks. |
