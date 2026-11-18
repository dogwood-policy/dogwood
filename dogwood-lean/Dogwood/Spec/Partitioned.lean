import Dogwood.Spec.Ingest

/-!
# Partitioned evaluation: one log per partition key, each log stamped on its own

An implementation can realize key-local semantics by keeping **one log per partition key**: it
files each event under its partition key (`EventSchema.partitionKey`, the logged values of the
universally pinned fields) and decides each event over its own key's log. Two kinds of
implementation do so:

* the crate's partitioned mode (`AuthorizerBuilder::partition_temporal`): the in-memory engine
  keeps one trace per key (`partition_value_of` in `engine.rs`), and evaluates the authored,
  pinned leaves of each decision over the trace of the decision event's key;
* an implementation that stores each key's log separately and stamps each log on its own.

## Stamps are per log

An implementation that keeps one log per key stamps each log on its own: an event's stamp is its
clock reading, or one tick after the stamp of **the last event of its own key's log** when the
reading is not later (`stampAfter`). This is the specification's stamping rule (`Trace.stamp`),
applied to each key's log instead of to one log of all events. Partitions served concurrently
have no single order of all events to stamp in, so per-log stamps are the stamps such an
implementation can assign.

## The definitions

The input is the stream of **arrivals**: the accepted events in arrival order, each with its clock
reading, as a `Trace` whose timestamps are the readings (the form `Trace.stamp` takes).

* `EventSchema.keyLog S ρ k`: the log of the key `k`, the arrivals of `ρ` whose event has the
  key `k`, in arrival order, with their readings;
* `EventSchema.partitionLog S ρ n e`: the log of `e`'s key as it stands once arrival `n` is
  appended;
* `PolicySet.PartLeafHolds ι P ρ n φ`: the value of a temporal leaf at arrival `n` under
  partitioned evaluation. The leaf, after pin injection (`φ.injectPins P.schema`), holds at the
  decision's position in the decision event's partition log, stamped on its own, with every
  timepoint of that log visible;
* `PolicySet.authorizePart ι P ω ρ n`: the decision under partitioned evaluation. It is
  `PolicySet.authorize` with each temporal leaf valued by `PartLeafHolds`.

## How partitioned evaluation relates to the single stamped log

`PolicySet.LeafHolds` and `PolicySet.authorize` decide over one stamped trace of all events, the
trace ingestion builds from the arrivals (`ρ.stamp`, `Dogwood.Thm.ingest_events`). The two
semantics agree in two cases:

* when the schema has no universal symmetric pin. Every event then has the same key, so there is
  one partition, whose log is the whole stream (`Dogwood.Thm.partLeafHolds_iff_leafHolds_of_noPins`,
  `Dogwood.Thm.authorizePart_eq_authorize_of_noPins`);
* when the readings strictly increase in arrival order across the whole stream, on a stream that
  suits partitioned evaluation (`EventSchema.Partitionable`, which every stream of conforming
  events does, `Dogwood.Thm.partitionable_of_strict`). Then stamping changes no reading, in any
  log (`Dogwood.Thm.partLeafHolds_iff_leafHolds`, `Dogwood.Thm.authorizePart_eq_authorize`).

They can differ when readings do not strictly increase across partitions. An event that arrives
at the reading of another key's event is stamped one tick later in the single log, but not in its
own key's log. At a window's edge, a shift of one tick changes a leaf's value
(`Dogwood.Examples.PartitionedStamps`).

The crate's partitioned mode does not stamp: an event carries its timestamp. On a stream whose
timestamps strictly increase within each partition, stamping a partition's log changes nothing, and
`PartLeafHolds` is the leaf's value over the partition with the events' own timestamps, which is
what the crate evaluates (`Dogwood.Thm.partLeafHolds_iff_of_strictlyIncreasing`).
-/

namespace Dogwood.Spec

open Temporal
open Cedar.Spec (EntityUID Response Value)

/-- **The log of the partition key `k`**: the arrivals of `ρ` whose event has the partition key
`k` (`EventSchema.partitionKey`), in arrival order, each with its clock reading. -/
def EventSchema.keyLog (S : EventSchema) (ρ : Trace) (k : List (Option Value)) : Trace :=
  ρ.filter fun q => decide (S.partitionKey q.event = k)

/-- **The log of the partition of `e` at arrival `n`**: the arrivals `ρ[0] … ρ[n]` whose event
has the partition key of `e`, in arrival order, each with its clock reading. When `e` is the event
of arrival `n`, the log's last entry is that arrival (`Dogwood.Thm.partitionLog_eq`). As a
function of a trace, it is `Dogwood.Thm.partitionOf` (`Dogwood.Thm.partitionLog_eq_partitionOf`).
The two semantics differ in what they stamp: partitioned evaluation stamps this log on its own,
while the single-log semantics stamps the stream of all arrivals and then takes the partition of
the stamped trace. -/
def EventSchema.partitionLog (S : EventSchema) (ρ : Trace) (n : Nat) (e : Event) : Trace :=
  S.keyLog (ρ.take (n + 1)) (S.partitionKey e)

/-- **A temporal leaf under partitioned evaluation.** The temporal leaf `φ` holds at arrival `n`
of the arrivals `ρ` (the accepted events, in arrival order, each with its clock reading) when the
decision event's partition is evaluated as a log of its own:

* the log is the arrivals `ρ[0] … ρ[n]` with the decision event's partition key
  (`EventSchema.partitionLog`);
* it is stamped on its own (`Trace.stamp`): each stamp is the event's reading, or one tick after
  the stamp before it **in this log** when the reading is not later;
* the leaf after pin injection, `φ.injectPins P.schema`, is evaluated at the decision's position,
  the log's last, with every timepoint of the log visible.

This is what an implementation that keeps one log per partition key, and stamps each log as
`Trace.stamp` does, computes. The crate's partitioned mode
(`AuthorizerBuilder::partition_temporal`) evaluates each event's leaves over its own partition
(`partition_value_of`), with the events' own timestamps; on timestamps that
strictly increase within each partition, that is this value
(`Dogwood.Thm.partLeafHolds_iff_of_strictlyIncreasing`).

The unfolding over a key's whole log is `Dogwood.Thm.partLeafHolds_iff_keyLog`. Without a
universal symmetric pin, there is one partition, and this is `PolicySet.LeafHolds` over the
stamped stream (`Dogwood.Thm.partLeafHolds_iff_leafHolds_of_noPins`). -/
def PolicySet.PartLeafHolds (ι : ImplChoices) (P : PolicySet) (ρ : Trace) (n : Nat)
    (φ : Formula) : Prop :=
  ∃ p, ρ[n]? = some p ∧
    Sat ι P.tickRate (P.schema.partitionLog ρ n p.event).stamp p.event (fun _ => True)
      Valuation.empty ((P.schema.partitionLog ρ n p.event).length - 1) (φ.injectPins P.schema)

/-- The leaf valuation of a decision at arrival `n`, whose event is `e`, under partitioned
evaluation: each temporal leaf by `PolicySet.PartLeafHolds`, each provider leaf by the output of
the providers `ω`. -/
noncomputable def PolicySet.partLeaves (ι : ImplChoices) (P : PolicySet) (ω : Provider.Providers)
    (ρ : Trace) (n : Nat) (e : Event) : Leaves where
  temporal φ := @decide (P.PartLeafHolds ι ρ n φ) (Classical.propDecidable _)
  provider c := (ω (c.resolve e)).leafValue

/-- The response of a decision at arrival `n`, whose event is `e`, under partitioned evaluation
and the reading `ι`: `PolicySet.respond`, with the leaf valuation of partitioned evaluation. -/
noncomputable def PolicySet.respondPart (ι : ImplChoices) (P : PolicySet) (ω : Provider.Providers)
    (ρ : Trace) (n : Nat) (e : Event) (pr rs : EntityUID) : Option Response :=
  ι.supervaluate fun ι' =>
    isAuthorized (P.partLeaves ι' ω ρ n e) (e.request pr rs) (P.decisionEntities e) P.policies

/-- **The decision under partitioned evaluation**: the outcome of the arrival `n` of the arrivals
`ρ`, when each temporal leaf is valued over the decision event's partition log, stamped on its own
(`PolicySet.PartLeafHolds`). The checks are `PolicySet.authorize`'s (`PolicySet.decideWith`); they
read the decision event only. This is the decision of an implementation that keeps one log per
partition key, and of an authorizer built with `AuthorizerBuilder::partition_temporal()` when
timestamps strictly increase within each partition. Without a universal symmetric pin it is
`PolicySet.authorize` over the stamped stream (`Dogwood.Thm.authorizePart_eq_authorize_of_noPins`),
and so it is when the readings strictly increase across the whole stream, on a stream that suits
partitioned evaluation (`Dogwood.Thm.authorizePart_eq_authorize`). -/
noncomputable def PolicySet.authorizePart (ι : ImplChoices) (P : PolicySet)
    (ω : Provider.Providers) (ρ : Trace) (n : Nat) : Outcome :=
  P.decideWith P.policies ω ρ n (P.respondPart ι ω ρ n)

end Dogwood.Spec
