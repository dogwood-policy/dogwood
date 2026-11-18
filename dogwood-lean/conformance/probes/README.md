# Probes

The corpora exercise few of the rules the specification adds, so these bundles do.
`conformance/run.sh` exports them as the group `Probes`. Each bundle has the guide's default event
schema, with `request` the decision kind and the universal `callerPrincipal` pin, and a
`policy.dw` whose first comment says what it probes. The validity and runtime probes share one
action schema: `OAuthUser` principals with a required `id` and a required `level`, `Gateway`
resources, a `Login` action, and a `Read` action whose `input` record has a required `user` and
an optional `note` and `level`. The probes of field names that hold a `.`, and those of fields of
an extension type, have a schema of their own. `conformance/probegen.py` writes them.

## Traces whose times do not strictly increase

An authorizer stamps each event it accepts with its clock reading, or one tick after the last
stamp when the reading is not later (`Dogwood.Spec.Ingest`). The crate takes the times of a trace
as given. The corpora contain no trace whose times do not strictly increase. The conformance run
reads each recorded time as its event's clock reading, in nanoseconds, stamps the trace, and
compares the specification over the stamped trace with the crate over the recorded times. It
reports each of these traces apart: the events stamped one tick after the last stamp, how many of
them the crate decided, and at how many events the verdicts differ. A verdict that differs is a
disagreement of stamping.

| Probe | Trace | The specification | The crate |
|---|---|---|---|
| `equal_timestamp_read` | the guide's `read_after_login` policy; a `Read` recorded at the time of the `Login` response before it | stamps the `Read` one tick after the response, and allows it | takes the time as given, and allows it |
| `decreasing_timestamp_read` | the same policy; a `Read` recorded earlier than the `Login` response before it | stamps the `Read` one tick after the response, so the login lies in its window, and allows it | takes the time as given, so the login lies "in the future", and denies it |
| `equal_timestamp_logout_read` | `Login` and `Logout` responses recorded at one time, then a `Read` that the logout forbids | stamps the `Logout` one tick after the `Login`, so the `Read` sees it, and denies the `Read` | ingests the `Logout` at its recorded time, and denies the `Read` too |

## Validity rules

| Probe | The rule | The specification | The crate |
|---|---|---|---|
| `validation_optional_unguarded` | a leaf reads the optional `context.input.note` with no `has` test | rejects it (optional attributes) | rejects it (optional attributes) |
| `validation_optional_guarded` | the same leaf after `when { context.input has note }` | accepts it: the preceding condition's fact guards the read | accepts it |
| `validation_duplicate_for_names` | `count for (t: Timepoint), (t: Timepoint)` | rejects it (binders) | rejects it (binders) |
| `validation_timepoint_ordered` | `s < t` on two timepoint variables | rejects it (timepoints) | rejects it (timepoints); its interpreter reads the ordering as false (`unorder_timepoints`) |
| `validation_string_ordered` | `u < context.input.user` on strings | rejects it (comparison operands) | rejects it |
| `validation_principal_id_attribute` | `principal.id` where `OAuthUser` declares a `String` `id` attribute | accepts it, as the attribute | accepts it |
| `validation_datetime_binder` | a `datetime` variable binds the `datetime` field `input.at`, and equals `context.input.since` | rejects it (binders): temporal conditions do not support `datetime` | rejects it (it accepted it while the crate supported the type) |
| `validation_datetime_argument` | `context.input.since`, a `datetime`, is the argument of the `datetime` field `input.at` | rejects it (extension types) | rejects it |
| `validation_datetime_wildcard` | a wildcard for the `datetime` field `input.at` | accepts it, and allows every `Read` after the login | accepts it, and decides alike |
| `validation_datetime_optional_unguarded` | the optional `datetime` attribute `context.input.later`, read with no `has` test | rejects it (optional attributes) | rejects it, and also reports the unsupported type (extension types), as the baseline expects |
| `validation_datetime_string_binder` | a `String` variable binds the `datetime` field `input.at` | rejects it (predicate arguments) | rejects it (predicate arguments) |
| `validation_datetime_string_literal` | a `String` literal for the `datetime` field `input.at` | rejects it (predicate arguments) | rejects it (predicate arguments) |

## Validity rules of `PolicySet.Valid`, one probe each

These probes have no trace, and share a schema of their own: the `Login` and `Read` actions of
the others, a `Ping` action whose principals are `OAuthUser`s and `Bot`s, an `OAuthUser` that
declares an `id` of type `Long` and can be in a `Group`, a second `OAuthUser` in the namespace
`Other`, and a `Read` input with a `datetime`, an `OAuthUser`, and two records of different
shapes. The provider probes declare `Risk::Score`, which takes a `String`, and `Risk::Chain`,
whose method `first` takes a `Set<Long>` after a stage that produces a `Set<String>`. For each
probe the specification rejects, the crate's validator reports a finding of the same category.
Both accept the other three: `principal in E` admits only the types that can be in `E`, a
provider argument needs no `has` guard, and `principal.id` is the attribute the entity type
declares, not the uid's id.

| Probe | The rule | Both |
|---|---|---|
| `validation_wildcard_operand` | `context.input.user == *` | reject it (placement) |
| `validation_undeclared_action_literal` | the action literal `Drupe::Action::"Lgoin"` | reject it (paths) |
| `validation_unparsable_decimal` | `decimal("1.23456")` | reject it (paths) |
| `validation_unqualified_binder_type` | `exists (u: OAuthUser)`, the type being `Drupe::OAuthUser` | reject it (binders) |
| `validation_entity_type_namespace` | an `Other::OAuthUser` for a field of type `Drupe::OAuthUser` | reject it (predicate arguments) |
| `validation_scope_root_per_environment` | on `Ping`, `principal` for a field of type `OAuthUser`, wrong when the principal is a `Bot` | reject it (predicate arguments) |
| `validation_binding_equality_entity_types` | `x == resource`, binding an `OAuthUser` variable to a `Gateway` | reject it (comparison operands) |
| `validation_extension_type_operand` | a `datetime` compared with a `String` | reject it (extension types) |
| `validation_record_operands` | two records of different shapes compared | reject it (comparison operands) |
| `validation_named_field_argument` | `requestId: 5`, the event schema typing it `String` | reject it (predicate arguments) |
| `validation_principal_id_declared_attribute` | `principal.id == 5`, `principal.id` being the declared `Long` attribute | accept it |
| `validation_principal_in_group` | `principal.level` under `principal in Drupe::Group::"staff"` on `Ping`, which no `Bot` can be in | accept it |
| `validation_attribute_typed_per_environment` | `principal.rank == principal.rank`, `rank` a `Long` on `OAuthUser` and a `String` on `Bot` | accept it (the crate used to reject it as ambiguous) |
| `validation_attribute_typed_per_environment_wrong_in_one` | `principal.rank == 5`, wrong for a `Bot` | reject it (comparison operands) |
| `validation_impossible_policy` | `principal is Drupe::Bot` on `Read`, which has no `Bot` principal | reject it (cedar) |
| `validation_context_read_whole` | `when { context == context }` in a rule with a temporal leaf | reject it (context reads) |
| `validation_temporal_reads_hoisted` | a leaf reads `context.policy_0__temporal_0` | reject it (paths) |
| `validation_provider_optional_argument` | `Risk::Score(context.input.note)`, `note` optional and unguarded | accept it |
| `validation_provider_argument_type` | `Risk::Score(principal)`, an entity for a `String` | reject it (providers) |
| `validation_provider_method_input` | `Risk::Chain().first()`, a `Set<String>` for a `Set<Long>` | reject it (providers) |
| `validation_compound_aggregate_event` | an undeclared event in an aggregate inside a compound operand | reject it (event names) |
| `validation_compound_aggregate_constant` | an aggregate inside a compound operand whose body does not vary with the timepoint | reject it (time dependence) |

## Lowering edge cases found by the Lean port of the frontend

A port of the frontend to Lean (`Dogwood.Frontend`, compared with the crate stage by stage by
`conformance/frontend-run.sh`) found these cases. The probes the crate rejects at lowering are
compared there, stage by stage; the others here, end to end.

| Probe | The input | Both |
|---|---|---|
| `runtime_root_common_type` | `Drupe`'s actions refer bare to a `LoginInput` the root namespace declares | derive `input.user` for the events, allow alice's `Read` after her login, and deny bob's |
| `validation_enum_parent` | `OAuthUser in [Application]` with `Application` enumerated | reject it (schema; the specification states the rule, `Schema.standardAncestors`), where Cedar accepts it |
| `runtime_pin_named_binder` | a leaf binds `__pin_ti0` and reads it inside a `previous` | allow alice's `Read` after her login: the rewrite's own binders do not capture it |
| `runtime_provider_decimal_type_name` | the namespace declares `type decimal = …`, and a provider's output field is a `decimal` | type the field by the extension type, and allow |
| `runtime_provider_quoted_field` | a provider's output field is named `content-type` | lower the rule (the shared provider type writes the name as a string), and allow |
| `validation_context_read_empty_record` | `when { context == {} }` in a rule with a temporal leaf | reject it (context reads) |
| `lowering_array_under_arithmetic` | an array constant in an aggregate that is an operand of `*` | reject it at lowering |
| `lowering_macro_error_span` | a Cedar macro called in a temporal block | reject it, at the call |
| `lowering_binding_value_operand` | a macro body binds `$x` to `$y + 1` before the count that binds `$y` | reject it, naming the value operand |
| `lowering_cyclic_common_type` | a context common type with an attribute `meta: A`, `type A = { x: A }` | reject it at lowering (a cycle) |
| `lowering_declared_hoisted_name` | `Read` declares `policy_0__temporal_0: Bool` | reject it at lowering, whatever the attribute's type |
| `lowering_declared_providers_record` | `Read` declares a `providers` record | reject it at lowering |

## Runtime conformance

| Probe | The data | The specification | The crate |
|---|---|---|---|
| `runtime_nonconforming_context` | a `Read` whose request context lacks the required `input.user` | fails the decision closed (nonconforming request context) | fails it closed too (nonconforming request) |
| `runtime_nonconforming_entities` | entity data giving `level` a `String` | fails the decision closed (nonconforming entity store) | fails it closed too |
| `runtime_caller_mismatch` | a `Read` that logs `callerPrincipal` as bob, by alice | fails the decision closed (nonconforming decision event) | fails it closed too (nonconforming decision event) |
| `runtime_nonconforming_history` | a `Login` response that logs `input.user` as a `Long` | ingestion rejects the event, so the later `Read` has no login to rely on | rejects the event too, and denies the `Read` |
| `runtime_principal_id_supplied` | entity data giving alice the `id` attribute `"mallory"` | reads the supplied attribute, as Cedar does, and denies | decides alike |
| `runtime_renamed_principal_pin_forged` | under `pin actor = principal`, mallory's Login response that logs `actor: alice` | ingestion rejects it, so alice's `Read` is denied until her own login | rejects it too, naming `actor`, and decides alike |
| `runtime_renamed_context_pin_forged` | under `pin sid = context.input.user`, a Login response by mallory that logs `sid: "alice"` | ingestion rejects it, so alice's `Read` is denied until a login in her own `sid` | rejects it too, naming `sid`, and decides alike |
| `runtime_attribute_pin_unchecked` | under `pin uid = principal.id`, an attribute pin, a Login response that logs `uid: "someone"` | ingests it, but it does not match alice's `Read`, which is denied until a login logs `uid: "alice"` | decides alike |
| `runtime_scopeless_history` | a `Login` response with no scope that logs alice as its caller, then alice's `Read` | ingestion rejects the response (the strict mirror rule), so the `Read` has no login to rely on, and is denied | under its default `MirrorRule::Strict`, rejects the response and denies the `Read` (under the opt-out `MirrorRule::Current` it would ingest it and allow) |
| `runtime_forged_rate_limit` | three scope-less `Read` requests that log alice as their caller, then alice's `Read`, under a limit of two per hour | ingestion rejects the forged requests, so alice's request is under her limit, and is allowed | under its default `MirrorRule::Strict`, fails each forged request closed without recording it, and allows alice's request (under the opt-out `MirrorRule::Current` it would record them and deny) |
| `runtime_missing_scope_entity` | a leaf that reads `principal.level` under a negation, and a `Read` without alice's entity data | fails the decision closed (missing scope entity); with the data supplied, decides as the crate does | adds a bare entity, so `!(principal.level < 3)` holds, and allows |

## Field names that hold a `.`

A path steps one level per `.`, and a Cedar attribute may have any string as its name. These
probes share an action schema whose `input` record has both an attribute named `"user.id"` and a
record `user` with an `id`, and policies that compare the field `input.user.id` with
`context.input.user.id`: both are the `id` inside `user`. The crate escapes each segment of a
path (`dogwood-language/src/field_path.rs`), so its request environment keeps the two paths apart,
and agrees with the specification. An environment that joined the segments with a plain `.` would
give the two paths one key, answer `context.input.user.id` with the attribute `"user.id"`, and
decide each `Read` of these probes the other way.

| Probe | The trace | Both |
|---|---|---|
| `runtime_dotted_attribute_permit` | a `Login`; a `Read` with the `Login`'s nested id and another `"user.id"`; a `Read` with bob's nested id and alice's `"user.id"` | allow the first `Read` and deny the second |
| `runtime_dotted_attribute_forbid` | the same, with a `Logout` that a `forbid` reads | block the first `Read` and allow the second |

## Found by generated runs

`conformance/gen-run.sh` generates bundles and runs both harnesses on them (see the conformance
README, "Generated runs"). These probes are the minimized bundles of what its runs found: one
defect of the Lean port of the frontend, one of the Lean port of the validator, and imprecisions
of the harnesses that would report a disagreement where there is none, or hide one. The last
column says what each probe checks.

| Probe | The input | What it checks |
|---|---|---|
| `lowering_folded_boolean_literals` | `when { true && true && temporal { … } } when { true } when { true }` | the Lean port folds `&&` of two Boolean literals, as Cedar's expression builder does, and lowers the rule as the crate does; both allow (frontend `cedarify`, `pipeline`) |
| `validation_context_read_own_leaf_name` | rule 0's Cedar part reads `context.policy_0__temporal_0`, its own leaf's name | the crate and its Lean validator reject it (context reads); the specification, through the bridge, sees the leaf, and accepts (the conformance baseline lists it); the Lean validator takes the reads from the authored rule, since in the lowered rule the author's read is the leaf's reference (frontend `validate`) |
| `validation_aggregate_operand_two_findings` | an aggregate on `Ping` whose pinned `callerPrincipal` cannot hold a `Bot` | both report a predicate-argument and a pin finding: the specification's typing check reports every problem of an operand |
| `validation_undeclared_field_term` | `nosuch: context.input.nosuch` | both report event names and paths: the specification's typing check also checks the term of an argument for an undeclared field |
| `validation_provider_unused_method_enum` | a provider whose method outputs a provider enum, called without the method | both accept, and allow: the bridge leaves out the method alone, not the whole declaration |
| `runtime_erring_rule_missing_scope_entity` | a rule reads `principal.level` in its Cedar part and its leaf; alice's `Read` has no entity data; another rule allows all | the runtime gap of a missing scope entity (the baseline lists it), not a disagreement of verdicts: the crate decided, though its diagnostics hold an error; on the data supplied both allow |
| `runtime_stamped_ingestion_change` | a rejected `Login` response, then a `Read` recorded before alice's `Login` response | the stamping disagreement alone (the baseline lists it), not also as a decision that ingestion changes |
| `lowering_unparsable_schema_and_array` | an action schema with a JSON-style escape, and an array in a predicate argument | the frontend `export` check counts the schema's rejection where the pipeline meets it |
| `lowering_unparsable_event_schema_and_provider_error` | an event schema that does not parse, and a provider enum outside its providers' namespaces | the same, for the event schema |
| `lowering_cyclic_action_hierarchy` | `Login` and `Read` each in the other | the frontend `pipeline` check compares Cedar's own schema errors by category, not by message |

## Cedar 4.14

These probes cover features of Cedar 4.14 that the crate, the Lean frontend and the specification
all follow. All agree.

| Probe | The input | Both |
|---|---|---|
| `validation_external_declarations` | the action schema declares `external entity Remote in [Gateway]` and `external action "Outside"` | reject the rule (Cedar: `schema is incomplete: … are declared `external` but not defined`; the specification's `complete`) |
| `lowering_external_enum_ancestor` | `external entity Remote in [Application]` with `Application` enumerated | reject the schema at lowering |
| `runtime_extended_has` | `context.input has meta.tag && context.input.meta.tag == "ok"`, one extended `has` | allow alice's `Read` with the tag after her login, deny it without |
| `runtime_extended_has_reserved` | `context.input has meta.if`, a path with a reserved word, lowered to the conjunction | allow alice's `Read` with the attribute after her login, deny it without |
