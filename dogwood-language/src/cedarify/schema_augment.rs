//! Augment a Cedar schema with hoisted boolean context fields.
//!
//! For each [`ContextField`] produced by `cedarify`, add a required
//! `Bool` attribute to the named action's `context` record. Both passes
//! mutate a `cedar-policy-core` [`Fragment`] **in place**: `cedarify` parses
//! the base `.cedarschema` once, threads the fragment through the bool pass
//! and the provider pass, and converts it to the final schema afterward — so
//! there is no serialize/re-parse round-trip between passes.

use cedar_policy_core::FromNormalizedStr;
use cedar_policy_core::ast::Name;
use cedar_policy_core::validator::RawName;
pub(crate) use cedar_policy_core::validator::json_schema::Fragment;
use cedar_policy_core::validator::json_schema::{RecordType, Type, TypeOfAttribute, TypeVariant};
use smol_str::SmolStr;

use super::{ContextField, ProviderField, ScopedAction};
use std::collections::BTreeMap;

/// Add a required `Bool` field to each listed action's context record,
/// mutating `fragment` in place.
pub fn add_bool_context_fields(
    fragment: &mut Fragment<RawName>,
    fields: &[ContextField],
) -> Result<(), String> {
    if fields.is_empty() {
        return Ok(());
    }
    inline_context_references(fragment)?;
    for field in fields {
        add_one(fragment, field)?;
    }
    Ok(())
}

/// Replace every action context that is declared as a *type reference*
/// (`context: SomeCommonType`) with an inlined clone of the referenced
/// record, so the grafting passes below can insert hoisted fields into it.
///
/// Cedar allows an action's context to be a common-type reference — either
/// a [`Type::CommonTypeRef`] or an entity-or-common reference
/// ([`TypeVariant::EntityOrCommon`]) that names a common type. The grafting
/// passes mutate the context *record in place*, and mutating the shared
/// common type instead would be wrong (it may be referenced from non-context
/// positions, where a `providers`/temporal field must not appear). So each
/// referencing action gets its own inlined copy.
///
/// **All name-resolution decisions are Cedar's own.** The fragment is first
/// run through Cedar's public qualification pipeline
/// ([`Fragment::to_internal_name_fragment_with_resolved_types`]), which
/// applies Cedar's conditional-qualification semantics to every name — each
/// reference resolved relative to the namespace where it is lexically
/// written, `__cedar` primitive/extension aliasing included — yielding a
/// fragment in which every type reference is a fully-qualified
/// [`InternalName`]. Our remaining walk is decision-free: exact-match map
/// chasing to the terminal type, then a normalization of the resolved type
/// (see [`normalize_resolved_type`]) that deep-inlines nested common-type
/// references and pins bare builtin aliases to `__cedar::`, and a
/// name-preserving conversion back into the `RawName` fragment — so cloning
/// across namespaces cannot re-interpret any name.
///
/// Idempotent: an already-inline context is left untouched, so running this
/// at the start of both grafting passes (and across repeated lowerings of a
/// fed-forward augmented schema) is safe.
fn inline_context_references(fragment: &mut Fragment<RawName>) -> Result<(), String> {
    // Fast path: nothing to do unless some action context is a reference.
    let any_reference = fragment.0.values().any(|ns| {
        ns.actions.values().any(|a| {
            a.applies_to
                .as_ref()
                .is_some_and(|ap| context_reference_name(&ap.context.0).is_some())
        })
    });
    if !any_reference {
        return Ok(());
    }

    // Cedar's own resolution: every type reference in `qualified` is a
    // fully-qualified InternalName, resolved by Cedar's rules.
    let qualified = fragment
        .to_internal_name_fragment_with_resolved_types()
        .map_err(|e| format!("resolve schema type references: {e}"))?;

    // All common-type definitions, keyed by fully-qualified name string.
    let mut defs: BTreeMap<String, &Type<cedar_policy_core::ast::InternalName>> = BTreeMap::new();
    for (ns_name, ns) in qualified.0.iter() {
        for (id, ct) in ns.common_types.iter() {
            let full = match ns_name {
                Some(n) => format!("{n}::{}", id.as_ref()),
                None => id.as_ref().to_string(),
            };
            defs.insert(full, &ct.ty);
        }
    }
    // An acyclic chain cannot be longer than the number of definitions;
    // cycles (which Cedar also rejects, at ValidatorSchema construction)
    // are the only way to exceed this bound.
    let bound = defs.len() + 1;
    // Serialized view of the definitions for the normalization pass
    // (loop-invariant across referencing actions).
    let defs_json: BTreeMap<String, serde_json::Value> = defs
        .iter()
        .map(|(k, v)| Ok((k.clone(), serde_json::to_value(v)?)))
        .collect::<Result<_, serde_json::Error>>()
        .map_err(|e| format!("serialize common-type definitions: {e}"))?;

    // Phase A (immutable): resolve each referencing action's context to its
    // terminal type via exact fully-qualified lookups, then convert the
    // resolved type back to the RawName representation. The conversion is a
    // serde round-trip: names serialize as their fully-qualified strings,
    // which parse back as (qualified) `RawName`s — no renaming decisions.
    let mut replacements: Vec<(Option<Name>, SmolStr, Type<RawName>)> = Vec::new();
    for (ns_key, ns) in qualified.0.iter() {
        for (action_id, action) in ns.actions.iter() {
            let Some(applies_to) = action.applies_to.as_ref() else {
                continue;
            };
            let mut current = &applies_to.context.0;
            if context_reference_name(current).is_none() {
                continue; // already inline — leave as is
            }
            let mut steps = 0usize;
            while let Some(name) = context_reference_name(current) {
                steps += 1;
                if steps > bound {
                    return Err(format!(
                        "action `{action_id}` context reference is cyclic and cannot be resolved"
                    ));
                }
                match defs.get(&name) {
                    Some(next) => current = next,
                    // Not a common type — a builtin/extension alias left
                    // bare by the pipeline (pinned to `__cedar::` in the
                    // normalization pass) reaching the terminal position:
                    // stop chasing; the downstream record check reports a
                    // non-record context against the action. (Undefined and
                    // entity names never reach here — Cedar's qualification
                    // pipeline errors first, with its own diagnostics.)
                    None => break,
                }
            }
            let as_json = serde_json::to_value(current)
                .map_err(|e| format!("serialize resolved context type: {e}"))?;
            // Post-pass on the serialized type (see `normalize_resolved_type`):
            // deep-inline any nested common-type references and pin bare
            // builtin-alias names to their explicit `__cedar::` spelling, so
            // the clone cannot be re-interpreted in the target namespace.
            let normalized = normalize_resolved_type(as_json, &defs_json)
                .map_err(|m| format!("action `{action_id}`: {m}"))?;
            let raw: Type<RawName> = serde_json::from_value(normalized)
                .map_err(|e| format!("convert resolved context type: {e}"))?;
            replacements.push((ns_key.clone(), action_id.clone(), raw));
        }
    }
    // Phase B (mutable): apply to the RawName fragment.
    for (ns_key, action_id, resolved) in replacements {
        let action = fragment
            .0
            .get_mut(&ns_key)
            .and_then(|ns| ns.actions.get_mut(&action_id))
            .ok_or("internal: action vanished between phases")?;
        let applies_to = action
            .applies_to
            .as_mut()
            .ok_or("internal: appliesTo vanished between phases")?;
        applies_to.context.0 = resolved;
    }
    Ok(())
}

/// The referenced type name if `ty` is a type reference, else `None`.
fn context_reference_name<N: std::fmt::Display>(ty: &Type<N>) -> Option<String> {
    match ty {
        Type::CommonTypeRef { type_name, .. } => Some(type_name.to_string()),
        Type::Type {
            ty: TypeVariant::EntityOrCommon { type_name },
            ..
        } => Some(type_name.to_string()),
        _ => None,
    }
}

/// Normalize a resolved context type (as serialized JSON) so that inlining
/// it into ANY namespace cannot re-interpret a name:
///
/// * **Nested common-type references are deep-inlined.** Cedar's
///   qualification pipeline fully qualifies USER-defined names, but a
///   reference it resolved to a *builtin alias* (the empty-namespace
///   `decimal`/`datetime`/`duration`/`ipaddr` aliases it registers) stays
///   bare — and a bare name re-parsed in the target namespace is subject
///   to conditional qualification there, where a same-named common type
///   (legal: shadowing a builtin is only a warning) captures it.
///   Deep-inlining removes every nested reference we have a definition
///   for, mirroring what Cedar's own `CommonTypeResolver` does.
/// * **Remaining bare extension-type names are pinned to `__cedar::`.**
///   After deep-inlining, a bare name with no definition in `defs` can
///   only be a builtin alias; `__cedar::<name>` is its explicit,
///   capture-proof spelling (verified to parse, validate, and compile).
///
/// Cycles among common types are only rejected later (at ValidatorSchema
/// construction), so the per-chain visited-set check below must not hang;
/// it reports a cycle if one chase revisits a name. Sibling references to
/// the same type are NOT a cycle — each attribute's chase is independent.
fn normalize_resolved_type(
    ty: serde_json::Value,
    defs: &BTreeMap<String, serde_json::Value>,
) -> Result<serde_json::Value, String> {
    let ext_names: std::collections::BTreeSet<String> =
        cedar_policy_core::extensions::Extensions::all_available()
            .ext_types()
            .map(|n| n.to_string())
            .collect();
    normalize_value(ty, defs, &ext_names)
}

fn normalize_value(
    mut ty: serde_json::Value,
    defs: &BTreeMap<String, serde_json::Value>,
    ext_names: &std::collections::BTreeSet<String>,
) -> Result<serde_json::Value, String> {
    // In attribute position this node is a flattened `TypeOfAttribute`:
    // the type's own keys plus `required` / `annotations`. Substituting a
    // definition wholesale would drop those (and Cedar defaults `required`
    // to TRUE, silently making optional attributes required — a validator
    // soundness bug). Preserve them across substitution.
    let preserved: Vec<(String, serde_json::Value)> = ty
        .as_object()
        .map(|o| {
            ["required", "annotations"]
                .iter()
                .filter_map(|k| o.get(*k).map(|v| ((*k).to_string(), v.clone())))
                .collect()
        })
        .unwrap_or_default();

    // Chase this node's chain of common-type references. The cycle check
    // is per chain (a chase revisiting a name), not a global budget —
    // sibling attributes referencing the same type are legal fan-out.
    let mut visited: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    let mut substituted = false;
    while let Some(name) = ty
        .as_object()
        .and_then(|o| o.get("type"))
        .and_then(serde_json::Value::as_str)
        .map(str::to_string)
    {
        if let Some(def) = defs.get(&name) {
            if !visited.insert(name) {
                return Err(
                    "context type reference chain is cyclic and cannot be resolved".to_string(),
                );
            }
            ty = def.clone();
            substituted = true;
            continue;
        }
        if ext_names.contains(&name) {
            // A builtin alias left bare by the qualification pipeline: pin
            // it to the explicit `__cedar::` spelling.
            ty.as_object_mut()
                .expect("checked object above")
                .insert("type".into(), format!("__cedar::{name}").into());
        }
        break;
    }
    if substituted && let Some(obj) = ty.as_object_mut() {
        for (k, v) in preserved {
            obj.insert(k, v);
        }
    }
    // Recurse into structural children.
    if let Some(obj) = ty.as_object_mut() {
        if let Some(attrs) = obj
            .get_mut("attributes")
            .and_then(serde_json::Value::as_object_mut)
        {
            let keys: Vec<String> = attrs.keys().cloned().collect();
            for k in keys {
                let v = attrs.remove(&k).expect("key just listed");
                attrs.insert(k, normalize_value(v, defs, ext_names)?);
            }
        }
        if let Some(el) = obj.remove("element") {
            obj.insert("element".into(), normalize_value(el, defs, ext_names)?);
        }
    }
    Ok(ty)
}

fn add_one(fragment: &mut Fragment<RawName>, field: &ContextField) -> Result<(), String> {
    // EVERY arm goes through the one resolution. A leaf's hoisted field must exist on
    // exactly the actions the validator will check it against, and the validator reads
    // the same `scope_target_actions` result — so resolving separately here, however
    // simple the arm looks, is how the two drift. When they drift the symptom is Cedar
    // reporting the hoisted field missing on an action, which is the defect this
    // resolution exists to prevent.
    //
    // The resolution already drops actions that cannot receive a request, so a pure
    // action group named in a list is not an error: naming a group names its members.
    // A named action the schema does not DECLARE is still an error, raised below.
    for (namespace, action_id) in scope_target_actions(&field.action, fragment)? {
        add_bool_to_named_action(fragment, &field.field_name, &namespace, &action_id)?;
    }
    Ok(())
}

/// Add the bool field to one named `(namespace, action_id)` in the schema.
fn add_bool_to_named_action(
    fragment: &mut Fragment<RawName>,
    field_name: &str,
    namespace: &str,
    action_id: &str,
) -> Result<(), String> {
    let ns_key = ns_key(namespace)?;
    let ns = fragment
        .0
        .get_mut(&ns_key)
        .ok_or_else(|| format!("namespace `{namespace}` not found in schema"))?;
    let action = ns
        .actions
        .get_mut(&SmolStr::from(action_id))
        .ok_or_else(|| format!("action `{action_id}` not found in schema"))?;
    add_bool_to_action(action, field_name, action_id)
}

/// Cedar schema namespaces are keyed by `Option<Name>`; an empty
/// namespace is the `None` key.
fn ns_key(namespace: &str) -> Result<Option<Name>, String> {
    if namespace.is_empty() {
        Ok(None)
    } else {
        Name::from_normalized_str(namespace)
            .map(Some)
            .map_err(|e| format!("bad namespace `{namespace}`: {e}"))
    }
}

/// Add a required `Bool` `field_name` to one action's context record.
fn add_bool_to_action(
    action: &mut cedar_policy_core::validator::json_schema::ActionType<RawName>,
    field_name: &str,
    action_id: &str,
) -> Result<(), String> {
    let applies_to = action
        .applies_to
        .as_mut()
        .ok_or_else(|| format!("action `{action_id}` has no appliesTo"))?;

    match &mut applies_to.context.0 {
        Type::Type { ty, .. } => match ty {
            TypeVariant::Record(record) => {
                record.attributes.insert(
                    SmolStr::from(field_name),
                    TypeOfAttribute {
                        ty: Type::Type {
                            ty: TypeVariant::Boolean,
                            loc: None,
                        },
                        required: true,
                        annotations: Default::default(),
                    },
                );
                Ok(())
            }
            _ => Err(format!("action `{action_id}` context is not a record type")),
        },
        _ => Err(format!(
            "action `{action_id}` context does not resolve to a record type \
             (an action's context must be a record)"
        )),
    }
}

/// Add a `providers` record to EVERY action's context, whose fields are the
/// hoisted information-provider outputs typed from the provider
/// declarations. Multiple provider fields are grouped into a single
/// `providers: { ... }` record per action.
///
/// **Every action, not just the rule's scope targets.** Provider execution
/// is unconditional: a provider may be evaluated for any decision event
/// (see the provider contract in the guide, 05-information-providers), and
/// `build_context` binds every provider's output into every decision
/// event's context. The declared schema must match that runtime shape, so
/// the hoisted field is declared on every action that can receive a
/// request. Actions without an `appliesTo` (pure action groups) receive no
/// context and are skipped.
///
/// The field types are recovered by synthesizing a tiny `.cedarschema`
/// common type, parsing it with Cedar's own parser (so arbitrary nested
/// record/set/decimal types are handled correctly), and grafting the
/// resulting record `Type` into each action's context.
///
/// **Additive across passes.** If an action's context *already* carries a
/// `providers` record (from a prior augmentation of the same base schema —
/// e.g. incremental / repeated lowering that feeds an augmented schema
/// forward), this pass's fields are *merged into* that record rather than
/// replacing it, so earlier providers survive. Field names are namespaced by
/// their rule key (see [`crate::cedarify::rule_key`]), so distinct lowerings
/// never collide; a name that does recur (the same set re-lowered) simply
/// overwrites with an identically-typed field, which is a no-op.
pub fn add_provider_context_fields(
    fragment: &mut Fragment<RawName>,
    fields: &[ProviderField],
) -> Result<(), String> {
    if fields.is_empty() {
        return Ok(());
    }
    // A context declared as a common-type reference (`context: SomeType`)
    // must be inlined before hoisted fields can be inserted into it.
    inline_context_references(fragment)?;
    // Every action with an appliesTo, across every namespace in the schema.
    let all_actions: Vec<(String, String)> = fragment
        .0
        .iter()
        .flat_map(|(ns_name, ns)| {
            let ns_str = ns_name.as_ref().map(|n| n.to_string()).unwrap_or_default();
            ns.actions
                .iter()
                .filter(|(_, a)| a.applies_to.is_some())
                .map(move |(id, _)| (ns_str.clone(), id.to_string()))
        })
        .collect();

    // Synthesize `type __PR = { f1: T1, f2: T2 };` once and parse it to
    // recover each field's Cedar `Type<RawName>`. (This parses a tiny
    // *synthetic* schema, not the base one — it is how we recover
    // arbitrary nested record/set/decimal field types.) Loop-invariant:
    // the same attribute record is grafted onto every action.
    let attrs = fields
        .iter()
        .map(|f| format!("{}: {}", f.field_name, f.cedar_type))
        .collect::<Vec<_>>()
        .join(", ");
    let synth = format!("type __PR = {{ {attrs} }};");
    let (synth_frag, _) = Fragment::<RawName>::from_cedarschema_str(
        &synth,
        cedar_policy_core::extensions::Extensions::all_available(),
    )
    .map_err(|e| format!("synthesize providers type: {e} (from `{synth}`)"))?;
    let pr_record = synth_frag
        .0
        .get(&None)
        .and_then(|ns| ns.common_types.values().next())
        .map(|ct| ct.ty.clone())
        .ok_or("internal: synthesized providers type missing")?;

    // The fields this pass contributes, as a record's attribute map.
    let new_attrs = match pr_record {
        Type::Type {
            ty: TypeVariant::Record(record),
            ..
        } => record.attributes,
        _ => return Err("internal: synthesized providers type is not a record".to_string()),
    };

    for (namespace, action_id) in all_actions {
        let ns_key = ns_key(&namespace)?;
        let ns = fragment
            .0
            .get_mut(&ns_key)
            .ok_or_else(|| format!("namespace `{namespace}` not found"))?;
        let action = ns
            .actions
            .get_mut(&SmolStr::from(action_id.as_str()))
            .ok_or_else(|| format!("action `{action_id}` not found"))?;
        let applies_to = action
            .applies_to
            .as_mut()
            .ok_or_else(|| format!("action `{action_id}` has no appliesTo"))?;

        insert_provider_record(&mut applies_to.context.0, new_attrs.clone(), &action_id)?;
    }

    Ok(())
}

/// Insert (or merge) a `providers` record carrying `new_attrs` into one
/// action's `context` record.
fn insert_provider_record(
    context: &mut Type<RawName>,
    new_attrs: BTreeMap<SmolStr, TypeOfAttribute<RawName>>,
    action_id: &str,
) -> Result<(), String> {
    match context {
        Type::Type { ty, .. } => match ty {
            TypeVariant::Record(record) => {
                match record.attributes.get_mut(&SmolStr::from("providers")) {
                    // A `providers` record already exists (a prior pass, or
                    // an earlier lowering whose augmented schema was fed
                    // forward): MERGE this pass's fields into it so earlier
                    // providers are preserved, rather than replacing the
                    // whole record.
                    Some(TypeOfAttribute {
                        ty:
                            Type::Type {
                                ty: TypeVariant::Record(existing),
                                ..
                            },
                        ..
                    }) => {
                        existing.attributes.extend(new_attrs);
                        Ok(())
                    }
                    // A `providers` attribute exists but is not an inline
                    // record — a schema we did not produce. Refuse rather
                    // than silently clobber it.
                    Some(_) => Err(format!(
                        "action `{action_id}` already has a `providers` attribute that \
                         is not an inline record; cannot merge hoisted provider fields \
                         into it"
                    )),
                    // First provider pass for this action: install the record.
                    None => {
                        record.attributes.insert(
                            SmolStr::from("providers"),
                            TypeOfAttribute {
                                ty: Type::Type {
                                    ty: TypeVariant::Record(RecordType {
                                        attributes: new_attrs,
                                        additional_attributes: false,
                                    }),
                                    loc: None,
                                },
                                required: true,
                                annotations: Default::default(),
                            },
                        );
                        Ok(())
                    }
                }
            }
            _ => Err(format!("action `{action_id}` context is not a record")),
        },
        _ => Err(format!(
            "action `{action_id}` context does not resolve to a record type \
             (an action's context must be a record)"
        )),
    }
}

/// The concrete `(namespace, action_id)` actions a scope attaches to. Concrete → that one action; List → each listed action plus, for
/// any action that is a *group* (has descendants), its transitive descendants;
/// Unconstrained → every action in the schema.
pub fn scope_target_actions(
    action: &ScopedAction,
    fragment: &Fragment<RawName>,
) -> Result<Vec<(String, String)>, String> {
    let mut out: Vec<(String, String)> = Vec::new();
    match action {
        ScopedAction::Concrete(a) => out.push(a.clone()),
        ScopedAction::List(list) => {
            for a in list {
                collect_action_and_descendants(a, fragment, &mut out);
            }
        }
        ScopedAction::Unconstrained => {
            for (ns_key, ns) in fragment.0.iter() {
                let namespace = ns_key.as_ref().map(|n| n.to_string()).unwrap_or_default();
                for action_id in ns.actions.keys() {
                    out.push((namespace.clone(), action_id.to_string()));
                }
            }
        }
    }
    // Drop actions that cannot receive a request. A PURE action group (no
    // `appliesTo`) has no principal, resource or context of its own, so it is
    // never a target: Cedar validates a group-scoped policy against the group's
    // MEMBERS. An APPLIABLE group — one that declares `appliesTo` and also has
    // members — is kept, because it contributes its own request environment
    // alongside its members'.
    // Drop only actions that are DECLARED but not appliable. An action the schema does
    // not declare at all must NOT be dropped: silently removing it hides the real
    // diagnostic ("action `X` not found in schema") and lets the grafting pass skip a
    // named action, after which Cedar reports the hoisted field missing on the actions
    // that WERE grafted — an internal field name in a user-facing error, for what is
    // usually a typo. `add_bool_to_named_action` still raises the good error for a
    // declared-but-unappliable name reached through the Concrete arm.
    out.retain(|(namespace, action_id)| {
        !action_is_declared(fragment, namespace, action_id)
            || action_is_appliable(fragment, namespace, action_id)
    });
    // De-duplicate: a group and one of its descendants may both be listed, and
    // an action reachable by two paths would otherwise be visited twice.
    out.sort();
    out.dedup();
    Ok(out)
}

/// Whether the schema declares `(namespace, action_id)` as an action at all.
fn action_is_declared(fragment: &Fragment<RawName>, namespace: &str, action_id: &str) -> bool {
    ns_key(namespace).is_ok_and(|k| {
        fragment
            .0
            .get(&k)
            .is_some_and(|ns| ns.actions.contains_key(action_id))
    })
}

/// Whether `(namespace, action_id)` declares an `appliesTo`, i.e. can receive a
/// request and therefore has a context record to graft a hoisted field into. A
/// pure action group declares none.
fn action_is_appliable(fragment: &Fragment<RawName>, namespace: &str, action_id: &str) -> bool {
    let Ok(ns_key) = ns_key(namespace) else {
        return false;
    };
    fragment
        .0
        .get(&ns_key)
        .and_then(|ns| ns.actions.get(action_id))
        .and_then(|action| action.applies_to.as_ref())
        // A Cedar-syntax action declared with no `appliesTo` still parses to
        // `Some(ApplySpec)`, with EMPTY principal and resource lists — so testing
        // `applies_to.is_some()` alone reports a pure group as appliable. What
        // makes an action reachable by a request is having at least one principal
        // AND one resource type it applies to.
        .is_some_and(|spec| !spec.principal_types.is_empty() && !spec.resource_types.is_empty())
}

/// Push `action` and — if it is a group (some action lists it via `memberOf`) —
/// every transitive descendant, onto `out`.
fn collect_action_and_descendants(
    action: &(String, String),
    fragment: &Fragment<RawName>,
    out: &mut Vec<(String, String)>,
) {
    out.push(action.clone());
    // Walk `memberOf` edges: any action whose parents include `action` is a
    // direct child; recurse to reach the full subtree.
    let mut stack = vec![action.clone()];
    while let Some(parent) = stack.pop() {
        for (ns_key, ns) in fragment.0.iter() {
            let namespace = ns_key.as_ref().map(|n| n.to_string()).unwrap_or_default();
            for (child_id, child) in ns.actions.iter() {
                let is_child = child.member_of.iter().flatten().any(|m| {
                    // A parent ref's `ty` is the action *type* (e.g.
                    // `Drupe::Action`); its namespace is the parent action's
                    // namespace. `ty == None` is the `Action` shorthand, meaning
                    // the parent is in the child's own namespace. Compare on
                    // (namespace, id).
                    // The parent action's namespace. A member ref's `ty` is the
                    // action *type* (e.g. `App::Action`). Its namespace prefix
                    // is the parent's namespace — but an *unqualified* `Action`
                    // ref (written `Action::"X"` inside `namespace App`, so `ty`
                    // is `Action` with an empty namespace, or the `None`
                    // shorthand) resolves to the CHILD's own namespace, not the
                    // empty namespace. Only an explicitly-qualified
                    // `Other::Action` ref is cross-namespace.
                    let m_ns = match &m.ty {
                        Some(ty) => {
                            let ns = ty.qualify_with(None).namespace();
                            if ns.is_empty() { namespace.clone() } else { ns }
                        }
                        None => namespace.clone(),
                    };
                    m_ns == parent.0 && m.id.as_str() == parent.1
                });
                if is_child {
                    let entry = (namespace.clone(), child_id.to_string());
                    if !out.contains(&entry) {
                        out.push(entry.clone());
                        stack.push(entry);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::Span;
    use crate::extension::provider::ast::Invocation;

    const BASE_SCHEMA: &str = r#"
        namespace Drupe {
          type ReadInput = { document: String };
          entity Gateway;
          entity OAuthUser;
          action "Read" appliesTo {
            principal: [OAuthUser],
            resource: [Gateway],
            context: { input: ReadInput }
          };
        }
    "#;

    /// A minimal provider leaf on `Drupe::Read` with the given field name
    /// and a `Bool` output type.
    fn provider_field(field_name: &str) -> ProviderField {
        ProviderField {
            action: ScopedAction::Concrete(("Drupe".to_string(), "Read".to_string())),
            target_actions: vec![("Drupe".to_string(), "Read".to_string())],
            field_name: field_name.to_string(),
            cedar_type: "Bool".to_string(),
            body_base: 0,
            invocation: Invocation {
                span: Span { start: 0, end: 0 },
                function: vec!["Risk".to_string(), "Score".to_string()],
                args: vec![],
            },
            methods: vec![],
        }
    }

    /// Helper: parse a `.cedarschema` string into a fragment.
    fn parse(text: &str) -> Fragment<RawName> {
        Fragment::<RawName>::from_cedarschema_str(
            text,
            cedar_policy_core::extensions::Extensions::all_available(),
        )
        .expect("schema parses")
        .0
    }

    /// Feeding an already-augmented schema back through
    /// `add_provider_context_fields` (as incremental / repeated lowering does)
    /// must PRESERVE the earlier pass's provider fields, not replace them.
    #[test]
    fn provider_augmentation_is_additive_across_passes() {
        // Pass 1: augment the base schema with one provider field.
        let mut fragment = parse(BASE_SCHEMA);
        add_provider_context_fields(&mut fragment, &[provider_field("ruleA_0_p_0")]).unwrap();
        let after_a = fragment.to_cedarschema().unwrap();
        assert!(
            after_a.contains("ruleA_0_p_0"),
            "pass 1 field missing: {after_a}"
        );

        // Pass 2: feed pass 1's OUTPUT back in and augment with a second,
        // distinctly-named provider field (as a second lowering with a
        // different distincter would produce). Re-parsing here models the
        // feed-forward path, where a prior lowering's serialized augmented
        // schema is the next lowering's base.
        let mut fragment_b = parse(&after_a);
        add_provider_context_fields(&mut fragment_b, &[provider_field("ruleB_0_p_0")]).unwrap();
        let after_b = fragment_b.to_cedarschema().unwrap();

        // Both providers must survive in the final schema — the earlier one is
        // not clobbered by the later pass.
        assert!(
            after_b.contains("ruleA_0_p_0"),
            "earlier provider field was dropped on re-augmentation: {after_b}"
        );
        assert!(
            after_b.contains("ruleB_0_p_0"),
            "later provider field missing: {after_b}"
        );

        // And the result is still a single, well-formed schema that parses.
        let _ = parse(&after_b);
    }

    #[test]
    fn provider_augmentation_feed_forward_accumulates_on_every_action() {
        // Feed-forward over a MULTI-ACTION schema: with graft-everywhere,
        // each pass must merge its field into EVERY action's providers
        // record, and a second lowering over the serialized result must
        // accumulate (not clobber) on every action.
        let schema = r#"
            namespace App {
              entity User;
              entity Doc;
              action "Read" appliesTo {
                principal: [User], resource: [Doc],
                context: { input: { doc: String } }
              };
              action "Write" appliesTo {
                principal: [User], resource: [Doc],
                context: { input: { doc: String } }
              };
            }
        "#;
        let mut fragment = parse(schema);
        add_provider_context_fields(&mut fragment, &[provider_field("ruleA_0_p_0")]).unwrap();
        let after_a = fragment.to_cedarschema().unwrap();

        let mut fragment_b = parse(&after_a);
        add_provider_context_fields(&mut fragment_b, &[provider_field("ruleB_0_p_0")]).unwrap();

        // Both fields present on BOTH actions' contexts after the second pass.
        for action in ["Read", "Write"] {
            let ctx = &fragment_b.0[&ns_key("App").unwrap()].actions[&SmolStr::from(action)]
                .applies_to
                .as_ref()
                .unwrap()
                .context
                .0;
            let Type::Type {
                ty: TypeVariant::Record(record),
                ..
            } = ctx
            else {
                panic!("action {action} context not a record after augmentation");
            };
            let Some(TypeOfAttribute {
                ty:
                    Type::Type {
                        ty: TypeVariant::Record(providers),
                        ..
                    },
                ..
            }) = record.attributes.get(&SmolStr::from("providers"))
            else {
                panic!("action {action} has no providers record");
            };
            for field in ["ruleA_0_p_0", "ruleB_0_p_0"] {
                assert!(
                    providers.attributes.contains_key(&SmolStr::from(field)),
                    "action {action} missing provider field {field} after feed-forward"
                );
            }
        }
    }

    // ─── Unconstrained and list scope augmentation ───────────────────

    const MULTI_ACTION_SCHEMA: &str = r#"
        namespace App {
          entity User;
          entity Doc;
          action "Read" appliesTo {
            principal: [User], resource: [Doc],
            context: { input: { doc: String } }
          };
          action "Write" appliesTo {
            principal: [User], resource: [Doc],
            context: { input: { doc: String } }
          };
          action "Delete" appliesTo {
            principal: [User], resource: [Doc],
            context: { input: { doc: String } }
          };
        }
    "#;

    fn bool_field(field_name: &str, action: ScopedAction) -> ContextField {
        use crate::extension::temporal::Temporal;
        // A dummy temporal leaf — the schema augmentation doesn't inspect it,
        // it just carries it for authorize-time evaluation.
        let temporal = Temporal::parse(
            "formerly(action == Action::\"Read\")",
            Span { start: 0, end: 0 },
        )
        .expect("dummy temporal parses");
        ContextField {
            target_actions: Vec::new(),
            principal: crate::cedarify::ScopeConstraint::Any,
            resource: crate::cedarify::ScopeConstraint::Any,
            action,
            field_name: field_name.to_string(),
            temporal,
        }
    }

    #[test]
    fn unconstrained_scope_augments_all_actions() {
        let mut fragment = parse(MULTI_ACTION_SCHEMA);
        let field = bool_field("policy_0__temporal_0", ScopedAction::Unconstrained);
        add_bool_context_fields(&mut fragment, &[field]).unwrap();
        let text = fragment.to_cedarschema().unwrap();
        // The field must appear on all three actions.
        let count = text.matches("policy_0__temporal_0").count();
        assert_eq!(
            count, 3,
            "expected field on all 3 actions, got {count} in:\n{text}"
        );
    }

    #[test]
    fn list_scope_augments_only_listed_actions() {
        let mut fragment = parse(MULTI_ACTION_SCHEMA);
        let field = bool_field(
            "policy_0__temporal_0",
            ScopedAction::List(vec![
                ("App".to_string(), "Read".to_string()),
                ("App".to_string(), "Write".to_string()),
            ]),
        );
        add_bool_context_fields(&mut fragment, &[field]).unwrap();
        let text = fragment.to_cedarschema().unwrap();
        // Field appears on Read and Write (2 times), not on Delete.
        let count = text.matches("policy_0__temporal_0").count();
        assert_eq!(
            count, 2,
            "expected field on 2 actions, got {count} in:\n{text}"
        );
    }

    // ─── Provider group expansion ────────────────────────────────────

    const HIERARCHY_SCHEMA: &str = r#"
        namespace App {
          entity User;
          entity Doc;
          action "ReadWrite" appliesTo {
            principal: [User], resource: [Doc],
            context: { input: { x: String } }
          };
          action "Read" in [Action::"ReadWrite"] appliesTo {
            principal: [User], resource: [Doc],
            context: { input: { x: String } }
          };
          action "Write" in [Action::"ReadWrite"] appliesTo {
            principal: [User], resource: [Doc],
            context: { input: { x: String } }
          };
        }
    "#;

    #[test]
    fn provider_group_expansion_includes_descendants() {
        let fragment = parse(HIERARCHY_SCHEMA);
        // Scope is `action in [Action::"ReadWrite"]` — a group with 2 children.
        let action = ScopedAction::List(vec![("App".to_string(), "ReadWrite".to_string())]);
        let targets = scope_target_actions(&action, &fragment).unwrap();
        // Should include parent + both children.
        assert!(
            targets.contains(&("App".to_string(), "ReadWrite".to_string())),
            "parent missing from targets: {targets:?}"
        );
        assert!(
            targets.contains(&("App".to_string(), "Read".to_string())),
            "child Read missing from targets: {targets:?}"
        );
        assert!(
            targets.contains(&("App".to_string(), "Write".to_string())),
            "child Write missing from targets: {targets:?}"
        );
        assert_eq!(targets.len(), 3, "expected 3 targets, got {targets:?}");
    }

    // ─── Error paths ─────────────────────────────────────────────────

    #[test]
    fn conflicting_providers_attribute_type_errors() {
        // A schema where `providers` is already a Bool (not a record) —
        // the augmentation should refuse rather than clobber.
        let schema = r#"
            namespace App {
              entity User;
              entity Doc;
              action "Read" appliesTo {
                principal: [User], resource: [Doc],
                context: { input: { x: String }, providers: Bool }
              };
            }
        "#;
        let mut fragment = parse(schema);
        let field = ProviderField {
            action: ScopedAction::Concrete(("App".to_string(), "Read".to_string())),
            target_actions: vec![("App".to_string(), "Read".to_string())],
            field_name: "policy_0_p_0".to_string(),
            cedar_type: "Bool".to_string(),
            body_base: 0,
            invocation: Invocation {
                span: Span { start: 0, end: 0 },
                function: vec!["Risk".to_string(), "Score".to_string()],
                args: vec![],
            },
            methods: vec![],
        };
        let result = add_provider_context_fields(&mut fragment, &[field]);
        assert!(
            result.is_err(),
            "should reject non-record providers attribute"
        );
        assert!(
            result.unwrap_err().contains("not an inline record"),
            "error should mention the reason"
        );
    }

    // ─── Context-as-type-reference inlining ──────────────────────────
    //
    // Cedar treats common types as pure aliases: `CommonTypeResolver`
    // ("facilitates inlining the definitions of common types") substitutes
    // them away during ValidatorSchema construction. `inline_context_
    // references` must therefore (a) accept every reference spelling Cedar
    // accepts, and (b) resolve names to the SAME definition Cedar's
    // conditional qualification picks (current namespace, then empty
    // namespace; explicit qualification wins; common type beats entity
    // type). The differential tests below pin (b) against Cedar's own
    // validator rather than against our reading of its source.

    /// Extract one action's context record attribute names after running the
    /// provider pass with a single Bool field.
    fn augmented_context_attrs(schema: &str, namespace: &str, action: &str) -> Vec<String> {
        let mut fragment = parse(schema);
        add_provider_context_fields(&mut fragment, &[provider_field("p0")]).expect("augments");
        let ns_key = ns_key(namespace).unwrap();
        let ctx = &fragment.0[&ns_key].actions[&SmolStr::from(action)]
            .applies_to
            .as_ref()
            .unwrap()
            .context
            .0;
        match ctx {
            Type::Type {
                ty: TypeVariant::Record(r),
                ..
            } => r.attributes.keys().map(|k| k.to_string()).collect(),
            other => panic!("context not inlined to a record: {other:?}"),
        }
    }

    #[test]
    fn context_reference_on_untargeted_action_is_inlined() {
        // The provider rule targets Read; Audit's referenced context must be
        // inlined (not rejected) because provider fields graft everywhere.
        let schema = r#"
            namespace Drupe {
              type ReadInput = { document: String };
              type AuditCtx = { input: { reason: String } };
              entity Gateway;
              entity OAuthUser;
              action "Read" appliesTo {
                principal: [OAuthUser], resource: [Gateway],
                context: { input: ReadInput }
              };
              action "Audit" appliesTo {
                principal: [OAuthUser], resource: [Gateway],
                context: AuditCtx
              };
            }
        "#;
        let attrs = augmented_context_attrs(schema, "Drupe", "Audit");
        assert!(
            attrs.contains(&"input".to_string()),
            "inlined attrs: {attrs:?}"
        );
        assert!(
            attrs.contains(&"providers".to_string()),
            "grafted attrs: {attrs:?}"
        );
    }

    #[test]
    fn chained_context_references_resolve_to_terminal_record() {
        // `context: A`, `type A = B;`, `type B = { … };` — the chain must be
        // followed to the terminal record (Cedar has no depth limit; our
        // bound is #common-types + 1, which only fires on cycles).
        let schema = r#"
            namespace Drupe {
              type A = B;
              type B = C;
              type C = { leaf: Long };
              entity Gateway;
              entity OAuthUser;
              action "Read" appliesTo {
                principal: [OAuthUser], resource: [Gateway],
                context: A
              };
            }
        "#;
        let attrs = augmented_context_attrs(schema, "Drupe", "Read");
        assert!(attrs.contains(&"leaf".to_string()), "attrs: {attrs:?}");
        assert!(attrs.contains(&"providers".to_string()), "attrs: {attrs:?}");
    }

    #[test]
    fn cyclic_context_reference_errors() {
        // Cedar rejects cyclic common types at ValidatorSchema construction;
        // our resolver must error (not hang) when handed the parsed fragment.
        let schema = r#"
            namespace Drupe {
              type A = B;
              type B = A;
              entity Gateway;
              entity OAuthUser;
              action "Read" appliesTo {
                principal: [OAuthUser], resource: [Gateway],
                context: A
              };
            }
        "#;
        let mut fragment = parse(schema);
        let err = add_provider_context_fields(&mut fragment, &[provider_field("p0")])
            .expect_err("cycle must error");
        assert!(err.contains("cyclic"), "unexpected error: {err}");
    }

    #[test]
    fn appliesto_less_action_is_skipped_by_both_passes() {
        // A pure action group (no appliesTo) cannot receive requests: the
        // provider pass and the temporal Unconstrained arm both skip it.
        let schema = r#"
            namespace Drupe {
              entity Gateway;
              entity OAuthUser;
              action "Group";
              action "Read" in [Action::"Group"] appliesTo {
                principal: [OAuthUser], resource: [Gateway],
                context: { input: { document: String } }
              };
            }
        "#;
        let mut fragment = parse(schema);
        add_provider_context_fields(&mut fragment, &[provider_field("p0")])
            .expect("provider pass skips the group");
        let mut fragment = parse(schema);
        let field = ContextField {
            target_actions: Vec::new(),
            principal: crate::cedarify::ScopeConstraint::Any,
            resource: crate::cedarify::ScopeConstraint::Any,
            action: ScopedAction::Unconstrained,
            field_name: "t0".to_string(),
            temporal: crate::extension::temporal::Temporal::parse(
                r#"formerly within 1h Drupe::Action::"Read"::request{ input.document: context.input.document }"#,
                Span { start: 0, end: 0 },
            )
            .expect("temporal body parses"),
        };
        add_bool_context_fields(&mut fragment, &[field])
            .expect("temporal Unconstrained arm skips the group");
    }

    // ─── Differential agreement with Cedar's own resolution ──────────

    /// Validate `policy_src` against `schema_src` using Cedar's validator
    /// directly (no Dogwood augmentation). Returns whether it passes.
    fn cedar_validates(schema_src: &str, policy_src: &str) -> bool {
        let (schema, _) = cedar_policy::Schema::from_cedarschema_str(schema_src).unwrap();
        let policies: cedar_policy::PolicySet = policy_src.parse().unwrap();
        let validator = cedar_policy::Validator::new(schema);
        validator
            .validate(&policies, cedar_policy::ValidationMode::Strict)
            .validation_passed()
    }

    /// Same, but validating against OUR augmented schema (provider pass run
    /// over the fragment first, then compiled through Cedar).
    fn dogwood_inlined_validates(schema_src: &str, policy_src: &str) -> bool {
        let mut fragment = parse(schema_src);
        add_provider_context_fields(&mut fragment, &[provider_field("p0")]).expect("augments");
        let schema: cedar_policy::SchemaFragment = fragment.try_into().unwrap();
        let schema = cedar_policy::Schema::from_schema_fragments([schema]).unwrap();
        let policies: cedar_policy::PolicySet = policy_src.parse().unwrap();
        let validator = cedar_policy::Validator::new(schema);
        validator
            .validate(&policies, cedar_policy::ValidationMode::Strict)
            .validation_passed()
    }

    /// Same-name common type in the action's namespace AND the empty
    /// namespace, with DIFFERENT shapes — which definition wins is
    /// observable through attribute access.
    const SHADOWED_SCHEMA: &str = r#"
        type Ctx = { empty_ns_field: Long };
        namespace Drupe {
          type Ctx = { current_ns_field: Long };
          entity Gateway;
          entity OAuthUser;
          action "Read" appliesTo {
            principal: [OAuthUser], resource: [Gateway],
            context: Ctx
          };
        }
    "#;

    const READS_CURRENT_NS_FIELD: &str = r#"
        permit (principal, action == Drupe::Action::"Read", resource)
        when { context.current_ns_field > 0 };
    "#;
    const READS_EMPTY_NS_FIELD: &str = r#"
        permit (principal, action == Drupe::Action::"Read", resource)
        when { context.empty_ns_field > 0 };
    "#;

    #[test]
    fn shadowed_reference_is_rejected_by_cedar_so_no_precedence_question() {
        // Discovered BY this test: Cedar does not adjudicate between a
        // current-namespace and an empty-namespace definition of the same
        // name — it REJECTS the schema outright (`TypeShadowingError`,
        // disallowed shadowing of empty-namespace definitions). So the
        // ambiguous input our resolver's current-ns-first order would have
        // to get right never reaches augmentation on a legal schema.
        let err = cedar_policy::Schema::from_cedarschema_str(SHADOWED_SCHEMA)
            .map(|_| ())
            .expect_err("Cedar must reject the shadowing schema");
        assert!(
            format!("{err:?}").contains("Shadowing"),
            "expected a shadowing rejection, got: {err:?}"
        );

        // Our inlining pass must not MASK that rejection: it resolves the
        // context reference (picking the current-ns definition), but both
        // shadowing type declarations remain, so compiling the augmented
        // fragment still fails the same way.
        let mut fragment = parse(SHADOWED_SCHEMA);
        add_provider_context_fields(&mut fragment, &[provider_field("p0")])
            .expect("augmentation itself proceeds");
        let schema: cedar_policy::SchemaFragment = fragment.try_into().unwrap();
        let err = cedar_policy::Schema::from_schema_fragments([schema])
            .map(|_| ())
            .expect_err("augmented shadowing schema must still be rejected");
        assert!(
            format!("{err:?}").contains("Shadowing"),
            "expected a shadowing rejection post-augmentation, got: {err:?}"
        );
    }

    #[test]
    fn unqualified_reference_falls_back_to_empty_namespace_like_cedar() {
        // No definition in the current namespace: both Cedar and our
        // resolver fall back to the empty namespace.
        let schema = r#"
            type Ctx = { empty_ns_field: Long };
            namespace Drupe {
              entity Gateway;
              entity OAuthUser;
              action "Read" appliesTo {
                principal: [OAuthUser], resource: [Gateway],
                context: Ctx
              };
            }
        "#;
        assert!(cedar_validates(schema, READS_EMPTY_NS_FIELD));
        assert!(dogwood_inlined_validates(schema, READS_EMPTY_NS_FIELD));
        assert!(!cedar_validates(schema, READS_CURRENT_NS_FIELD));
        assert!(!dogwood_inlined_validates(schema, READS_CURRENT_NS_FIELD));
    }

    #[test]
    fn extension_type_in_cross_namespace_record_is_not_captured_like_cedar() {
        // Fourth manifestation of the cross-namespace root shape: a bare
        // extension-type name (`decimal`) inside a foreign namespace's
        // record must keep meaning the builtin after inlining, even when
        // the referencing action's namespace declares a same-named common
        // type (legal — shadowing a builtin name is only a warning).
        // Both polarities: the builtin-typed read must validate; a read
        // treating the field as the capturing record must not.
        let schema = r#"
            namespace Shared {
              type Ctx = { document: String, amount: decimal };
            }
            namespace App {
              type decimal = { foo: Long };
              entity User;
              entity Doc;
              action "Read" appliesTo {
                principal: [User], resource: [Doc],
                context: Shared::Ctx
              };
            }
        "#;
        let reads_builtin = r#"
            permit (principal, action == App::Action::"Read", resource)
            when { context.amount.lessThan(decimal("1.0")) };
        "#;
        let reads_captured = r#"
            permit (principal, action == App::Action::"Read", resource)
            when { context.amount.foo > 0 };
        "#;
        assert!(cedar_validates(schema, reads_builtin));
        assert!(!cedar_validates(schema, reads_captured));
        assert!(
            dogwood_inlined_validates(schema, reads_builtin),
            "`decimal` inside Shared's record must stay the builtin after inlining"
        );
        assert!(
            !dogwood_inlined_validates(schema, reads_captured),
            "`decimal` must NOT be captured by App's same-named common type"
        );
    }

    #[test]
    fn nested_user_types_are_deep_inlined_across_namespaces_like_cedar() {
        // Two levels of nested user-defined references inside the resolved
        // record, all written in the foreign namespace — must stay correct
        // after inlining into App.
        let schema = r#"
            namespace Shared {
              type Ctx = { input: Doc };
              type Doc = { meta: Meta };
              type Meta = { document: String };
            }
            namespace App {
              entity User;
              entity Doc2;
              action "Read" appliesTo {
                principal: [User], resource: [Doc2],
                context: Shared::Ctx
              };
            }
        "#;
        let reads_deep = r#"
            permit (principal, action == App::Action::"Read", resource)
            when { context.input.meta.document like "SAFE*" };
        "#;
        assert!(cedar_validates(schema, reads_deep));
        assert!(
            dogwood_inlined_validates(schema, reads_deep),
            "two-level nested foreign references must survive inlining"
        );
    }

    #[test]
    fn sibling_references_do_not_exhaust_the_cycle_budget() {
        // Four sibling attributes referencing the same common type: legal,
        // acyclic, accepted by Cedar. A substitution budget shared across
        // the whole tree (instead of per reference chain) falsely rejects
        // this as 'cyclic' once sibling substitutions outnumber the
        // definition count.
        let schema = r#"
            namespace App {
              type B = Long;
              type Ctx = { document: String, a: B, b: B, c: B, d: B };
              entity User;
              entity Doc;
              action "Read" appliesTo {
                principal: [User], resource: [Doc],
                context: Ctx
              };
            }
        "#;
        let attrs = augmented_context_attrs(schema, "App", "Read");
        for k in ["a", "b", "c", "d", "document", "providers"] {
            assert!(attrs.contains(&k.to_string()), "missing {k}: {attrs:?}");
        }
    }

    #[test]
    fn optional_attribute_in_referenced_record_stays_optional_like_cedar() {
        // `note?: NoteT` inside a referenced context: inlining must
        // preserve `required: false`. Dropping it makes the attribute
        // required, which (a) lets an unguarded `context.note.text` read
        // validate when Cedar rejects it — Cedar-UNSOUND — and (b) makes
        // the exported schema over-strict for request validation.
        let schema = r#"
            namespace App {
              type NoteT = { text: String };
              type Ctx = { document: String, note?: NoteT };
              entity User;
              entity Doc;
              action "Read" appliesTo {
                principal: [User], resource: [Doc],
                context: Ctx
              };
            }
        "#;
        let unguarded = r#"
            permit (principal, action == App::Action::"Read", resource)
            when { context.note.text like "SAFE*" };
        "#;
        let guarded = r#"
            permit (principal, action == App::Action::"Read", resource)
            when { context has note && context.note.text like "SAFE*" };
        "#;
        assert!(!cedar_validates(schema, unguarded));
        assert!(cedar_validates(schema, guarded));
        assert!(
            !dogwood_inlined_validates(schema, unguarded),
            "unguarded access to an optional attribute must stay REJECTED \
             after inlining (required flag must be preserved)"
        );
        assert!(
            dogwood_inlined_validates(schema, guarded),
            "has-guarded access must validate after inlining"
        );
    }

    #[test]
    fn qualified_reference_resolves_only_where_written_like_cedar() {
        // `context: Shared::Ctx` from another namespace: explicit
        // qualification wins over the current namespace's same-name type.
        let schema = r#"
            namespace Shared {
              type Ctx = { shared_field: Long };
            }
            namespace Drupe {
              type Ctx = { current_ns_field: Long };
              entity Gateway;
              entity OAuthUser;
              action "Read" appliesTo {
                principal: [OAuthUser], resource: [Gateway],
                context: Shared::Ctx
              };
            }
        "#;
        let reads_shared = r#"
            permit (principal, action == Drupe::Action::"Read", resource)
            when { context.shared_field > 0 };
        "#;
        assert!(cedar_validates(schema, reads_shared));
        assert!(dogwood_inlined_validates(schema, reads_shared));
        assert!(!cedar_validates(schema, READS_CURRENT_NS_FIELD));
        assert!(!dogwood_inlined_validates(schema, READS_CURRENT_NS_FIELD));
    }

    // ─── Cross-namespace resolution: each hop resolves where the ────
    // ─── definition is WRITTEN, not where the action lives ──────────

    #[test]
    fn chain_hop_in_foreign_namespace_resolves_at_definition_site_like_cedar() {
        // `Shared::Ctx = Inner` — the hop `Inner` is written inside Shared,
        // so it means Shared::Inner even though the referencing action
        // lives in App, and even though App declares its own `Inner` with a
        // different shape (legal: RFC 70 only forbids shadowing the EMPTY
        // namespace). Picking App::Inner silently inverts validation.
        let schema = r#"
            namespace Shared {
              type Ctx = Inner;
              type Inner = { shared_field: Long };
            }
            namespace App {
              type Inner = { app_field: Long };
              entity User;
              entity Doc;
              action "Read" appliesTo {
                principal: [User], resource: [Doc],
                context: Shared::Ctx
              };
            }
        "#;
        let reads_shared = r#"
            permit (principal, action == App::Action::"Read", resource)
            when { context.shared_field > 0 };
        "#;
        let reads_app = r#"
            permit (principal, action == App::Action::"Read", resource)
            when { context.app_field > 0 };
        "#;
        assert!(cedar_validates(schema, reads_shared));
        assert!(!cedar_validates(schema, reads_app));
        assert!(
            dogwood_inlined_validates(schema, reads_shared),
            "hop `Inner` must resolve at its definition site (Shared), like Cedar"
        );
        assert!(
            !dogwood_inlined_validates(schema, reads_app),
            "hop `Inner` must NOT resolve against the action's namespace (App)"
        );
    }

    #[test]
    fn chain_hop_defined_only_in_foreign_namespace_resolves_like_cedar() {
        // Same shape but `Inner` exists ONLY in Shared: an action-namespace
        // -rooted lookup finds nothing and falsely rejects a schema Cedar
        // accepts.
        let schema = r#"
            namespace Shared {
              type Ctx = Inner;
              type Inner = { shared_field: Long };
            }
            namespace App {
              entity User;
              entity Doc;
              action "Read" appliesTo {
                principal: [User], resource: [Doc],
                context: Shared::Ctx
              };
            }
        "#;
        let reads_shared = r#"
            permit (principal, action == App::Action::"Read", resource)
            when { context.shared_field > 0 };
        "#;
        assert!(cedar_validates(schema, reads_shared));
        assert!(
            dogwood_inlined_validates(schema, reads_shared),
            "a foreign-namespace hop must resolve; Cedar accepts this schema"
        );
    }

    #[test]
    fn nested_reference_in_record_cloned_across_namespaces_like_cedar() {
        // The resolved record itself contains a further unqualified
        // reference (`input: Doc`, with Doc written in Shared). Inlined
        // into an App action, that name must keep meaning Shared::Doc —
        // i.e. the clone must be namespace-safe (fully qualified), or Cedar
        // later mis-qualifies it against App.
        let schema = r#"
            namespace Shared {
              type Ctx = { input: Doc };
              type Doc = { document: String };
            }
            namespace App {
              entity User;
              entity Doc2;
              action "Read" appliesTo {
                principal: [User], resource: [Doc2],
                context: Shared::Ctx
              };
            }
        "#;
        let reads_doc = r#"
            permit (principal, action == App::Action::"Read", resource)
            when { context.input.document like "SAFE*" };
        "#;
        assert!(cedar_validates(schema, reads_doc));
        assert!(
            dogwood_inlined_validates(schema, reads_doc),
            "nested `Doc` inside the cloned record must keep meaning Shared::Doc"
        );
    }
}
