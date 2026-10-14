//! Augment a Cedar schema with hoisted boolean context fields.
//!
//! For each [`ContextField`] produced by `cedarify`, add a required
//! `Bool` attribute to the named action's `context` record. Both passes
//! mutate a `cedar-policy-core` [`Fragment`] **in place**: `cedarify` parses
//! the base `.cedarschema` once, threads the fragment through the bool pass
//! and the provider pass, and converts it to the final schema afterward — so
//! there is no serialize/re-parse round-trip between passes.

use cedar_policy_core::FromNormalizedStr;
use cedar_policy_core::ast::{Annotation, AnyId, Name};
use cedar_policy_core::est::Annotations;
use cedar_policy_core::validator::RawName;
pub(crate) use cedar_policy_core::validator::json_schema::Fragment;
use cedar_policy_core::validator::json_schema::{
    CommonType, CommonTypeId, RecordType, Type, TypeOfAttribute, TypeVariant,
};
use smol_str::SmolStr;

use super::{ContextField, ProviderField, ScopedAction};
use std::collections::{BTreeMap, BTreeSet};

const SHARED_PROVIDER_TYPE_BASENAME: &str = "DogwoodProviders";
const SHARED_PROVIDER_TYPE_ANNOTATION: &str = "dogwood_provider_context";
const SHARED_PROVIDER_TYPE_VERSION: &str = "1.1";

fn escaped_action_id(action_id: &str) -> String {
    cedar_policy_core::ast::Eid::new(action_id)
        .escaped()
        .to_string()
}

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
/// across repeated lowerings of a fed-forward augmented schema is safe. The
/// temporal pass uses this all-action form; the provider pass uses the
/// targeted wrapper below so unrelated actions retain their common-type
/// references.
fn inline_context_references(fragment: &mut Fragment<RawName>) -> Result<(), String> {
    inline_selected_context_references(fragment, None)
}

/// The provider pass already carries its exact concrete target actions, so it
/// can avoid expanding common context types used only by unrelated actions.
fn inline_context_references_for_actions(
    fragment: &mut Fragment<RawName>,
    targets: &BTreeSet<(String, String)>,
) -> Result<(), String> {
    inline_selected_context_references(fragment, Some(targets))
}

fn inline_selected_context_references(
    fragment: &mut Fragment<RawName>,
    targets: Option<&BTreeSet<(String, String)>>,
) -> Result<(), String> {
    let selected = |namespace: &Option<Name>, action_id: &str| {
        targets.is_none_or(|targets| {
            targets.contains(&(namespace_string(namespace), action_id.to_string()))
        })
    };

    // Fast path: nothing to do unless some action context is a reference.
    let any_reference = fragment.0.iter().any(|(namespace, ns)| {
        ns.actions.iter().any(|(action_id, a)| {
            selected(namespace, action_id)
                && a.applies_to
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
            if !selected(ns_key, action_id) {
                continue;
            }
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
                        "action `{}` context reference is cyclic and cannot be resolved",
                        escaped_action_id(action_id)
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
                .map_err(|m| format!("action `{}`: {m}", escaped_action_id(action_id)))?;
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
        .ok_or_else(|| {
            format!(
                "action `{}` not found in schema",
                escaped_action_id(action_id)
            )
        })?;
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
        .ok_or_else(|| format!("action `{}` has no appliesTo", escaped_action_id(action_id)))?;

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
            _ => Err(format!(
                "action `{}` context is not a record type",
                escaped_action_id(action_id)
            )),
        },
        _ => Err(format!(
            "action `{}` context does not resolve to a record type \
             (an action's context must be a record)",
            escaped_action_id(action_id)
        )),
    }
}

/// The annotation that tags an injected provider enum with its declared
/// name: `@dogwood_provider_enum("GuardDuty::Severity")`. A later lowering
/// finds an enum it injected by this tag (feed-forward) and reuses it.
const PROVIDER_ENUM_ANNOTATION: &str = "dogwood_provider_enum";

/// The namespace provider enums are exported into: the first namespace, in
/// sorted order, that declares actions (the root namespace, `None`, sorts
/// first). It depends only on the action schema, never on the policy set, so
/// every schema built from the same action schema puts an enum in the same
/// place. `None` (outer) if no namespace declares actions.
pub(crate) fn provider_enum_home(fragment: &Fragment<RawName>) -> Option<Option<Name>> {
    fragment
        .0
        .iter()
        .filter(|(_, ns)| !ns.actions.is_empty())
        .map(|(name, _)| name.clone())
        .min_by_key(|name| name.as_ref().map(ToString::to_string))
}

/// The exported name of each declared provider enum in `referenced`, keyed
/// by its declared name: `GuardDuty::Severity` -> `Drupe::GuardDuty_Severity`
/// (`GuardDuty_Severity` if the home namespace is the root). Names
/// `referenced` holds that the declarations do not declare (an app enum used
/// as an argument) are left out. Empty if no namespace declares actions.
pub(crate) fn provider_enum_names(
    fragment: &Fragment<RawName>,
    decls: &crate::extension::provider::declarations::ProviderDeclarations,
    referenced: &BTreeSet<String>,
) -> BTreeMap<String, String> {
    let Some(home) = provider_enum_home(fragment) else {
        return BTreeMap::new();
    };
    referenced
        .iter()
        .filter(|name| decls.entity_type_decls.contains_key(*name))
        .map(|declared| {
            let base = crate::extension::provider::declarations::exported_enum_basename(declared);
            let exported = match &home {
                Some(ns) => format!("{ns}::{base}"),
                None => base,
            };
            (declared.clone(), exported)
        })
        .collect()
}

/// The declared name an injected provider enum is tagged with, if `entity`
/// is one.
fn provider_enum_tag(
    entity: &cedar_policy_core::validator::json_schema::EntityType<RawName>,
) -> Option<&str> {
    entity
        .annotations
        .0
        .iter()
        .find(|(annotation, _)| annotation.to_string() == PROVIDER_ENUM_ANNOTATION)
        .and_then(|(_, value)| value.as_ref())
        .map(|value| value.val.as_str())
}

/// Inject the provider-declared enum entity types (`entityTypes` in
/// `providers.json`) named in `referenced` into the schema, so hoisted
/// provider fields can be typed by them and policies can name their literals.
/// `referenced` is what the policy set's provider calls use; a name it holds
/// that the declarations do not declare (an app-schema enum used as an
/// argument) is left alone.
///
/// Each enum goes into the **home namespace** ([`provider_enum_home`]) under
/// its exported name ([`provider_enum_names`]), tagged with its declared
/// name, so no namespace is ever added: a consumer that accepts only the
/// action schema's namespaces accepts the result. There is exactly one copy,
/// which the other namespaces refer to by its full name, so a policy literal
/// matches the field's value on every action.
///
/// The exported name is fixed by the declaration: policies name it, and it
/// must be the same in every schema that gets merged. So instead of getting
/// a suffix, a clash is an error, reported against the BASE schema:
///
/// * the declared name is also declared by the action schema (a literal
///   `GuardDuty::Severity::"HIGH"` would be ambiguous);
/// * the home namespace already declares the exported name (an entity or
///   common type), unless it is this enum, injected by an earlier lowering:
///   then it is reused and takes the current values;
/// * the exported name would shadow a root-namespace name, which Cedar
///   rejects.
///
/// The declarations are built as Cedar JSON schema so ids need no Cedar
/// string escaping here.
pub fn add_provider_entity_types(
    fragment: &mut Fragment<RawName>,
    decls: &crate::extension::provider::declarations::ProviderDeclarations,
    referenced: &BTreeSet<String>,
) -> Result<(), String> {
    let names = provider_enum_names(fragment, decls, referenced);
    if names.is_empty() {
        if decls
            .entity_type_decls
            .keys()
            .any(|name| referenced.contains(name))
        {
            return Err(
                "no namespace in the policy schema declares actions, so provider entity \
                 types have nowhere to go"
                    .to_string(),
            );
        }
        return Ok(());
    }
    let home = provider_enum_home(fragment).expect("names are only built with a home");
    let declares = |ns: &Option<Name>, base: &str| {
        fragment.0.get(ns).is_some_and(|ns| {
            ns.common_types
                .keys()
                .any(|id| id.as_ref().to_string() == base)
                || ns.entity_types.keys().any(|id| id.to_string() == base)
        })
    };

    let mut errors: Vec<String> = Vec::new();
    let mut entries = serde_json::Map::new();
    for (declared, exported) in &names {
        let decl = &decls.entity_type_decls[declared];
        // `ProviderDeclarations::check` guarantees a qualified, valid name.
        if let Some((ns, base)) = declared.rsplit_once("::") {
            if declares(&ns_key(ns)?, base) {
                errors.push(format!(
                    "entity type `{declared}` is also declared by the policy schema, so \
                     `{declared}::\"…\"` would be ambiguous; rename one of them"
                ));
                continue;
            }
        }
        let base = crate::extension::provider::declarations::exported_enum_basename(declared);
        let reused = fragment
            .0
            .get(&home)
            .and_then(|ns| {
                ns.entity_types
                    .iter()
                    .find(|(id, _)| id.to_string() == base)
            })
            .is_some_and(|(_, entity)| provider_enum_tag(entity) == Some(declared.as_str()));
        if !reused && declares(&home, &base) {
            errors.push(format!(
                "entity type `{declared}` is exported as `{exported}`, which the policy \
                 schema already declares; rename the policy schema's type"
            ));
            continue;
        }
        if home.is_some() && declares(&None, &base) {
            errors.push(format!(
                "entity type `{declared}` is exported as `{exported}`, which would shadow \
                 `{base}` declared in the policy schema's root namespace"
            ));
            continue;
        }
        let mut annotations = decl.annotations.clone();
        annotations.insert(PROVIDER_ENUM_ANNOTATION.to_string(), declared.clone());
        entries.insert(
            base,
            serde_json::json!({ "enum": decl.values, "annotations": annotations }),
        );
    }
    if !errors.is_empty() {
        return Err(errors.join("\n"));
    }

    // Build the entries as a one-namespace fragment, then move them into the
    // home namespace, replacing a reused enum.
    let home_json = home.as_ref().map(ToString::to_string).unwrap_or_default();
    let injected = Fragment::<RawName>::from_json_value(serde_json::json!({
        home_json: { "entityTypes": entries, "actions": {} }
    }))
    .map_err(|e| format!("provider entity types: {e}"))?;
    let home_ns = fragment
        .0
        .get_mut(&home)
        .expect("the home namespace is in the fragment");
    for (_, ns) in injected.0 {
        home_ns.entity_types.extend(ns.entity_types);
    }
    Ok(())
}

/// Define all hoisted information-provider outputs once in a shared common
/// type, then add a `providers` reference only to actions reached by at least
/// one provider-bearing policy.
///
/// Every provider-relevant action references the same all-provider record:
/// fields are not filtered per action. This preserves the runtime's
/// unconditional provider-output shape while avoiding the old
/// fields-times-actions schema expansion. Actions untouched by every provider
/// policy omit `providers` entirely.
///
/// The field types are recovered by synthesizing a tiny `.cedarschema`
/// common type, parsing it with Cedar's own parser (so arbitrary nested
/// record/set/decimal types are handled correctly). Each touched namespace
/// receives one annotated definition (normally `DogwoodProviders`, with a
/// numeric suffix if that name is occupied), because an unqualified type
/// nested inside a provider output must resolve relative to the action's
/// namespace exactly as it did when the record was inline.
///
/// **Additive across passes.** A later lowering merges new fields into every
/// previously emitted shared definition, so actions touched by an earlier
/// provider policy see the complete accumulated provider set. Newly touched
/// actions gain a reference; still-untouched actions remain unchanged.
pub fn add_provider_context_fields(
    fragment: &mut Fragment<RawName>,
    fields: &[ProviderField],
) -> Result<(), String> {
    if fields.is_empty() {
        return Ok(());
    }
    let targets: BTreeSet<(String, String)> = fields
        .iter()
        .flat_map(|field| field.target_actions.iter().cloned())
        .collect();
    if targets.is_empty() {
        return Ok(());
    }
    // A context declared as a common-type reference (`context: SomeType`)
    // must be inlined before hoisted fields can be inserted into it. Only
    // targeted actions need this expansion.
    inline_context_references_for_actions(fragment, &targets)?;

    // Synthesize `type __PR = { f1: T1, f2: T2 };` once and parse it to
    // recover each field's Cedar `Type<RawName>`. (This parses a tiny
    // *synthetic* schema, not the base one — it is how we recover
    // arbitrary nested record/set/decimal field types.)
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

    let target_namespaces: BTreeSet<String> = targets
        .iter()
        .map(|(namespace, _)| namespace.clone())
        .collect();

    // Start with fields carried by any shared definitions from earlier
    // lowerings. They must all converge to the same record after this pass.
    let mut all_attrs = BTreeMap::new();
    let mut shared_type_ids: BTreeMap<String, CommonTypeId> = BTreeMap::new();
    for (ns_key, ns) in &fragment.0 {
        let namespace = namespace_string(ns_key);
        let mut generated = ns
            .common_types
            .iter()
            .filter(|(_, common)| is_dogwood_provider_type(common));
        if let Some((id, common)) = generated.next() {
            if generated.next().is_some() {
                return Err(format!(
                    "namespace `{namespace}` contains multiple Dogwood-generated provider types"
                ));
            }
            let version = dogwood_provider_type_version(common).ok_or_else(|| {
                format!(
                    "namespace `{namespace}` contains a Dogwood provider type without a \
                     representation version"
                )
            })?;
            if version != SHARED_PROVIDER_TYPE_VERSION {
                return Err(format!(
                    "namespace `{namespace}` contains a Dogwood provider type with unsupported \
                     representation version `{version}`"
                ));
            }
            let attrs = common_type_record(common, &namespace)?;
            merge_provider_attributes(&mut all_attrs, attrs.attributes.clone())?;
            shared_type_ids.insert(namespace, id.clone());
        }
    }
    for namespace in &target_namespaces {
        if !shared_type_ids.contains_key(namespace) {
            let ns = fragment
                .0
                .get(&ns_key(namespace)?)
                .ok_or_else(|| format!("namespace `{namespace}` not found"))?;
            shared_type_ids.insert(namespace.clone(), available_shared_provider_type_id(ns)?);
        }
    }

    // A targeted action may carry an inline provider record from a schema
    // produced by the older augmentation strategy, or from a customer schema.
    // Preserve those fields when migrating that action to the shared type.
    for (namespace, action_id) in &targets {
        let ns_key = ns_key(namespace)?;
        let ns = fragment
            .0
            .get(&ns_key)
            .ok_or_else(|| format!("namespace `{namespace}` not found"))?;
        let action = ns
            .actions
            .get(action_id.as_str())
            .ok_or_else(|| format!("action `{}` not found", escaped_action_id(action_id)))?;
        let applies_to = action
            .applies_to
            .as_ref()
            .ok_or_else(|| format!("action `{}` has no appliesTo", escaped_action_id(action_id)))?;
        match provider_attribute(&applies_to.context.0, action_id)? {
            None => {}
            Some(TypeOfAttribute {
                ty:
                    Type::Type {
                        ty: TypeVariant::Record(existing),
                        ..
                    },
                ..
            }) => merge_provider_attributes(&mut all_attrs, existing.attributes.clone())?,
            Some(attribute) => {
                let shared_id = shared_type_ids
                    .get(namespace)
                    .expect("target namespace assigned a shared type");
                let shared_name = shared_id.as_ref().to_string();
                if !provider_type_reference_matches(&attribute.ty, namespace, &shared_name) {
                    return Err(format!(
                        "action `{}` already has a `providers` attribute that is neither an \
                         inline record nor Dogwood's shared provider type",
                        escaped_action_id(action_id)
                    ));
                }
                let common = ns.common_types.get(shared_id).ok_or_else(|| {
                    format!(
                        "action `{}` references missing Dogwood shared provider type",
                        escaped_action_id(action_id)
                    )
                })?;
                if !is_dogwood_provider_type(common) {
                    return Err(format!(
                        "action `{}` references `{shared_name}`, but that common type was not \
                         generated by Dogwood",
                        escaped_action_id(action_id),
                    ));
                }
            }
        }
    }
    merge_provider_attributes(&mut all_attrs, new_attrs)?;

    // Existing shared definitions must receive fields added by later passes,
    // even when none of that pass's policies target their namespace.
    for (namespace, shared_id) in &shared_type_ids {
        let ns_key = ns_key(&namespace)?;
        let ns = fragment
            .0
            .get_mut(&ns_key)
            .ok_or_else(|| format!("namespace `{namespace}` not found"))?;
        match ns.common_types.get_mut(shared_id) {
            Some(common) if is_dogwood_provider_type(common) => {
                common.ty = provider_record_type(all_attrs.clone());
            }
            Some(_) => unreachable!("available type name was checked before mutation"),
            None => {
                ns.common_types.insert(
                    shared_id.clone(),
                    CommonType {
                        ty: provider_record_type(all_attrs.clone()),
                        annotations: dogwood_provider_annotations()?,
                        loc: None,
                    },
                );
            }
        }
    }

    // Only actions reached by at least one provider policy gain the shared
    // reference. Every such action sees the complete all-provider record.
    for (namespace, action_id) in targets {
        let ns_key = ns_key(&namespace)?;
        let action = fragment
            .0
            .get_mut(&ns_key)
            .and_then(|ns| ns.actions.get_mut(&SmolStr::from(action_id.as_str())))
            .ok_or_else(|| format!("action `{}` not found", escaped_action_id(&action_id)))?;
        let applies_to = action.applies_to.as_mut().ok_or_else(|| {
            format!(
                "action `{}` has no appliesTo",
                escaped_action_id(&action_id)
            )
        })?;
        let shared_id = shared_type_ids
            .get(&namespace)
            .expect("target namespace assigned a shared type");
        let shared_name = shared_id.as_ref().to_string();
        insert_provider_reference(
            &mut applies_to.context.0,
            &namespace,
            &action_id,
            &shared_name,
        )?;
    }

    Ok(())
}

fn available_shared_provider_type_id(
    namespace: &cedar_policy_core::validator::json_schema::NamespaceDefinition<RawName>,
) -> Result<CommonTypeId, String> {
    for suffix in 0usize.. {
        let candidate = if suffix == 0 {
            SHARED_PROVIDER_TYPE_BASENAME.to_string()
        } else {
            format!("{SHARED_PROVIDER_TYPE_BASENAME}_{suffix}")
        };
        let id = candidate
            .parse()
            .map_err(|e| format!("invalid shared provider type name `{candidate}`: {e}"))?;
        let id = CommonTypeId::new(id)
            .map_err(|e| format!("invalid shared provider type name `{candidate}`: {e}"))?;
        if !namespace.common_types.contains_key(&id)
            && !namespace.entity_types.contains_key(id.as_ref())
        {
            return Ok(id);
        }
    }
    unreachable!("the unbounded suffix space cannot be exhausted")
}

fn dogwood_provider_annotations() -> Result<Annotations, String> {
    let annotation: AnyId = SHARED_PROVIDER_TYPE_ANNOTATION
        .parse()
        .map_err(|e| format!("invalid shared provider annotation name: {e}"))?;
    Ok(Annotations(BTreeMap::from([(
        annotation,
        Some(Annotation {
            val: SmolStr::from(SHARED_PROVIDER_TYPE_VERSION),
            loc: None,
        }),
    )])))
}

fn is_dogwood_provider_type(common: &CommonType<RawName>) -> bool {
    common
        .annotations
        .0
        .keys()
        .any(|annotation| annotation.to_string() == SHARED_PROVIDER_TYPE_ANNOTATION)
}

fn dogwood_provider_type_version(common: &CommonType<RawName>) -> Option<&str> {
    common
        .annotations
        .0
        .iter()
        .find(|(annotation, _)| annotation.to_string() == SHARED_PROVIDER_TYPE_ANNOTATION)
        .and_then(|(_, value)| value.as_ref())
        .map(AsRef::as_ref)
        .filter(|version: &&str| !version.is_empty())
}

fn common_type_record<'a>(
    common: &'a CommonType<RawName>,
    namespace: &str,
) -> Result<&'a RecordType<RawName>, String> {
    match &common.ty {
        Type::Type {
            ty: TypeVariant::Record(record),
            ..
        } => Ok(record),
        _ => Err(format!(
            "Dogwood shared provider type in namespace `{namespace}` is not a record"
        )),
    }
}

fn provider_record_type(attributes: BTreeMap<SmolStr, TypeOfAttribute<RawName>>) -> Type<RawName> {
    Type::Type {
        ty: TypeVariant::Record(RecordType {
            attributes,
            additional_attributes: false,
        }),
        loc: None,
    }
}

fn merge_provider_attributes(
    target: &mut BTreeMap<SmolStr, TypeOfAttribute<RawName>>,
    source: BTreeMap<SmolStr, TypeOfAttribute<RawName>>,
) -> Result<(), String> {
    for (name, attribute) in source {
        if let Some(existing) = target.get(&name)
            && existing != &attribute
        {
            return Err(format!(
                "provider field `{name}` was previously declared with a different type"
            ));
        }
        target.insert(name, attribute);
    }
    Ok(())
}

fn namespace_string(namespace: &Option<Name>) -> String {
    namespace
        .as_ref()
        .map(ToString::to_string)
        .unwrap_or_default()
}

fn provider_attribute<'a>(
    context: &'a Type<RawName>,
    action_id: &str,
) -> Result<Option<&'a TypeOfAttribute<RawName>>, String> {
    match context {
        Type::Type {
            ty: TypeVariant::Record(record),
            ..
        } => Ok(record.attributes.get("providers")),
        Type::Type { .. } => Err(format!(
            "action `{}` context is not a record",
            escaped_action_id(action_id)
        )),
        _ => Err(format!(
            "action `{}` context does not resolve to a record type \
             (an action's context must be a record)",
            escaped_action_id(action_id)
        )),
    }
}

fn provider_type_reference_matches(ty: &Type<RawName>, namespace: &str, type_name: &str) -> bool {
    let Some(reference) = context_reference_name(ty) else {
        return false;
    };
    reference == type_name
        || (!namespace.is_empty() && reference == format!("{namespace}::{type_name}"))
}

/// Insert a reference to the namespace's shared provider type into one action.
fn insert_provider_reference(
    context: &mut Type<RawName>,
    namespace: &str,
    action_id: &str,
    shared_type_name: &str,
) -> Result<(), String> {
    match context {
        Type::Type { ty, .. } => match ty {
            TypeVariant::Record(record) => {
                let shared_type = Type::CommonTypeRef {
                    type_name: RawName::parse_unqualified_name(shared_type_name)
                        .map_err(|e| format!("invalid shared provider type reference: {e}"))?,
                    loc: None,
                };
                match record.attributes.get_mut(&SmolStr::from("providers")) {
                    Some(attribute)
                        if matches!(
                            attribute.ty,
                            Type::Type {
                                ty: TypeVariant::Record(_),
                                ..
                            }
                        ) =>
                    {
                        attribute.ty = shared_type;
                        Ok(())
                    }
                    Some(attribute)
                        if provider_type_reference_matches(
                            &attribute.ty,
                            namespace,
                            shared_type_name,
                        ) =>
                    {
                        Ok(())
                    }
                    Some(_) => Err(format!(
                        "action `{}` already has a `providers` attribute that \
                         is neither an inline record nor Dogwood's shared provider type",
                        escaped_action_id(action_id)
                    )),
                    None => {
                        record.attributes.insert(
                            SmolStr::from("providers"),
                            TypeOfAttribute {
                                ty: shared_type,
                                required: true,
                                annotations: Default::default(),
                            },
                        );
                        Ok(())
                    }
                }
            }
            _ => Err(format!(
                "action `{}` context is not a record",
                escaped_action_id(action_id)
            )),
        },
        _ => Err(format!(
            "action `{}` context does not resolve to a record type \
             (an action's context must be a record)",
            escaped_action_id(action_id)
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
        provider_field_for(field_name, "Drupe", "Read")
    }

    fn provider_field_for(field_name: &str, namespace: &str, action_id: &str) -> ProviderField {
        ProviderField {
            action: ScopedAction::Concrete((namespace.to_string(), action_id.to_string())),
            target_actions: vec![(namespace.to_string(), action_id.to_string())],
            field_name: field_name.to_string(),
            cedar_type: "Bool".to_string(),
            body_base: 0,
            invocation: Invocation {
                span: Span { start: 0, end: 0 },
                function: vec!["Risk".to_string(), "Score".to_string()],
                args: vec![],
            },
            methods: vec![],
            principal: crate::cedarify::ScopeConstraint::Any,
            resource: crate::cedarify::ScopeConstraint::Any,
        }
    }

    fn provider_field_for_first_appliable(
        fragment: &Fragment<RawName>,
        field_name: &str,
    ) -> ProviderField {
        for (namespace, schema) in &fragment.0 {
            let namespace = namespace_string(namespace);
            for action_id in schema.actions.keys() {
                if action_is_appliable(fragment, &namespace, action_id) {
                    return provider_field_for(field_name, &namespace, action_id);
                }
            }
        }
        panic!("test schema has no requestable action");
    }

    fn shared_provider_attr_names(
        fragment: &Fragment<RawName>,
        namespace: &str,
    ) -> Option<Vec<String>> {
        let common = fragment.0[&ns_key(namespace).unwrap()]
            .common_types
            .values()
            .find(|common| is_dogwood_provider_type(common))?;
        Some(
            common_type_record(common, namespace)
                .unwrap()
                .attributes
                .keys()
                .map(ToString::to_string)
                .collect(),
        )
    }

    fn action_references_shared_provider_type(
        fragment: &Fragment<RawName>,
        namespace: &str,
        action_id: &str,
    ) -> bool {
        let context = &fragment.0[&ns_key(namespace).unwrap()].actions[action_id]
            .applies_to
            .as_ref()
            .unwrap()
            .context
            .0;
        let shared_name = fragment.0[&ns_key(namespace).unwrap()]
            .common_types
            .iter()
            .find(|(_, common)| is_dogwood_provider_type(common))
            .map(|(id, _)| id.as_ref().to_string());
        provider_attribute(context, action_id)
            .unwrap()
            .zip(shared_name.as_deref())
            .is_some_and(|(attribute, shared_name)| {
                provider_type_reference_matches(&attribute.ty, namespace, shared_name)
            })
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

    const DIAGNOSTIC_ACTION_IDS: &[&str] = &[
        "plain",
        "",
        r#"a\x22b"#,
        r#"a\x5cb"#,
        r#"a\nb"#,
        r#"\u{0_0_0_e}"#,
        r#"u\u{0_1_2_3}"#,
        r#"\\u{e}"#,
        "犬",
    ];

    fn cedar_action_id(action_source: &str) -> (String, String) {
        let uid: cedar_policy_core::ast::EntityUID = format!(r#"Drupe::Action::"{action_source}""#)
            .parse()
            .expect("Cedar action UID parses");
        (
            uid.eid().as_ref().to_string(),
            uid.eid().escaped().to_string(),
        )
    }

    fn action_schema(action_source: &str, context: &str) -> String {
        format!(
            r#"
            namespace Drupe {{
                entity User;
                entity Doc;
                action "{action_source}" appliesTo {{
                    principal: [User],
                    resource: [Doc],
                    context: {context}
                }};
            }}
            "#
        )
    }

    fn take_action(
        action_source: &str,
        context: &str,
    ) -> cedar_policy_core::validator::json_schema::ActionType<RawName> {
        let (decoded, _) = cedar_action_id(action_source);
        let mut fragment = parse(&action_schema(action_source, context));
        fragment
            .0
            .get_mut(&ns_key("Drupe").unwrap())
            .expect("Drupe namespace")
            .actions
            .remove(&SmolStr::from(decoded))
            .expect("action")
    }

    #[test]
    fn context_inlining_diagnostics_escape_action_ids_like_cedar() {
        for action_source in DIAGNOSTIC_ACTION_IDS {
            let (_, escaped) = cedar_action_id(action_source);
            let root_cycle = format!(
                r#"
                namespace Drupe {{
                    type A = B;
                    type B = A;
                    entity User;
                    entity Doc;
                    action "{action_source}" appliesTo {{
                        principal: [User], resource: [Doc], context: A
                    }};
                }}
                "#
            );
            let mut fragment = parse(&root_cycle);
            assert_eq!(
                inline_context_references(&mut fragment).expect_err("root cycle"),
                format!("action `{escaped}` context reference is cyclic and cannot be resolved"),
                "root cycle for {action_source:?}"
            );

            let nested_cycle = format!(
                r#"
                namespace Drupe {{
                    type A = {{ nested: B }};
                    type B = C;
                    type C = B;
                    entity User;
                    entity Doc;
                    action "{action_source}" appliesTo {{
                        principal: [User], resource: [Doc], context: A
                    }};
                }}
                "#
            );
            let mut fragment = parse(&nested_cycle);
            assert_eq!(
                inline_context_references(&mut fragment).expect_err("nested cycle"),
                format!(
                    "action `{escaped}`: context type reference chain is cyclic and cannot be \
                     resolved"
                ),
                "nested cycle for {action_source:?}"
            );
        }
    }

    #[test]
    fn temporal_augmentation_diagnostics_escape_action_ids_like_cedar() {
        for action_source in DIAGNOSTIC_ACTION_IDS {
            let (decoded, escaped) = cedar_action_id(action_source);

            let mut fragment = parse(BASE_SCHEMA);
            let field = bool_field(
                "policy_0__temporal_0",
                ScopedAction::Concrete(("Drupe".to_string(), decoded.clone())),
            );
            assert_eq!(
                add_bool_context_fields(&mut fragment, &[field]).expect_err("unknown action"),
                format!("action `{escaped}` not found in schema"),
                "unknown action {action_source:?}"
            );

            let mut action = take_action(action_source, "{ input: { value: String } }");
            action.applies_to = None;
            assert_eq!(
                add_bool_to_action(&mut action, "temporal", &decoded)
                    .expect_err("missing appliesTo"),
                format!("action `{escaped}` has no appliesTo"),
                "missing appliesTo {action_source:?}"
            );

            let mut action = take_action(action_source, "{ input: { value: String } }");
            action.applies_to.as_mut().unwrap().context.0 = Type::Type {
                ty: TypeVariant::String,
                loc: None,
            };
            assert_eq!(
                add_bool_to_action(&mut action, "temporal", &decoded).expect_err("scalar context"),
                format!("action `{escaped}` context is not a record type"),
                "scalar context {action_source:?}"
            );

            let mut action = take_action(action_source, "Ctx");
            assert_eq!(
                add_bool_to_action(&mut action, "temporal", &decoded)
                    .expect_err("unresolved context"),
                format!(
                    "action `{escaped}` context does not resolve to a record type \
                     (an action's context must be a record)"
                ),
                "unresolved context {action_source:?}"
            );
        }
    }

    #[test]
    fn provider_record_diagnostics_escape_action_ids_like_cedar() {
        for action_source in DIAGNOSTIC_ACTION_IDS {
            let (decoded, escaped) = cedar_action_id(action_source);

            let mut action = take_action(
                action_source,
                "{ input: { value: String }, providers: Bool }",
            );
            let context = &mut action.applies_to.as_mut().unwrap().context.0;
            assert_eq!(
                insert_provider_reference(
                    context,
                    "Drupe",
                    &decoded,
                    SHARED_PROVIDER_TYPE_BASENAME,
                )
                .expect_err("providers is not a record"),
                format!(
                    "action `{escaped}` already has a `providers` attribute that is neither an \
                     inline record nor Dogwood's shared provider type"
                ),
                "non-record providers {action_source:?}"
            );

            let mut action = take_action(action_source, "{ input: { value: String } }");
            action.applies_to.as_mut().unwrap().context.0 = Type::Type {
                ty: TypeVariant::String,
                loc: None,
            };
            let context = &mut action.applies_to.as_mut().unwrap().context.0;
            assert_eq!(
                insert_provider_reference(
                    context,
                    "Drupe",
                    &decoded,
                    SHARED_PROVIDER_TYPE_BASENAME,
                )
                .expect_err("scalar context"),
                format!("action `{escaped}` context is not a record"),
                "scalar provider context {action_source:?}"
            );

            let mut action = take_action(action_source, "Ctx");
            let context = &mut action.applies_to.as_mut().unwrap().context.0;
            assert_eq!(
                insert_provider_reference(
                    context,
                    "Drupe",
                    &decoded,
                    SHARED_PROVIDER_TYPE_BASENAME,
                )
                .expect_err("unresolved context"),
                format!(
                    "action `{escaped}` context does not resolve to a record type \
                     (an action's context must be a record)"
                ),
                "unresolved provider context {action_source:?}"
            );
        }
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
    fn provider_augmentation_feed_forward_updates_one_shared_type() {
        // Pass A touches Read. Pass B touches Write. After feed-forward both
        // actions reference the one accumulated all-provider type, while an
        // action untouched by either pass still has no providers attribute.
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
              action "Delete" appliesTo {
                principal: [User], resource: [Doc],
                context: { input: { doc: String } }
              };
            }
        "#;
        let mut fragment = parse(schema);
        add_provider_context_fields(
            &mut fragment,
            &[provider_field_for("ruleA_0_p_0", "App", "Read")],
        )
        .unwrap();
        let after_a = fragment.to_cedarschema().unwrap();

        let mut fragment_b = parse(&after_a);
        add_provider_context_fields(
            &mut fragment_b,
            &[provider_field_for("ruleB_0_p_0", "App", "Write")],
        )
        .unwrap();

        assert_eq!(
            shared_provider_attr_names(&fragment_b, "App"),
            Some(vec!["ruleA_0_p_0".to_string(), "ruleB_0_p_0".to_string()])
        );
        for action in ["Read", "Write"] {
            assert!(
                action_references_shared_provider_type(&fragment_b, "App", action),
                "{action} should reference the accumulated shared provider type"
            );
        }
        assert!(
            !action_references_shared_provider_type(&fragment_b, "App", "Delete"),
            "untouched Delete unexpectedly gained providers"
        );
    }

    #[test]
    fn feed_forward_updates_shared_provider_types_across_namespaces() {
        let schema = r#"
            namespace AppA {
              entity User;
              entity Doc;
              action "Read" appliesTo {
                principal: [User], resource: [Doc], context: {}
              };
            }
            namespace AppB {
              entity User;
              entity Doc;
              action "Write" appliesTo {
                principal: [User], resource: [Doc], context: {}
              };
            }
        "#;
        let mut fragment = parse(schema);
        add_provider_context_fields(
            &mut fragment,
            &[provider_field_for("field_a", "AppA", "Read")],
        )
        .unwrap();

        let mut fragment = parse(&fragment.to_cedarschema().unwrap());
        let mut field_b = provider_field_for("field_b", "AppB", "Write");
        field_b.cedar_type = "String".to_string();
        add_provider_context_fields(&mut fragment, &[field_b]).unwrap();

        let expected = Some(vec!["field_a".to_string(), "field_b".to_string()]);
        assert_eq!(
            shared_provider_attr_names(&fragment, "AppA"),
            expected,
            "the earlier namespace must receive fields introduced later elsewhere"
        );
        assert_eq!(
            shared_provider_attr_names(&fragment, "AppB"),
            expected,
            "a newly touched namespace receives the complete accumulated type"
        );
        assert!(action_references_shared_provider_type(
            &fragment, "AppA", "Read"
        ));
        assert!(action_references_shared_provider_type(
            &fragment, "AppB", "Write"
        ));

        let schema: cedar_policy::SchemaFragment = fragment.try_into().unwrap();
        cedar_policy::Schema::from_schema_fragments([schema])
            .expect("cross-namespace shared types compile");
    }

    #[test]
    fn targeted_inline_provider_record_migrates_to_shared_type() {
        let mut fragment = parse(
            r#"
            namespace App {
              entity User;
              entity Doc;
              action "Read" appliesTo {
                principal: [User], resource: [Doc],
                context: { providers: { legacy: String } }
              };
            }
            "#,
        );
        add_provider_context_fields(
            &mut fragment,
            &[provider_field_for("generated", "App", "Read")],
        )
        .unwrap();

        assert_eq!(
            shared_provider_attr_names(&fragment, "App"),
            Some(vec!["generated".to_string(), "legacy".to_string()])
        );
        assert!(action_references_shared_provider_type(
            &fragment, "App", "Read"
        ));
    }

    #[test]
    fn customer_common_type_name_collision_uses_a_suffix() {
        let mut fragment = parse(
            r#"
            namespace App {
              type DogwoodProviders = { customer: Bool };
              entity User;
              entity Doc;
              action "Read" appliesTo {
                principal: [User], resource: [Doc], context: {}
              };
            }
            "#,
        );
        add_provider_context_fields(
            &mut fragment,
            &[provider_field_for("generated", "App", "Read")],
        )
        .expect("Dogwood chooses a non-colliding generated name");

        let namespace = &fragment.0[&ns_key("App").unwrap()];
        let customer = namespace
            .common_types
            .iter()
            .find(|(id, _)| id.as_ref().to_string() == SHARED_PROVIDER_TYPE_BASENAME)
            .map(|(_, common)| common)
            .expect("customer type remains");
        assert!(
            !is_dogwood_provider_type(customer),
            "customer type was incorrectly claimed by Dogwood"
        );
        let generated_name = namespace
            .common_types
            .iter()
            .find(|(_, common)| is_dogwood_provider_type(common))
            .map(|(id, _)| id.as_ref().to_string())
            .expect("generated provider type");
        assert_eq!(generated_name, "DogwoodProviders_1");
        assert!(action_references_shared_provider_type(
            &fragment, "App", "Read"
        ));
    }

    #[test]
    fn suffixed_provider_type_is_reused_across_feed_forward() {
        let schema = r#"
            namespace App {
              type DogwoodProviders = { customer: Bool };
              entity User;
              entity Doc;
              action "Read" appliesTo {
                principal: [User], resource: [Doc], context: {}
              };
              action "Write" appliesTo {
                principal: [User], resource: [Doc], context: {}
              };
            }
        "#;
        let mut fragment = parse(schema);
        add_provider_context_fields(&mut fragment, &[provider_field_for("first", "App", "Read")])
            .unwrap();

        let mut fragment = parse(&fragment.to_cedarschema().unwrap());
        add_provider_context_fields(
            &mut fragment,
            &[provider_field_for("second", "App", "Write")],
        )
        .unwrap();

        let namespace = &fragment.0[&ns_key("App").unwrap()];
        let generated: Vec<_> = namespace
            .common_types
            .iter()
            .filter(|(_, common)| is_dogwood_provider_type(common))
            .collect();
        assert_eq!(generated.len(), 1);
        assert_eq!(generated[0].0.as_ref().to_string(), "DogwoodProviders_1");
        assert_eq!(
            shared_provider_attr_names(&fragment, "App"),
            Some(vec!["first".to_string(), "second".to_string()])
        );
        assert!(
            !fragment
                .to_cedarschema()
                .unwrap()
                .contains("DogwoodProviders_2")
        );
        for action in ["Read", "Write"] {
            assert!(action_references_shared_provider_type(
                &fragment, "App", action
            ));
        }

        let schema: cedar_policy::SchemaFragment = fragment.try_into().unwrap();
        cedar_policy::Schema::from_schema_fragments([schema])
            .expect("suffixed shared provider schema compiles");
    }

    #[test]
    fn explicitly_qualified_shared_provider_reference_survives_reaugmentation() {
        let schema = r#"
            namespace App {
              @dogwood_provider_context("1.1")
              type DogwoodProviders = { existing: Bool };
              entity User;
              entity Doc;
              action "Read" appliesTo {
                principal: [User], resource: [Doc],
                context: { providers: App::DogwoodProviders }
              };
            }
        "#;
        let mut fragment = parse(schema);
        add_provider_context_fields(
            &mut fragment,
            &[provider_field_for("new_field", "App", "Read")],
        )
        .expect("a qualified local reference is the existing shared provider type");

        assert_eq!(
            shared_provider_attr_names(&fragment, "App"),
            Some(vec!["existing".to_string(), "new_field".to_string()])
        );
        assert!(action_references_shared_provider_type(
            &fragment, "App", "Read"
        ));

        let schema: cedar_policy::SchemaFragment = fragment.try_into().unwrap();
        cedar_policy::Schema::from_schema_fragments([schema])
            .expect("qualified shared provider reference compiles");
    }

    #[test]
    fn legacy_inline_provider_records_migrate_across_separate_passes() {
        let schema = r#"
            namespace App {
              entity User;
              entity Doc;
              action "Read" appliesTo {
                principal: [User], resource: [Doc],
                context: { providers: { read_legacy: String } }
              };
              action "Write" appliesTo {
                principal: [User], resource: [Doc],
                context: { providers: { write_legacy: Long } }
              };
            }
        "#;
        let mut fragment = parse(schema);
        add_provider_context_fields(
            &mut fragment,
            &[provider_field_for("read_new", "App", "Read")],
        )
        .unwrap();
        assert!(action_references_shared_provider_type(
            &fragment, "App", "Read"
        ));
        assert!(
            matches!(
                provider_attribute(
                    &fragment.0[&ns_key("App").unwrap()].actions["Write"]
                        .applies_to
                        .as_ref()
                        .unwrap()
                        .context
                        .0,
                    "Write"
                )
                .unwrap()
                .map(|attribute| &attribute.ty),
                Some(Type::Type {
                    ty: TypeVariant::Record(_),
                    ..
                })
            ),
            "an untargeted legacy action should remain inline until it is migrated"
        );

        let mut fragment = parse(&fragment.to_cedarschema().unwrap());
        add_provider_context_fields(
            &mut fragment,
            &[provider_field_for("write_new", "App", "Write")],
        )
        .unwrap();

        assert_eq!(
            shared_provider_attr_names(&fragment, "App"),
            Some(vec![
                "read_legacy".to_string(),
                "read_new".to_string(),
                "write_legacy".to_string(),
                "write_new".to_string(),
            ])
        );
        for action in ["Read", "Write"] {
            assert!(action_references_shared_provider_type(
                &fragment, "App", action
            ));
        }
    }

    #[test]
    fn provider_field_with_no_requestable_targets_is_a_schema_noop() {
        let schema = r#"
            namespace App {
              type SharedContext = { input: { key: String } };
              entity User;
              entity Doc;
              action "Read" appliesTo {
                principal: [User], resource: [Doc], context: SharedContext
              };
            }
        "#;
        let mut fragment = parse(schema);
        let before = fragment.to_cedarschema().unwrap();
        let mut field = provider_field_for("unreachable", "App", "Read");
        field.target_actions.clear();
        add_provider_context_fields(&mut fragment, &[field]).unwrap();
        assert_eq!(fragment.to_cedarschema().unwrap(), before);
    }

    #[test]
    fn asymmetric_cross_namespace_name_collisions_keep_local_generated_names() {
        let schema = r#"
            namespace Colliding {
              type DogwoodProviders = { customer: Bool };
              entity User;
              entity Doc;
              action "Read" appliesTo {
                principal: [User], resource: [Doc], context: {}
              };
            }
            namespace Available {
              entity User;
              entity Doc;
              action "Write" appliesTo {
                principal: [User], resource: [Doc], context: {}
              };
            }
        "#;
        let fields = [
            provider_field_for("read_field", "Colliding", "Read"),
            provider_field_for("write_field", "Available", "Write"),
        ];
        let mut fragment = parse(schema);
        add_provider_context_fields(&mut fragment, &fields).unwrap();
        let mut fragment = parse(&fragment.to_cedarschema().unwrap());
        add_provider_context_fields(
            &mut fragment,
            &[provider_field_for("later_field", "Available", "Write")],
        )
        .unwrap();

        for namespace in ["Colliding", "Available"] {
            assert_eq!(
                shared_provider_attr_names(&fragment, namespace),
                Some(vec![
                    "later_field".to_string(),
                    "read_field".to_string(),
                    "write_field".to_string(),
                ])
            );
        }
        let generated_name = |namespace: &str| {
            fragment.0[&ns_key(namespace).unwrap()]
                .common_types
                .iter()
                .find(|(_, common)| is_dogwood_provider_type(common))
                .map(|(id, _)| id.as_ref().to_string())
                .unwrap()
        };
        assert_eq!(generated_name("Colliding"), "DogwoodProviders_1");
        assert_eq!(generated_name("Available"), "DogwoodProviders");
        assert!(action_references_shared_provider_type(
            &fragment,
            "Colliding",
            "Read"
        ));
        assert!(action_references_shared_provider_type(
            &fragment,
            "Available",
            "Write"
        ));

        let schema: cedar_policy::SchemaFragment = fragment.try_into().unwrap();
        cedar_policy::Schema::from_schema_fragments([schema])
            .expect("asymmetric local generated names compile");
    }

    #[test]
    fn unsupported_shared_provider_representation_version_is_rejected() {
        let mut fragment = parse(
            r#"
            namespace App {
              @dogwood_provider_context("2.0")
              type DogwoodProviders = { old: Bool };
              entity User;
              entity Doc;
              action "Read" appliesTo {
                principal: [User], resource: [Doc], context: {
                  providers: DogwoodProviders
                }
              };
            }
            "#,
        );
        let err = add_provider_context_fields(
            &mut fragment,
            &[provider_field_for("generated", "App", "Read")],
        )
        .expect_err("an unknown generated representation must not be silently rewritten");
        assert!(
            err.contains("unsupported representation version `2.0`"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn malformed_generated_provider_metadata_is_rejected() {
        let cases = [
            (
                "missing version",
                r#"
                namespace App {
                  @dogwood_provider_context
                  type DogwoodProviders = { old: Bool };
                  entity User;
                  entity Doc;
                  action "Read" appliesTo {
                    principal: [User], resource: [Doc], context: {}
                  };
                }
                "#,
                "without a representation version",
            ),
            (
                "non-record",
                r#"
                namespace App {
                  @dogwood_provider_context("1.1")
                  type DogwoodProviders = Bool;
                  entity User;
                  entity Doc;
                  action "Read" appliesTo {
                    principal: [User], resource: [Doc], context: {}
                  };
                }
                "#,
                "is not a record",
            ),
            (
                "multiple generated types",
                r#"
                namespace App {
                  @dogwood_provider_context("1.1")
                  type DogwoodProviders = { old: Bool };
                  @dogwood_provider_context("1.1")
                  type DogwoodProviders_1 = { other: String };
                  entity User;
                  entity Doc;
                  action "Read" appliesTo {
                    principal: [User], resource: [Doc], context: {}
                  };
                }
                "#,
                "multiple Dogwood-generated provider types",
            ),
        ];

        for (label, schema, expected) in cases {
            let mut fragment = parse(schema);
            let err = add_provider_context_fields(
                &mut fragment,
                &[provider_field_for("new_field", "App", "Read")],
            )
            .unwrap_err();
            assert!(
                err.contains(expected),
                "{label}: expected {expected:?}, got {err:?}"
            );
        }
    }

    #[test]
    fn provider_schema_is_invariant_to_policy_order() {
        let schema = r#"
            namespace App {
              entity User;
              entity Doc;
              action "Read" appliesTo {
                principal: [User], resource: [Doc], context: {}
              };
              action "Write" appliesTo {
                principal: [User], resource: [Doc], context: {}
              };
            }
        "#;
        let read = provider_field_for("read_field", "App", "Read");
        let mut write = provider_field_for("write_field", "App", "Write");
        write.cedar_type = "String".to_string();

        let mut read_then_write = parse(schema);
        add_provider_context_fields(&mut read_then_write, &[read.clone()]).unwrap();
        let mut read_then_write = parse(&read_then_write.to_cedarschema().unwrap());
        add_provider_context_fields(&mut read_then_write, &[write.clone()]).unwrap();

        let mut write_then_read = parse(schema);
        add_provider_context_fields(&mut write_then_read, &[write]).unwrap();
        let mut write_then_read = parse(&write_then_read.to_cedarschema().unwrap());
        add_provider_context_fields(&mut write_then_read, &[read]).unwrap();

        assert_eq!(
            read_then_write.to_cedarschema().unwrap(),
            write_then_read.to_cedarschema().unwrap(),
            "provider schema should not depend on policy arrival order"
        );
    }

    #[test]
    fn reapplying_the_same_provider_field_is_idempotent() {
        let field = provider_field("same_field");
        let mut once = parse(BASE_SCHEMA);
        add_provider_context_fields(&mut once, &[field.clone()]).unwrap();
        let once_text = once.to_cedarschema().unwrap();

        let mut twice = parse(&once_text);
        add_provider_context_fields(&mut twice, &[field]).unwrap();
        assert_eq!(twice.to_cedarschema().unwrap(), once_text);
        assert_eq!(
            shared_provider_attr_names(&twice, "Drupe"),
            Some(vec!["same_field".to_string()])
        );
    }

    #[test]
    fn feed_forward_rejects_a_provider_field_with_a_changed_type() {
        let mut fragment = parse(BASE_SCHEMA);
        add_provider_context_fields(&mut fragment, &[provider_field("same_field")]).unwrap();

        let mut fragment = parse(&fragment.to_cedarschema().unwrap());
        let mut changed = provider_field("same_field");
        changed.cedar_type = "String".to_string();
        let err = add_provider_context_fields(&mut fragment, &[changed])
            .expect_err("the same generated field cannot change type");
        assert_eq!(
            err,
            "provider field `same_field` was previously declared with a different type"
        );
    }

    #[test]
    fn missing_provider_marker_fails_without_creating_a_second_type() {
        let schema = r#"
            namespace App {
              type DogwoodProviders = { old_field: Bool };
              entity User;
              entity Doc;
              action "Read" appliesTo {
                principal: [User], resource: [Doc],
                context: { providers: DogwoodProviders }
              };
            }
        "#;
        let mut fragment = parse(schema);
        let before = fragment.to_cedarschema().unwrap();
        let err = add_provider_context_fields(
            &mut fragment,
            &[provider_field_for("new_field", "App", "Read")],
        )
        .expect_err("an unmarked type must not be treated as Dogwood-owned");
        assert!(
            err.contains("neither an inline record nor Dogwood's shared provider type"),
            "unexpected error: {err}"
        );
        assert_eq!(
            fragment.to_cedarschema().unwrap(),
            before,
            "failure must not leave a partially generated suffixed type"
        );
    }

    #[test]
    fn large_provider_schema_defines_each_field_once_and_only_references_it_per_action() {
        const ACTIONS: usize = 80;
        const FIELDS: usize = 200;
        let mut schema = String::from(
            r#"
            namespace Scale {
              entity User;
              entity Doc;
            "#,
        );
        for action in 0..ACTIONS {
            schema.push_str(&format!(
                r#"
                action "Action{action}" appliesTo {{
                  principal: [User], resource: [Doc], context: {{}}
                }};
                "#
            ));
        }
        schema.push_str(
            r#"
              action "Untouched" appliesTo {
                principal: [User], resource: [Doc], context: {}
              };
            }
            "#,
        );

        let fields: Vec<_> = (0..FIELDS)
            .map(|field| {
                provider_field_for(
                    &format!("provider_field_{field}"),
                    "Scale",
                    &format!("Action{}", field % ACTIONS),
                )
            })
            .collect();
        let mut fragment = parse(&schema);
        add_provider_context_fields(&mut fragment, &fields).unwrap();

        assert_eq!(
            shared_provider_attr_names(&fragment, "Scale")
                .expect("shared provider type")
                .len(),
            FIELDS
        );
        for action in 0..ACTIONS {
            assert!(action_references_shared_provider_type(
                &fragment,
                "Scale",
                &format!("Action{action}")
            ));
        }
        assert!(!action_references_shared_provider_type(
            &fragment,
            "Scale",
            "Untouched"
        ));

        let text = fragment.to_cedarschema().unwrap();
        assert!(!text.contains("DogwoodProviders_1"));
        for field in 0..FIELDS {
            let name = format!("provider_field_{field}");
            let declaration = format!("{name}: ");
            assert_eq!(
                text.matches(&declaration).count(),
                1,
                "{name} should be defined once, not copied into every action"
            );
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

    #[test]
    fn escaped_group_ids_expand_from_decoded_scope_identity() {
        let cases = [
            ("quote", r#"a\"b"#, r#"a\x22b"#),
            ("backslash", r#"a\\b"#, r#"a\x5cb"#),
            ("unicode control", r#"\u{e}"#, r#"\u{0_0_0_e}"#),
            ("underscored unicode", r#"u\u{0_1_2_3}"#, r#"u\u{123}"#),
            ("literal escape text", r#"\\u{e}"#, r#"\\u{e}"#),
        ];

        for (label, declaration, reference) in cases {
            let schema = format!(
                r#"
                namespace App {{
                  entity User;
                  entity Doc;
                  action "{declaration}";
                  action "Member" in [Action::"{declaration}"] appliesTo {{
                    principal: [User], resource: [Doc],
                    context: {{ input: {{ x: String }} }}
                  }};
                }}
                "#
            );
            let fragment = parse(&schema);
            let uid: cedar_policy_core::ast::EntityUID = format!(r#"App::Action::"{reference}""#)
                .parse()
                .unwrap_or_else(|error| panic!("{label}: {error}"));
            let action =
                ScopedAction::List(vec![("App".to_string(), uid.eid().as_ref().to_string())]);
            assert_eq!(
                scope_target_actions(&action, &fragment).unwrap(),
                vec![("App".to_string(), "Member".to_string())],
                "{label}"
            );
        }
    }

    #[test]
    fn escaped_group_ids_do_not_conflate_control_and_literal_escape_text() {
        let schema = r#"
            namespace App {
              entity User;
              entity Doc;
              action "\u{e}";
              action "\\u{e}";
              action "ControlMember" in [Action::"\u{0_0_0_e}"] appliesTo {
                principal: [User], resource: [Doc], context: {}
              };
              action "LiteralMember" in [Action::"\\u{e}"] appliesTo {
                principal: [User], resource: [Doc], context: {}
              };
            }
        "#;
        let fragment = parse(schema);
        let control = ScopedAction::List(vec![("App".to_string(), "\u{e}".to_string())]);
        let literal = ScopedAction::List(vec![("App".to_string(), r"\u{e}".to_string())]);

        assert_eq!(
            scope_target_actions(&control, &fragment).unwrap(),
            vec![("App".to_string(), "ControlMember".to_string())]
        );
        assert_eq!(
            scope_target_actions(&literal, &fragment).unwrap(),
            vec![("App".to_string(), "LiteralMember".to_string())]
        );
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
            principal: crate::cedarify::ScopeConstraint::Any,
            resource: crate::cedarify::ScopeConstraint::Any,
        };
        let result = add_provider_context_fields(&mut fragment, &[field]);
        assert!(
            result.is_err(),
            "should reject non-record providers attribute"
        );
        assert!(
            result.unwrap_err().contains("neither an inline record"),
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
        add_provider_context_fields(
            &mut fragment,
            &[provider_field_for("p0", namespace, action)],
        )
        .expect("augments");
        context_attr_names(&fragment, namespace, action)
    }

    fn context_attr_names(
        fragment: &Fragment<RawName>,
        namespace: &str,
        action: &str,
    ) -> Vec<String> {
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
    fn context_reference_on_untargeted_action_stays_shared_and_gets_no_providers() {
        // The provider rule targets Read. Audit should retain its common-type
        // reference and remain provider-free because no provider policy
        // reaches it.
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
        let mut fragment = parse(schema);
        add_provider_context_fields(&mut fragment, &[provider_field_for("p0", "Drupe", "Read")])
            .expect("augments Read");
        let audit_context = &fragment.0[&ns_key("Drupe").unwrap()].actions["Audit"]
            .applies_to
            .as_ref()
            .unwrap()
            .context
            .0;
        assert_eq!(
            context_reference_name(audit_context).as_deref(),
            Some("AuditCtx"),
            "untargeted context was unnecessarily expanded: {audit_context:?}"
        );
        assert!(
            provider_attribute(audit_context, "Audit").is_err(),
            "an untouched common-type context should not have an inline providers attribute"
        );
    }

    #[test]
    fn multiple_targets_inline_only_their_shared_context_references() {
        let schema = r#"
            namespace App {
              type SharedContext = { input: { key: String } };
              entity User;
              entity Doc;
              action "Read" appliesTo {
                principal: [User], resource: [Doc], context: SharedContext
              };
              action "Write" appliesTo {
                principal: [User], resource: [Doc], context: SharedContext
              };
              action "Delete" appliesTo {
                principal: [User], resource: [Doc], context: SharedContext
              };
            }
        "#;
        let mut fragment = parse(schema);
        add_provider_context_fields(
            &mut fragment,
            &[
                provider_field_for("read_provider", "App", "Read"),
                provider_field_for("write_provider", "App", "Write"),
            ],
        )
        .expect("targeted shared contexts augment");

        for action in ["Read", "Write"] {
            assert!(
                action_references_shared_provider_type(&fragment, "App", action),
                "{action} should be inlined and reference the provider type"
            );
            assert!(
                context_reference_name(
                    &fragment.0[&ns_key("App").unwrap()].actions[action]
                        .applies_to
                        .as_ref()
                        .unwrap()
                        .context
                        .0
                )
                .is_none(),
                "{action}'s targeted context should be inlined"
            );
        }

        let delete_context = &fragment.0[&ns_key("App").unwrap()].actions["Delete"]
            .applies_to
            .as_ref()
            .unwrap()
            .context
            .0;
        assert_eq!(
            context_reference_name(delete_context).as_deref(),
            Some("SharedContext"),
            "the untouched action must retain its exact original common-type reference"
        );
        let shared_context = fragment.0[&ns_key("App").unwrap()]
            .common_types
            .iter()
            .find(|(name, _)| name.as_ref().to_string() == "SharedContext")
            .map(|(_, common)| common)
            .expect("SharedContext remains");
        assert!(
            !common_type_record(shared_context, "App")
                .unwrap()
                .attributes
                .contains_key("providers"),
            "targeted inlining must not mutate the customer common type"
        );

        let schema: cedar_policy::SchemaFragment = fragment.try_into().unwrap();
        cedar_policy::Schema::from_schema_fragments([schema])
            .expect("partially inlined shared contexts compile");
    }

    #[test]
    fn root_namespace_provider_type_survives_feed_forward() {
        let schema = r#"
            entity User;
            entity Doc;
            action "Read" appliesTo {
              principal: [User], resource: [Doc], context: {}
            };
            action "Write" appliesTo {
              principal: [User], resource: [Doc], context: {}
            };
        "#;
        let mut fragment = parse(schema);
        add_provider_context_fields(&mut fragment, &[provider_field_for("first", "", "Read")])
            .expect("root namespace provider generation");

        let mut fragment = parse(&fragment.to_cedarschema().unwrap());
        add_provider_context_fields(&mut fragment, &[provider_field_for("second", "", "Write")])
            .expect("root namespace provider feed-forward");

        assert_eq!(
            shared_provider_attr_names(&fragment, ""),
            Some(vec!["first".to_string(), "second".to_string()])
        );
        for action in ["Read", "Write"] {
            assert!(action_references_shared_provider_type(
                &fragment, "", action
            ));
        }

        let schema: cedar_policy::SchemaFragment = fragment.try_into().unwrap();
        cedar_policy::Schema::from_schema_fragments([schema])
            .expect("root namespace shared provider schema compiles");
    }

    #[test]
    fn one_target_does_not_expand_many_shared_contexts() {
        const UNTOUCHED_ACTIONS: usize = 64;
        let mut schema = String::from(
            r#"
            namespace Scale {
              type LargeContext = {
                input: {
                  a: String,
                  b: Long,
                  c: Bool,
                  nested: { x: String, y: Set<Long> }
                }
              };
              entity User;
              entity Doc;
              action "Target" appliesTo {
                principal: [User], resource: [Doc], context: LargeContext
              };
            "#,
        );
        for action in 0..UNTOUCHED_ACTIONS {
            schema.push_str(&format!(
                r#"
                action "Untouched{action}" appliesTo {{
                  principal: [User], resource: [Doc], context: LargeContext
                }};
                "#
            ));
        }
        schema.push('}');

        let mut fragment = parse(&schema);
        add_provider_context_fields(
            &mut fragment,
            &[provider_field_for("only_target", "Scale", "Target")],
        )
        .unwrap();

        assert!(action_references_shared_provider_type(
            &fragment, "Scale", "Target"
        ));
        for action in 0..UNTOUCHED_ACTIONS {
            let action_id = format!("Untouched{action}");
            let context = &fragment.0[&ns_key("Scale").unwrap()].actions[action_id.as_str()]
                .applies_to
                .as_ref()
                .unwrap()
                .context
                .0;
            assert!(
                context_reference_name(context).is_some(),
                "{action_id} duplicated the shared context: {context:?}"
            );
        }
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
        let field = provider_field_for_first_appliable(&fragment, "p0");
        add_provider_context_fields(&mut fragment, &[field]).expect("augments");
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

    // ── Provider enums in the home namespace ────────────────────────────

    fn enum_decls(
        values: &[&str],
    ) -> crate::extension::provider::declarations::ProviderDeclarations {
        crate::extension::provider::declarations::ProviderDeclarations::from_json(
            &serde_json::json!({
                "entityTypes": { "MyGuardrails::Score": { "enum": values } },
                "availableProviders": { "MyGuardrails::Filter": {
                    "outputType": { "paramType": "entity", "entityType": "MyGuardrails::Score" } } }
            })
            .to_string(),
        )
        .expect("declarations load")
    }

    fn score_referenced() -> BTreeSet<String> {
        BTreeSet::from(["MyGuardrails::Score".to_string()])
    }

    fn home_of(schema: &str) -> Option<String> {
        provider_enum_home(&parse(schema)).map(|ns| ns.map(|n| n.to_string()).unwrap_or_default())
    }

    #[test]
    fn home_is_the_first_namespace_that_declares_actions() {
        let action = r#"action "Go" appliesTo { principal: [U], resource: [U], context: {} };"#;
        assert_eq!(home_of(BASE_SCHEMA).as_deref(), Some("Drupe"));
        assert_eq!(
            home_of(&format!(
                "namespace B {{ entity U; {action} }} namespace A {{ entity U; {action} }}"
            ))
            .as_deref(),
            Some("A")
        );
        // A namespace that only declares types doesn't count.
        assert_eq!(
            home_of(&format!(
                "namespace Aaa {{ type T = Long; }} namespace Zed {{ entity U; {action} }}"
            ))
            .as_deref(),
            Some("Zed")
        );
        // The root namespace sorts first.
        assert_eq!(
            home_of(&format!("entity U; {action} namespace A {{ entity V; }}")).as_deref(),
            Some("")
        );
        assert_eq!(home_of("namespace A { entity U; }"), None);
    }

    #[test]
    fn enum_is_injected_into_the_home_namespace_with_its_declared_name() {
        let mut fragment = parse(BASE_SCHEMA);
        add_provider_entity_types(
            &mut fragment,
            &enum_decls(&["LOW", "HIGH"]),
            &score_referenced(),
        )
        .unwrap();
        let text = fragment.to_cedarschema().unwrap();
        assert!(
            text.contains(
                "@dogwood_provider_enum(\"MyGuardrails::Score\")\n  entity MyGuardrails_Score enum [\"LOW\", \"HIGH\"];"
            ),
            "{text}"
        );
        assert!(!text.contains("namespace MyGuardrails"), "{text}");
    }

    #[test]
    fn injected_enum_is_reused_on_feed_forward_and_takes_current_values() {
        let mut fragment = parse(BASE_SCHEMA);
        add_provider_entity_types(
            &mut fragment,
            &enum_decls(&["LOW", "HIGH"]),
            &score_referenced(),
        )
        .unwrap();
        // A later lowering against the augmented schema finds its own enum by
        // the tag: no clash, no second copy, and the current values win.
        let mut fragment = parse(&fragment.to_cedarschema().unwrap());
        add_provider_entity_types(
            &mut fragment,
            &enum_decls(&["LOW", "HIGH", "CRITICAL"]),
            &score_referenced(),
        )
        .expect("an enum injected by an earlier lowering is reused");
        let text = fragment.to_cedarschema().unwrap();
        assert_eq!(
            text.matches("entity MyGuardrails_Score").count(),
            1,
            "{text}"
        );
        assert!(
            text.contains(r#"enum ["LOW", "HIGH", "CRITICAL"]"#),
            "{text}"
        );
    }

    #[test]
    fn an_untagged_type_with_the_exported_name_is_a_clash() {
        let schema = BASE_SCHEMA.replace(
            "entity Gateway;",
            "entity Gateway; entity MyGuardrails_Score;",
        );
        let err = add_provider_entity_types(
            &mut parse(&schema),
            &enum_decls(&["LOW"]),
            &score_referenced(),
        )
        .unwrap_err();
        assert!(
            err.contains("which the policy schema already declares"),
            "{err}"
        );
    }

    #[test]
    fn other_namespaces_refer_to_the_one_home_enum() {
        let schema = r#"
            namespace App {
              entity U;
              action "Read" appliesTo { principal: [U], resource: [U], context: {} };
            }
            namespace Audit {
              entity U;
              action "Inspect" appliesTo { principal: [U], resource: [U], context: {} };
            }
        "#;
        let mut fragment = parse(schema);
        add_provider_entity_types(&mut fragment, &enum_decls(&["LOW"]), &score_referenced())
            .unwrap();
        let mut field = provider_field_for("p0", "App", "Read");
        field
            .target_actions
            .push(("Audit".to_string(), "Inspect".to_string()));
        field.cedar_type = "{ result: App::MyGuardrails_Score }".to_string();
        add_provider_context_fields(&mut fragment, &[field]).unwrap();
        let text = fragment.to_cedarschema().unwrap();
        assert_eq!(text.matches(" enum [").count(), 1, "{text}");
        let fragment: cedar_policy::SchemaFragment = fragment.try_into().unwrap();
        cedar_policy::Schema::from_schema_fragments([fragment])
            .expect("both namespaces' provider types resolve the one enum");
    }
}
