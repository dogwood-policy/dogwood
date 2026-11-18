//! The schemas a lowered bundle is validated and decided against, as values of the
//! specification's types: the action schema (`Cedar.Validation.Schema`), the typed event
//! signatures (`Dogwood.Spec.EventSignature`), and the provider declarations
//! (`Dogwood.Spec.Provider.Declarations`).
//!
//! The action schema is read off the crate's augmented Cedar schema, without the context
//! attributes lowering hoisted (each temporal field `context.<id>`, and the `providers` record),
//! so it is the bundle's action schema with the enum entity types its provider declarations
//! inject. It is written as the Rust validator stores it, with *descendant* information; the
//! harness inverts it to cedar-lean's *ancestor* form as cedar-lean's own protobuf decoder does
//! (`CedarProto/Schema.lean`).
//!
//! A cedar type is written as `"bool"`, `"long"`, `"string"`, `{"set": T}`,
//! `{"entity": {"id", "path"}}`, `{"record": [[attr, {"ty": T, "required": b}], …]}`, or
//! `{"ext": name}`.

use std::collections::HashSet;

use cedar_policy_core::validator::types::{AttributeType, Attributes, BoolType, EntityKind, OpenTag, Type};
use cedar_policy_core::validator::{ValidatorEntityTypeKind, ValidatorSchema};
use dogwood_language::{EventFieldType, EventPinRoot, EventSignature, LoweredPolicySet, ProviderDeclarations};
use serde_json::{Value as Json, json};

use crate::{ctor, uid};

type Result<T> = std::result::Result<T, String>;

/// An entity type name, as a `Cedar.Spec.Name`.
pub fn ety(t: &cedar_policy_core::ast::EntityType) -> Json {
    let segs: Vec<String> = t.to_string().split("::").map(str::to_string).collect();
    let (id, path) = segs.split_last().expect("an entity type has a basename");
    json!({"id": id, "path": path})
}

fn entity_uid(u: &cedar_policy_core::ast::EntityUID) -> Json {
    json!({"ty": ety(u.entity_type()), "eid": u.eid().as_ref()})
}

/// A validator type, as a `Cedar.Validation.CedarType`.
pub fn ty(t: &Type) -> Result<Json> {
    Ok(match t {
        Type::Bool(BoolType::AnyBool) => json!("bool"),
        Type::Bool(b) => return Err(format!("singleton boolean type {b:?} in a schema")),
        Type::Long => json!("long"),
        Type::String => json!("string"),
        Type::Set { element_type: Some(e) } => json!({"set": ty(e)?}),
        Type::Set { element_type: None } => return Err("a set type without an element type".into()),
        Type::Entity(EntityKind::Entity(lub)) => match lub.get_single_entity() {
            Some(e) => json!({"entity": ety(e)}),
            None => return Err("a non-singleton entity type in a schema".into()),
        },
        Type::Entity(EntityKind::AnyEntity) => return Err("the any-entity type in a schema".into()),
        Type::Record { attrs, open_attributes } => {
            if *open_attributes != OpenTag::ClosedAttributes {
                return Err("an open record type in a schema".into());
            }
            json!({"record": record(attrs, &HashSet::new())?})
        }
        Type::ExtensionType { name } => json!({"ext": name.to_string()}),
        Type::Never => return Err("the never type in a schema".into()),
    })
}

fn attribute(a: &AttributeType) -> Result<Json> {
    Ok(json!({"ty": ty(&a.attr_type)?, "required": a.is_required()}))
}

/// A record type's attributes, without those in `drop`.
fn record(attrs: &Attributes, drop: &HashSet<String>) -> Result<Vec<Json>> {
    let mut out = Vec::new();
    for (k, a) in attrs.iter() {
        if drop.contains(k.as_str()) {
            continue;
        }
        out.push(json!([k.as_str(), attribute(a)?]));
    }
    Ok(out)
}

/// The context attributes lowering hoisted: each temporal field, and the provider record.
fn hoisted(lowered: &LoweredPolicySet) -> HashSet<String> {
    let mut h: HashSet<String> = lowered
        .nonrelativized_temporal_fields()
        .map(|f| f.id.as_str().to_string())
        .collect();
    if lowered.provider_fields().next().is_some() {
        h.insert("providers".to_string());
    }
    h
}

/// The action schema of a lowered bundle, in the validator's descendant form.
pub fn action_schema(lowered: &LoweredPolicySet) -> Result<Json> {
    validator_schema(lowered.cedar_schema().as_ref(), &hoisted(lowered))
}

/// A compiled Cedar schema, in the validator's descendant form, without the context attributes
/// in `drop`.
pub fn validator_schema(schema: &ValidatorSchema, drop: &HashSet<String>) -> Result<Json> {
    let mut ets = Vec::new();
    for e in schema.entity_types() {
        let descendants: Vec<Json> = e.descendants.iter().map(ety).collect();
        let (enum_choices, tags) = match &e.kind {
            ValidatorEntityTypeKind::Enum(choices) => {
                (Some(choices.iter().map(|c| c.as_ref().to_string()).collect::<Vec<_>>()), Json::Null)
            }
            ValidatorEntityTypeKind::Standard(_) => {
                (None, match e.tag_type() { Some(t) => ty(t)?, None => Json::Null })
            }
            // An `external` entity type (Cedar 4.14, RFC 116): Cedar's request and entity
            // validation view it as a standard entity type without attributes or tags.
            ValidatorEntityTypeKind::External => (None, Json::Null),
        };
        ets.push(json!({
            "name": ety(e.name()), "descendants": descendants,
            "attrs": record(e.attributes(), &HashSet::new())?, "tags": tags, "enum": enum_choices,
        }));
    }
    let mut acts = Vec::new();
    for a in schema.action_ids() {
        let context = match a.context_type() {
            Some(Type::Record { attrs, .. }) => record(attrs, drop)?,
            // An `external` action has no context type; it applies to no principal and no
            // resource, so no request for it conforms.
            None => Vec::new(),
            Some(other) => return Err(format!("the context of {} is {other:?}", a.name())),
        };
        acts.push(json!({
            "name": entity_uid(a.name()),
            "principals": a.applies_to_principals().map(ety).collect::<Vec<_>>(),
            "resources": a.applies_to_resources().map(ety).collect::<Vec<_>>(),
            "descendants": a.descendants().map(entity_uid).collect::<Vec<_>>(),
            "context": context,
        }));
    }
    let external_types: Vec<Json> =
        schema.entity_types().filter(|e| e.is_external()).map(|e| ety(e.name())).collect();
    let external_actions: Vec<Json> =
        schema.action_ids().filter(|a| a.is_external()).map(|a| entity_uid(a.name())).collect();
    Ok(json!({"ets": ets, "acts": acts, "externalTypes": external_types,
              "externalActions": external_actions}))
}

/// The type at `path` in a record type, and whether every attribute along the path is required.
fn path_type<'a>(mut attrs: &'a Attributes, path: &[String]) -> Option<(&'a Type, bool)> {
    let mut required = true;
    let (last, init) = path.split_last()?;
    for seg in init {
        let a = attrs.get_attr(seg)?;
        required &= a.is_required();
        match a.attr_type.as_ref() {
            Type::Record { attrs: inner, .. } => attrs = inner,
            _ => return None,
        }
    }
    let a = attrs.get_attr(last)?;
    Some((a.attr_type.as_ref(), required && a.is_required()))
}

/// A field type the event schema declares in text (`String`, `Long`, `Set < String >`, …), as a
/// cedar type. The event schema's own field types are primitive, sets, extension types, or entity
/// type names the action schema declares.
fn text_type(text: &str, schema: &ValidatorSchema) -> Result<Json> {
    let t = text.trim();
    Ok(match t {
        "String" => json!("string"),
        "Long" => json!("long"),
        "Bool" | "Boolean" => json!("bool"),
        "decimal" | "ipaddr" | "datetime" | "duration" => json!({"ext": t}),
        _ => {
            if let Some(inner) = t.strip_prefix("Set").map(str::trim).and_then(|r| r.strip_prefix('<')) {
                let inner = inner.strip_suffix('>').ok_or_else(|| format!("field type `{t}`"))?;
                return Ok(json!({"set": text_type(inner, schema)?}));
            }
            match schema.entity_types().find(|e| e.name().to_string() == t) {
                Some(e) => json!({"entity": ety(e.name())}),
                None => return Err(format!("field type `{t}`")),
            }
        }
    })
}

/// An entity type the event schema names, resolved against the action schema: as written, or in
/// the namespace of the event's action (`namespace` is the action's type path, ending in
/// `Action`).
fn resolve_entity_type(name: &str, namespace: &[String], schema: &ValidatorSchema) -> Result<Json> {
    let ns = &namespace[..namespace.len().saturating_sub(1)];
    let qualified = if ns.is_empty() { name.to_string() } else { format!("{}::{name}", ns.join("::")) };
    schema
        .entity_types()
        .find(|e| e.name().to_string() == qualified)
        .or_else(|| schema.entity_types().find(|e| e.name().to_string() == name))
        .map(|e| ety(e.name()))
        .ok_or_else(|| format!("entity type `{name}` of an event field"))
}

/// A typed event signature, as a `Dogwood.Spec.EventSignature`. A field of the spliced `input` or
/// `output` group has the type the action's context declares at its path, and is required when
/// every attribute along the path is; any other field is optional (a pinned field must still be
/// logged, `EventSignature.Admits`).
pub fn signature(s: &EventSignature, lowered: &LoweredPolicySet) -> Result<Json> {
    let schema: &ValidatorSchema = lowered.cedar_schema().as_ref();
    let action = uid(s.namespace(), s.action())?;
    let pins: Vec<Json> = s
        .pins()
        .map(|p| {
            let reference = match p.root() {
                EventPinRoot::Scope => {
                    let (root, rest) = p.target_path().split_first().expect("scope pin root");
                    ctor("scope", json!({"root": root, "path": rest}))
                }
                EventPinRoot::Context => ctor("context", json!({"path": p.target_path()})),
            };
            json!({"field": p.field_path(), "ref": reference})
        })
        .collect();
    let context = schema
        .action_ids()
        .find(|a| {
            let name = a.name();
            name.eid().as_ref() == s.action()
                && name.entity_type().to_string() == s.namespace().join("::")
        })
        .and_then(|a| a.context_type());
    let context_attrs = match context {
        Some(Type::Record { attrs, .. }) => Some(attrs),
        _ => None,
    };
    let mut fields = Vec::new();
    for f in s.fields() {
        let path = f.path();
        let spliced = matches!(path.first().map(String::as_str), Some("input" | "output"));
        let (fty, required) = match (spliced, context_attrs.and_then(|a| path_type(a, path))) {
            (true, Some((t, required))) => (ctor("cedar", json!({"ty": ty(t)?})), required),
            _ => match f.field_type() {
                EventFieldType::EntityTypes(names) => {
                    let etys = names
                        .iter()
                        .map(|n| resolve_entity_type(n, s.namespace(), schema))
                        .collect::<Result<Vec<_>>>()?;
                    (ctor("entities", json!({"etys": etys})), false)
                }
                EventFieldType::Cedar(text) => (ctor("cedar", json!({"ty": text_type(text, schema)?})), false),
            },
        };
        fields.push(json!({"path": path, "ty": fty, "required": required}));
    }
    Ok(json!({"action": action, "kind": s.kind(), "decision": s.is_decision(), "pins": pins, "fields": fields}))
}

/// A provider parameter type, as a cedar type, as the crate renders it into the augmented schema
/// (`ParamType::to_cedar_type_with`): an enum entity type a provider declares is the one the
/// crate exports, `<namespace>::<declared with :: as _>`; any other entity type keeps its name;
/// an unknown `paramType`, a set without items, and an entity without a type are `String` (the
/// crate's deprecated fallback).
fn param_type(p: &dogwood_language::ParamType, schema: &ValidatorSchema) -> Result<Json> {
    Ok(match p.param_type.as_str() {
        "string" => json!("string"),
        "integer" | "long" => json!("long"),
        "bool" | "boolean" => json!("bool"),
        "decimal" => json!({"ext": "decimal"}),
        "set" => match &p.items {
            Some(items) => json!({"set": param_type(items, schema)?}),
            None => json!({"set": "string"}),
        },
        "record" => {
            let mut attrs = Vec::new();
            for (k, v) in &p.fields {
                attrs.push(json!([k, {"ty": param_type(v, schema)?, "required": p.required.contains(k)}]));
            }
            json!({"record": attrs})
        }
        "entity" => match p.entity_type.as_deref() {
            Some(declared) => {
                let basename = declared.replace("::", "_");
                let exported = schema
                    .entity_types()
                    .find(|e| e.name().to_string().rsplit("::").next() == Some(basename.as_str()));
                let own = schema.entity_types().find(|e| e.name().to_string() == declared);
                match exported.or(own) {
                    Some(e) => json!({"entity": ety(e.name())}),
                    None => return Err(format!("the entity type `{declared}`")),
                }
            }
            None => json!("string"),
        },
        _ => json!("string"),
    })
}

/// The provider declarations, as a `Dogwood.Spec.Provider.Declarations`, and the names of the
/// declarations left out because their argument or output type names an entity type the
/// augmented schema does not declare (the crate injects only the enums an invocation
/// references). A method whose type names such an entity type is left out of its declaration:
/// no invocation calls it, or the crate would have injected the enum.
pub fn provider_decls(
    decls: Option<&ProviderDeclarations>,
    lowered: &LoweredPolicySet,
) -> Result<(Json, Vec<String>)> {
    let schema: &ValidatorSchema = lowered.cedar_schema().as_ref();
    let Some(decls) = decls else {
        return Ok((json!([]), vec![]));
    };
    let mut out = Vec::new();
    let mut skipped = Vec::new();
    for (name, d) in &decls.available {
        match provider_decl(name, d, schema) {
            Ok(j) => out.push(j),
            Err(_) => skipped.push(name.clone()),
        }
    }
    Ok((Json::Array(out), skipped))
}

fn provider_decl(name: &str, d: &dogwood_language::ProviderDecl, schema: &ValidatorSchema) -> Result<Json> {
    let segs: Vec<String> = name.split("::").map(str::to_string).collect();
    let (id, path) = segs.split_last().ok_or("an empty provider name")?;
    let args = d.argument_types.iter().map(|a| param_type(a, schema)).collect::<Result<Vec<_>>>()?;
    let mut methods = Vec::new();
    for (m, md) in &d.methods {
        let method = || -> Result<Json> {
            let input = match &md.input_type {
                Some(t) => param_type(t, schema)?,
                None => Json::Null,
            };
            Ok(json!({
                "name": m,
                "args": md.argument_types.iter().map(|a| param_type(a, schema)).collect::<Result<Vec<_>>>()?,
                "input": input,
                "output": param_type(&md.output_type, schema)?,
            }))
        };
        if let Ok(j) = method() {
            methods.push(j);
        }
    }
    Ok(json!({
        "function": {"id": id, "path": path}, "args": args,
        "output": param_type(&d.output_type, schema)?, "methods": methods,
    }))
}
