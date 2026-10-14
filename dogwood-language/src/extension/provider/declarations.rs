//! Information-provider declarations — the `providers.json` schema that,
//! for each provider, gives its argument signature, its output type, and
//! **how it is implemented**.
//!
//! This is the configurability the guardrail dialect lacked: a guardrail
//! declared only its interface (`argumentTypes` + `outputType`) and left
//! "how the value is produced" as tribal knowledge in a downstream
//! component that hardcoded the fixed set of classifiers. A provider
//! declaration additionally carries an [`Implementation`] — today a
//! sandboxed Rhai script — so a deployment can define a brand-new
//! provider purely by editing this file, with no Rust change.
//!
//! `cedarify` uses the declared `output_type` to type the hoisted
//! `context.providers.<name>` field; `validate` uses `argument_types` to
//! check invocations; the authorize-time evaluator (`super::eval`) uses
//! `implementation` to actually compute the value.
//!
//! The implementation may carry its Rhai script inline (`script`) or, for
//! readability, reference an external `.rhai` file (`scriptFile`) resolved
//! relative to the declarations file — load such a file via
//! [`ProviderDeclarations::from_json_file`], which reads each referenced
//! script and folds it into the inline `script`.
//!
//! ```json
//! {
//!   "availableProviders": {
//!     "Strings::Matches": {
//!       "argumentTypes": [ { "paramType": "string" }, { "paramType": "string" } ],
//!       "outputType": {
//!         "paramType": "record",
//!         "fields": { "matched": { "paramType": "bool" } },
//!         "required": ["matched"]
//!       },
//!       "implementation": { "kind": "rhai", "scriptFile": "matches.rhai" }
//!     }
//!   }
//! }
//! ```
//!
//! A provider value may also be an **enum entity**: the file declares the
//! enum under `entityTypes` (Cedar's own JSON shape for an enum entity type)
//! and a type references it with `"paramType": "entity"` +
//! `"entityType"`.
//!
//! ```json
//! {
//!   "entityTypes": { "MyGuardrails::Score": { "enum": ["LOW", "MEDIUM", "HIGH"] } },
//!   "availableProviders": {
//!     "MyGuardrails::ContentFilter": {
//!       "argumentTypes": [ { "paramType": "string" } ],
//!       "outputType": {
//!         "paramType": "record",
//!         "fields": { "result": { "paramType": "entity", "entityType": "MyGuardrails::Score" } },
//!         "required": ["result"]
//!       }
//!     }
//!   }
//! }
//! ```

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use cedar_policy_core::FromNormalizedStr;
use serde::Deserialize;

/// The parsed declarations file.
///
/// `Default` is derived so a caller building declarations with a struct
/// literal can write `..Default::default()` and stay source-compatible when
/// fields are added.
#[derive(Debug, Clone, Default, PartialEq, Eq, Deserialize)]
pub struct ProviderDeclarations {
    #[serde(rename = "availableProviders", default)]
    pub available: BTreeMap<String, ProviderDecl>,
    /// The enum entity types this file declares, keyed by fully-qualified
    /// name (`Ns::Type`). Dogwood injects them into the augmented schema; a
    /// type references one via `"paramType": "entity"` + `"entityType"`.
    #[serde(
        rename = "entityTypes",
        default,
        deserialize_with = "deserialize_entity_type_decls"
    )]
    pub entity_type_decls: BTreeMap<String, EntityTypeDecl>,
}

/// One declared enum entity type. Mirrors Cedar's JSON-schema declaration of
/// an enum entity type exactly — `enum` plus optional `annotations`, nothing
/// else — so a declaration can be copied into a Cedar schema unchanged.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EntityTypeDecl {
    /// The permitted entity ids, in declaration order.
    #[serde(rename = "enum")]
    pub values: Vec<String>,
    /// Cedar annotations (e.g. `doc`), carried into the injected declaration.
    #[serde(default)]
    pub annotations: BTreeMap<String, String>,
}

/// Deserialize `entityTypes`, rejecting a duplicated key. A plain map
/// silently keeps the last of duplicated JSON keys, which would hide one of
/// two conflicting enum declarations.
fn deserialize_entity_type_decls<'de, D>(
    deserializer: D,
) -> Result<BTreeMap<String, EntityTypeDecl>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    struct Visitor;
    impl<'de> serde::de::Visitor<'de> for Visitor {
        type Value = BTreeMap<String, EntityTypeDecl>;
        fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            f.write_str("a map of entity type declarations")
        }
        fn visit_map<A: serde::de::MapAccess<'de>>(
            self,
            mut map: A,
        ) -> Result<Self::Value, A::Error> {
            let mut out = BTreeMap::new();
            while let Some((name, decl)) = map.next_entry::<String, EntityTypeDecl>()? {
                if out.contains_key(&name) {
                    return Err(serde::de::Error::custom(format!(
                        "entity type `{name}` is declared more than once"
                    )));
                }
                out.insert(name, decl);
            }
            Ok(out)
        }
    }
    deserializer.deserialize_map(Visitor)
}

impl ProviderDeclarations {
    /// Parse from JSON text and [`check`](Self::check) it. Any
    /// `implementation` that uses `scriptFile` (an external `.rhai`
    /// reference) is left unresolved — use
    /// [`from_json_file`](Self::from_json_file) to also read those files.
    pub fn from_json(json: &str) -> Result<Self, String> {
        let json = json.strip_prefix('\u{FEFF}').unwrap_or(json);
        let decls: Self = serde_json::from_str(json).map_err(|e| format!("providers.json: {e}"))?;
        decls.check().map_err(|e| format!("providers.json: {e}"))?;
        Ok(decls)
    }

    /// Check the declarations' internal consistency, independent of any
    /// action schema: every `paramType` is known, `entity` types name a
    /// valid, fully-qualified `entityType`, every output entity type is
    /// declared in `entityTypes`, and every `entityTypes` entry is a
    /// well-formed enum in one of this file's provider namespaces.
    ///
    /// [`from_json`](Self::from_json) runs this; so does
    /// [`ServiceSchemaBuilder::build`](crate::ServiceSchemaBuilder::build),
    /// which covers declarations built directly in code. All problems are
    /// reported, one per line.
    pub fn check(&self) -> Result<(), String> {
        let mut errors: Vec<String> = Vec::new();
        let provider_namespaces: BTreeSet<&str> = self
            .available
            .keys()
            .filter_map(|k| k.rsplit_once("::").map(|(ns, _)| ns))
            .collect();

        for (name, decl) in &self.entity_type_decls {
            match check_entity_type_name(name) {
                Err(e) => errors.push(format!("entityTypes: {e}")),
                Ok(ns) if !provider_namespaces.contains(ns) => errors.push(format!(
                    "entityTypes: entity type `{name}` is not in a provider namespace declared \
                     by this file"
                )),
                Ok(_) => {}
            }
            if decl.values.is_empty() {
                errors.push(format!("entityTypes: enum `{name}` has no values"));
            }
            let mut seen = BTreeSet::new();
            for value in &decl.values {
                if !seen.insert(value) {
                    errors.push(format!(
                        "entityTypes: enum `{name}` lists `{value}` more than once"
                    ));
                }
            }
        }

        // Each enum is exported under a name derived from its declared name
        // (see `exported_enum_basename`). `_` is also legal inside a name, so
        // two declarations can map to the same exported name; that would
        // merge two different enums into one Cedar type.
        let mut by_export: BTreeMap<String, Vec<&str>> = BTreeMap::new();
        for name in self.entity_type_decls.keys() {
            by_export
                .entry(exported_enum_basename(name))
                .or_default()
                .push(name);
        }
        for (exported, names) in by_export.iter().filter(|(_, n)| n.len() > 1) {
            errors.push(format!(
                "entityTypes: `{}` are all exported as `{exported}`; rename all but one",
                names.join("`, `")
            ));
        }

        let declared = |name: &str| self.entity_type_decls.contains_key(name);
        for (key, decl) in &self.available {
            let at = format!("provider `{key}`");
            for (i, arg) in decl.argument_types.iter().enumerate() {
                arg.check(&format!("{at} argumentTypes[{i}]"), None, &mut errors);
            }
            decl.output_type
                .check(&format!("{at} outputType"), Some(&declared), &mut errors);
            for (method, mdecl) in &decl.methods {
                let at = format!("{at} method `{method}`");
                for (i, arg) in mdecl.argument_types.iter().enumerate() {
                    arg.check(&format!("{at} argumentTypes[{i}]"), None, &mut errors);
                }
                if let Some(input) = &mdecl.input_type {
                    input.check(&format!("{at} inputType"), None, &mut errors);
                }
                mdecl
                    .output_type
                    .check(&format!("{at} outputType"), Some(&declared), &mut errors);
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors.join("\n"))
        }
    }

    /// Non-fatal problems: every unknown `paramType` that [`check`](Self::check)
    /// accepts and types `String` (the deprecated fallback), one message per
    /// occurrence with its JSON path. Empty for a file that uses only known
    /// kinds.
    ///
    /// The fallback becomes an error in the next major version; until then
    /// this is the only signal that, say, `"decimel"` is not a decimal.
    pub fn warnings(&self) -> Vec<String> {
        let mut out = Vec::new();
        for (key, decl) in &self.available {
            decl.collect_fallback_warnings(key, decl.methods.keys().map(String::as_str), &mut out);
        }
        out
    }

    /// Load a declarations file from disk, resolving any `scriptFile`
    /// reference relative to the declarations file's directory and
    /// folding the file's contents into the inline `script`.
    pub fn from_json_file(path: impl AsRef<Path>) -> Result<Self, String> {
        let path = path.as_ref();
        let json = std::fs::read_to_string(path)
            .map_err(|e| format!("read providers file `{}`: {e}", path.display()))?;
        let mut decls = Self::from_json(&json)?;
        let base = path.parent().unwrap_or_else(|| Path::new("."));
        for (key, decl) in decls.available.iter_mut() {
            if let Some(Implementation::Rhai {
                script,
                script_file,
            }) = decl.implementation.as_mut()
                && script.is_none()
                && let Some(file) = script_file.take()
            {
                let script_path = base.join(&file);
                let body = std::fs::read_to_string(&script_path).map_err(|e| {
                    format!(
                        "provider `{key}`: read scriptFile `{}`: {e}",
                        script_path.display()
                    )
                })?;
                *script = Some(body);
            }
        }
        Ok(decls)
    }

    pub fn get(&self, key: &str) -> Option<&ProviderDecl> {
        self.available.get(key)
    }

    /// The set of declared provider names (the declaration keys, e.g.
    /// `Strings::Matches`). Used to recognize the *unwrapped* provider form
    /// — a bare `Ns::Fn(args)` call to a declared provider inside ordinary
    /// Cedar — so macro expansion leaves it for cedarify to hoist.
    pub fn names(&self) -> std::collections::BTreeSet<String> {
        self.available.keys().cloned().collect()
    }
}

/// One declared provider: its argument types, output type, the methods
/// callable on its output, and its implementation.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct ProviderDecl {
    #[serde(rename = "argumentTypes", default)]
    pub argument_types: Vec<ParamType>,
    #[serde(rename = "outputType")]
    pub output_type: ParamType,
    /// Methods callable on the provider's output, keyed by method name. A
    /// method `m` is a **post-processor**: on `Ns::Fn(args).m(margs)` the
    /// value bound into context is `m(evaluate(args), margs…)`, and chains
    /// compose (`.m1().m2()` = `m2(m1(output))`). Each method declares its
    /// own `argumentTypes` and `outputType` (which re-types the pipeline),
    /// mirroring the base invocation. A zero-`argumentTypes` method is the
    /// MFOTL-style accessor case (e.g. `maxSeverityScore()`); a method with
    /// arguments is the generalization. At authorize time each method resolves
    /// to a `fn <name>(input, args…)` in the provider's Rhai script.
    ///
    /// Optional and defaults to empty — a provider with no declared methods
    /// supports only field/index projection into its output (as before).
    #[serde(rename = "availableMethods", default)]
    pub methods: BTreeMap<String, MethodDecl>,
    /// How the provider's value is produced. Optional so a declarations
    /// file can describe the interface alone (e.g. for validation-only
    /// pipelines, or when the value is supplied externally); the
    /// authorize-time evaluator errors if it must evaluate a provider
    /// that has no implementation.
    #[serde(default)]
    pub implementation: Option<Implementation>,
}

impl ProviderDecl {
    /// The entity types a call to this provider references: its argument and
    /// output types, plus those of the chained `methods` (by name). The
    /// schema injection and the authorize-time conversion both use this, so
    /// they agree on which enums a call needs.
    pub(crate) fn referenced_entity_types<'a>(
        &self,
        methods: impl IntoIterator<Item = &'a str>,
    ) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        self.argument_types
            .iter()
            .chain(std::iter::once(&self.output_type))
            .for_each(|t| t.collect_entity_types(&mut out));
        for m in methods.into_iter().filter_map(|m| self.methods.get(m)) {
            m.argument_types
                .iter()
                .chain(m.input_type.iter())
                .chain(std::iter::once(&m.output_type))
                .for_each(|t| t.collect_entity_types(&mut out));
        }
        out
    }

    /// Push a [`ProviderDeclarations::warnings`] message for every unknown
    /// `paramType` in this provider's argument and output types and in those
    /// of the given `methods`, with paths rooted at `provider `{key}``.
    pub(crate) fn collect_fallback_warnings<'a>(
        &self,
        key: &str,
        methods: impl IntoIterator<Item = &'a str>,
        out: &mut Vec<String>,
    ) {
        let at = format!("provider `{key}`");
        for (i, arg) in self.argument_types.iter().enumerate() {
            arg.collect_fallback_warnings(&format!("{at} argumentTypes[{i}]"), out);
        }
        self.output_type
            .collect_fallback_warnings(&format!("{at} outputType"), out);
        for method in methods {
            let Some(m) = self.methods.get(method) else {
                continue;
            };
            let at = format!("{at} method `{method}`");
            for (i, arg) in m.argument_types.iter().enumerate() {
                arg.collect_fallback_warnings(&format!("{at} argumentTypes[{i}]"), out);
            }
            if let Some(input) = &m.input_type {
                input.collect_fallback_warnings(&format!("{at} inputType"), out);
            }
            m.output_type
                .collect_fallback_warnings(&format!("{at} outputType"), out);
        }
    }
}

/// One declared method callable on a provider's output. Mirrors the base
/// invocation's shape: an argument signature and an output type (which
/// becomes the pipeline's type after this method runs). The optional
/// `inputType` declares the type this method expects to *receive* (the
/// previous pipeline stage's output); when present it enables static
/// pipeline-compatibility checking, when absent the receiver is untyped
/// (MFOTL-style: the script is trusted to handle whatever it gets).
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct MethodDecl {
    #[serde(rename = "argumentTypes", default)]
    pub argument_types: Vec<ParamType>,
    #[serde(rename = "outputType")]
    pub output_type: ParamType,
    #[serde(rename = "inputType", default)]
    pub input_type: Option<ParamType>,
}

/// How a provider is evaluated. A tagged enum so new evaluation kinds
/// (e.g. an HTTP service binding) can be added without disturbing
/// existing declarations.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Implementation {
    /// A sandboxed Rhai script. The script must define a function
    /// `fn evaluate(arg0, arg1, …) { … }` whose parameters correspond
    /// positionally to the declared `argumentTypes` and which returns a
    /// value matching `outputType` (typically an object map). The script
    /// runs in a locked-down engine (operation/depth caps, no ambient
    /// file/network/process access); the only capabilities it has are the
    /// host functions Dogwood registers (see `super::eval`).
    ///
    /// The script is given either inline (`script`) or as an external
    /// `.rhai` file (`scriptFile`) resolved relative to the declarations
    /// file; [`ProviderDeclarations::from_json_file`] reads the referenced
    /// file into `script`. Exactly one should be present once loaded.
    Rhai {
        #[serde(default)]
        script: Option<String>,
        #[serde(rename = "scriptFile", default)]
        script_file: Option<String>,
    },
}

impl Implementation {
    /// The resolved Rhai script body, if this is a `Rhai` implementation
    /// whose script has been loaded (inline or via `scriptFile`).
    pub fn rhai_script(&self) -> Option<&str> {
        match self {
            Implementation::Rhai { script, .. } => script.as_deref(),
        }
    }
}

/// A provider parameter / output type.
///
/// `Default` is derived so a struct literal can end in `..Default::default()`
/// and stay source-compatible when fields are added.
#[derive(Debug, Clone, Default, PartialEq, Eq, Deserialize)]
pub struct ParamType {
    #[serde(rename = "paramType")]
    pub param_type: String,
    /// For `record`: the field name -> type map.
    #[serde(default)]
    pub fields: BTreeMap<String, ParamType>,
    /// For `set`: the element type.
    #[serde(default)]
    pub items: Option<Box<ParamType>>,
    #[serde(default)]
    pub required: Vec<String>,
    /// For `entity`: the fully-qualified enum entity type (`Ns::Type`) the
    /// value is an id of. Only valid with `paramType: "entity"`.
    #[serde(rename = "entityType", default)]
    pub entity_type: Option<String>,
}

/// The `paramType` values a declaration may use.
const KNOWN_PARAM_TYPES: &[&str] = &[
    "string", "integer", "long", "bool", "boolean", "decimal", "set", "record", "entity",
];

/// The basename a provider enum is exported under, in the action schema's
/// namespace: its declared name with each `::` replaced by `_`
/// (`GuardDuty::Severity` -> `GuardDuty_Severity`, `Acme::Guard::Score` ->
/// `Acme_Guard_Score`). Fixed by the declaration alone, so it is the same in
/// every schema the enum is exported into.
pub(crate) fn exported_enum_basename(declared: &str) -> String {
    declared.replace("::", "_")
}

/// Check an entity type name is a valid, fully-qualified Cedar name outside
/// the reserved `__cedar` namespace; returns its namespace.
fn check_entity_type_name(name: &str) -> Result<&str, String> {
    if name.split("::").any(|segment| segment == "__cedar") {
        return Err(format!("`{name}` uses the reserved `__cedar` namespace"));
    }
    cedar_policy_core::ast::Name::from_normalized_str(name)
        .map_err(|_| format!("`{name}` is not a valid Cedar entity type name"))?;
    name.rsplit_once("::")
        .map(|(namespace, _)| namespace)
        .ok_or_else(|| format!("`{name}` must be fully qualified (`Ns::Type`)"))
}

impl ParamType {
    /// Add every `entityType` named in this type (at any nesting depth) to
    /// `out`.
    pub(crate) fn collect_entity_types(&self, out: &mut BTreeSet<String>) {
        if let Some(name) = &self.entity_type {
            out.insert(name.clone());
        }
        if let Some(items) = &self.items {
            items.collect_entity_types(out);
        }
        for field in self.fields.values() {
            field.collect_entity_types(out);
        }
    }

    /// Whether this type, or any type nested in it, uses `paramType:
    /// "entity"` or carries an `entityType`.
    pub(crate) fn mentions_entity(&self) -> bool {
        self.param_type == "entity"
            || self.entity_type.is_some()
            || self
                .items
                .as_deref()
                .is_some_and(ParamType::mentions_entity)
            || self.fields.values().any(ParamType::mentions_entity)
    }

    /// Push a warning for this type, or the first type nested in it on each
    /// path, whose kind is unknown and so falls back to `String`. A fallen-back
    /// type's nested `fields` / `items` are ignored, so they get no warning.
    fn collect_fallback_warnings(&self, at: &str, out: &mut Vec<String>) {
        let kind = self.param_type.as_str();
        if !KNOWN_PARAM_TYPES.contains(&kind) {
            out.push(format!(
                "{at}: unknown paramType `{kind}` does not match a known paramType; falling \
                 back to String (deprecated: an unknown paramType becomes an error in the next \
                 major version)"
            ));
            return;
        }
        if let Some(items) = &self.items {
            items.collect_fallback_warnings(&format!("{at}.items"), out);
        }
        for (name, field) in &self.fields {
            field.collect_fallback_warnings(&format!("{at}.{name}"), out);
        }
    }

    /// Structural checks for this type and everything nested in it, pushing
    /// one message per problem onto `errors`. `output_decls` is `Some` in
    /// output positions, where an entity type must be one this file declares
    /// in `entityTypes`; argument / input positions may also name an
    /// app-schema enum, which is checked later against the schema.
    fn check(
        &self,
        at: &str,
        output_decls: Option<&dyn Fn(&str) -> bool>,
        errors: &mut Vec<String>,
    ) {
        let kind = self.param_type.as_str();
        if !KNOWN_PARAM_TYPES.contains(&kind) {
            // Deprecated: an unknown kind is typed `String`, as before enum
            // support. It is an error only when it could hide an enum: falling
            // back would switch off literal checking, schema injection and
            // fail-closed conversion. Becomes an error everywhere in the next
            // major version.
            if self.mentions_entity() {
                errors.push(format!("{at}: unknown paramType `{kind}`"));
            }
            return;
        }
        if kind == "entity" {
            for (present, key) in [
                (!self.fields.is_empty(), "fields"),
                (self.items.is_some(), "items"),
                (!self.required.is_empty(), "required"),
            ] {
                if present {
                    errors.push(format!("{at}: `entity` paramType does not take `{key}`"));
                }
            }
            match self.entity_type.as_deref() {
                None => errors.push(format!("{at}: `entity` paramType requires `entityType`")),
                Some(name) => match check_entity_type_name(name) {
                    Err(e) => errors.push(format!("{at}: entityType {e}")),
                    Ok(_) => {
                        if let Some(declared) = output_decls
                            && !declared(name)
                        {
                            errors.push(format!("{at}: `{name}` is not declared in `entityTypes`"));
                        }
                    }
                },
            }
            return;
        }
        if self.entity_type.is_some() {
            errors.push(format!(
                "{at}: `entityType` is only valid with `paramType: \"entity\"`"
            ));
        }
        if let Some(items) = &self.items {
            items.check(&format!("{at}.items"), output_decls, errors);
        }
        for (name, field) in &self.fields {
            field.check(&format!("{at}.{name}"), output_decls, errors);
        }
    }

    /// Render this type as a Cedar schema type expression (for use
    /// inside a record's attribute list).
    pub fn to_cedar_type(&self) -> String {
        self.to_cedar_type_with(&BTreeMap::new())
    }

    /// [`to_cedar_type`](Self::to_cedar_type), naming each provider enum by
    /// the name it is exported under: `names` maps a declared enum name
    /// (`GuardDuty::Severity`) to its exported name
    /// (`Drupe::GuardDuty_Severity`). Entity types not in `names` (an app
    /// enum used as an argument) keep their name.
    pub(crate) fn to_cedar_type_with(&self, names: &BTreeMap<String, String>) -> String {
        match self.param_type.as_str() {
            "string" => "String".to_string(),
            "integer" | "long" => "Long".to_string(),
            "bool" | "boolean" => "Bool".to_string(),
            "decimal" => "decimal".to_string(),
            "set" => {
                let inner = self
                    .items
                    .as_ref()
                    .map(|t| t.to_cedar_type_with(names))
                    .unwrap_or_else(|| "String".to_string());
                format!("Set<{inner}>")
            }
            "record" => {
                let mut attrs: Vec<String> = Vec::new();
                for (name, ty) in &self.fields {
                    let opt = if self.required.contains(name) {
                        ""
                    } else {
                        "?"
                    };
                    attrs.push(format!("{name}{opt}: {}", ty.to_cedar_type_with(names)));
                }
                format!("{{ {} }}", attrs.join(", "))
            }
            // The enum type: a provider enum by its exported name (injected
            // into the augmented schema by `add_provider_entity_types`), an
            // app enum (argument positions) by its own name.
            "entity" => match self.entity_type.as_deref() {
                Some(name) => names.get(name).cloned().unwrap_or_else(|| name.to_string()),
                None => "String".to_string(),
            },
            // Deprecated fallback: `check` accepts an unknown kind that
            // involves no entity type, and it is typed `String` as before
            // enum support. Becomes an error in the next major version.
            _ => "String".to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn errors(json: &str) -> String {
        ProviderDeclarations::from_json(json).expect_err("should be rejected")
    }

    #[test]
    fn nested_output_positions_are_checked_with_their_path() {
        let err = errors(
            r#"{ "availableProviders": { "A::F": {
                "outputType": { "paramType": "record", "fields": {
                    "tags": { "paramType": "set", "items": { "paramType": "entity", "entityType": "A::Nope" } }
                } },
                "availableMethods": { "m": { "outputType": { "paramType": "entity", "entityType": "A::Gone" } } }
            } } }"#,
        );
        assert!(
            err.contains(
                "provider `A::F` outputType.tags.items: `A::Nope` is not declared in `entityTypes`"
            ),
            "{err}"
        );
        assert!(
            err.contains(
                "provider `A::F` method `m` outputType: `A::Gone` is not declared in `entityTypes`"
            ),
            "{err}"
        );
    }

    #[test]
    fn argument_and_input_positions_may_name_app_enums() {
        // Not in `entityTypes`: argument / inputType entity types may be
        // app-schema enums, resolved later against the action schema.
        ProviderDeclarations::from_json(
            r#"{ "availableProviders": { "A::F": {
                "argumentTypes": [ { "paramType": "entity", "entityType": "App::Level" } ],
                "outputType": { "paramType": "bool" },
                "availableMethods": { "m": {
                    "inputType": { "paramType": "entity", "entityType": "App::Kind" },
                    "outputType": { "paramType": "bool" } } }
            } } }"#,
        )
        .expect("argument and input entity types are not required in entityTypes");
    }

    #[test]
    fn unknown_param_type_without_entity_falls_back_to_string() {
        // Deprecated: kept loading until the next major version.
        let decls = ProviderDeclarations::from_json(
            r#"{ "availableProviders": { "A::F": {
                "argumentTypes": [ { "paramType": "string" }, { "paramType": "decimel" } ],
                "outputType": { "paramType": "bool" } } } }"#,
        )
        .expect("an unknown paramType without an entity type is accepted");
        assert_eq!(
            decls.available["A::F"].argument_types[1].to_cedar_type(),
            "String"
        );
        assert_eq!(
            decls.warnings(),
            [
                "provider `A::F` argumentTypes[1]: unknown paramType `decimel` does not match a \
                 known paramType; falling back to String (deprecated: an unknown paramType \
                 becomes an error in the next major version)"
            ]
        );
    }

    #[test]
    fn known_param_types_produce_no_warnings() {
        let decls = ProviderDeclarations::from_json(
            r#"{ "entityTypes": { "A::S": { "enum": ["X"] } },
                 "availableProviders": { "A::F": {
                "argumentTypes": [ { "paramType": "string" }, { "paramType": "long" },
                                   { "paramType": "boolean" }, { "paramType": "set",
                                     "items": { "paramType": "integer" } } ],
                "outputType": { "paramType": "record", "fields": {
                    "d": { "paramType": "decimal" }, "b": { "paramType": "bool" },
                    "e": { "paramType": "entity", "entityType": "A::S" } } } } } }"#,
        )
        .expect("loads");
        assert!(decls.warnings().is_empty(), "{:?}", decls.warnings());
    }

    #[test]
    fn fallback_warnings_cover_every_position() {
        let decls = ProviderDeclarations::from_json(
            r#"{ "availableProviders": { "A::F": {
                "argumentTypes": [ { "paramType": "Decimal" } ],
                "outputType": { "paramType": "record", "fields": {
                    "flagged": { "paramType": "bolean" },
                    "tags": { "paramType": "set", "items": { "paramType": "strng" } },
                    "at": { "paramType": "datetime" } } },
                "availableMethods": { "m": {
                    "argumentTypes": [ { "paramType": "integr" } ],
                    "inputType": { "paramType": "recrod" },
                    "outputType": { "paramType": "lng" } } }
            } } }"#,
        )
        .expect("an unknown paramType without an entity type is accepted");
        let warnings = decls.warnings().join("\n");
        for (at, kind) in [
            ("argumentTypes[0]", "Decimal"),
            ("outputType.flagged", "bolean"),
            ("outputType.tags.items", "strng"),
            ("outputType.at", "datetime"),
            ("method `m` argumentTypes[0]", "integr"),
            ("method `m` inputType", "recrod"),
            ("method `m` outputType", "lng"),
        ] {
            let expected = format!(
                "provider `A::F` {at}: unknown paramType `{kind}` does not match a known \
                 paramType; falling back to String"
            );
            assert!(
                warnings.contains(&expected),
                "missing `{expected}` in:\n{warnings}"
            );
        }
        assert_eq!(decls.warnings().len(), 7, "{warnings}");
        assert!(!warnings.contains("did you mean"), "{warnings}");
    }

    #[test]
    fn exported_names_replace_each_namespace_separator() {
        assert_eq!(exported_enum_basename("GuardDuty::Severity"), "GuardDuty_Severity");
        assert_eq!(exported_enum_basename("Acme::Guard::Score"), "Acme_Guard_Score");
    }

    #[test]
    fn declarations_exported_under_the_same_name_are_rejected() {
        let err = errors(
            r#"{ "entityTypes": { "A_B::C": { "enum": ["X"] }, "A::B_C": { "enum": ["Y"] } },
                 "availableProviders": {
                   "A_B::P": { "outputType": { "paramType": "entity", "entityType": "A_B::C" } },
                   "A::Q": { "outputType": { "paramType": "entity", "entityType": "A::B_C" } } } }"#,
        );
        assert!(
            err.contains("entityTypes: `A::B_C`, `A_B::C` are all exported as `A_B_C`"),
            "{err}"
        );
    }

    #[test]
    fn cedar_types_name_provider_enums_by_their_exported_name() {
        let ty: ParamType = serde_json::from_str(
            r#"{ "paramType": "record", "fields": {
                   "level": { "paramType": "entity", "entityType": "GuardDuty::Severity" },
                   "levels": { "paramType": "set",
                     "items": { "paramType": "entity", "entityType": "GuardDuty::Severity" } },
                   "app": { "paramType": "entity", "entityType": "Drupe::AlertLevel" } },
                 "required": ["level", "levels", "app"] }"#,
        )
        .unwrap();
        let names = BTreeMap::from([(
            "GuardDuty::Severity".to_string(),
            "Drupe::GuardDuty_Severity".to_string(),
        )]);
        assert_eq!(
            ty.to_cedar_type_with(&names),
            "{ app: Drupe::AlertLevel, level: Drupe::GuardDuty_Severity, \
             levels: Set<Drupe::GuardDuty_Severity> }"
        );
        assert_eq!(
            ty.to_cedar_type(),
            "{ app: Drupe::AlertLevel, level: GuardDuty::Severity, levels: Set<GuardDuty::Severity> }"
        );
    }

    #[test]
    fn unknown_param_type_with_entity_type_is_rejected() {
        let err = errors(
            r#"{ "availableProviders": { "A::F": {
                "argumentTypes": [ { "paramType": "entiy", "entityType": "App::Level" } ],
                "outputType": { "paramType": "bool" } } } }"#,
        );
        assert!(
            err.contains("provider `A::F` argumentTypes[0]: unknown paramType `entiy`"),
            "{err}"
        );
    }

    #[test]
    fn unknown_param_type_wrapping_an_entity_is_rejected() {
        let err = errors(
            r#"{ "availableProviders": { "A::F": {
                "argumentTypes": [ { "paramType": "sett",
                    "items": { "paramType": "entity", "entityType": "App::Level" } } ],
                "outputType": { "paramType": "bool" } } } }"#,
        );
        assert!(
            err.contains("provider `A::F` argumentTypes[0]: unknown paramType `sett`"),
            "{err}"
        );
    }

    #[test]
    fn every_problem_is_reported() {
        let err = errors(
            r#"{ "entityTypes": { "Other::T": { "enum": [] } },
                 "availableProviders": { "A::F": { "outputType": { "paramType": "entity" } } } }"#,
        );
        assert!(
            err.contains("entity type `Other::T` is not in a provider namespace"),
            "{err}"
        );
        assert!(err.contains("enum `Other::T` has no values"), "{err}");
        assert!(
            err.contains("`entity` paramType requires `entityType`"),
            "{err}"
        );
    }
}
