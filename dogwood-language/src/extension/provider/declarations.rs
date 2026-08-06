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

use std::collections::BTreeMap;
use std::path::Path;

use serde::Deserialize;

/// The parsed declarations file.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct ProviderDeclarations {
    #[serde(rename = "availableProviders", default)]
    pub available: BTreeMap<String, ProviderDecl>,
}

impl ProviderDeclarations {
    /// Parse from JSON text. Any `implementation` that uses `scriptFile`
    /// (an external `.rhai` reference) is left unresolved — use
    /// [`from_json_file`](Self::from_json_file) to also read those files.
    pub fn from_json(json: &str) -> Result<Self, String> {
        let json = json.strip_prefix('\u{FEFF}').unwrap_or(json);
        serde_json::from_str(json).map_err(|e| format!("providers.json: {e}"))
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
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
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
}

impl ParamType {
    /// Render this type as a Cedar schema type expression (for use
    /// inside a record's attribute list).
    pub fn to_cedar_type(&self) -> String {
        match self.param_type.as_str() {
            "string" => "String".to_string(),
            "integer" | "long" => "Long".to_string(),
            "bool" | "boolean" => "Bool".to_string(),
            "decimal" => "decimal".to_string(),
            "set" => {
                let inner = self
                    .items
                    .as_ref()
                    .map(|t| t.to_cedar_type())
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
                    attrs.push(format!("{name}{opt}: {}", ty.to_cedar_type()));
                }
                format!("{{ {} }}", attrs.join(", "))
            }
            other => {
                // Unknown leaf type — fall back to a permissive String.
                let _ = other;
                "String".to_string()
            }
        }
    }
}
