//! Schema-aware validation of `provider { … }` invocations.
//!
//! The provider dialect's contribution to `validate_source`: each hoisted
//! invocation must name a declared provider, supply the declared number of
//! arguments, and pass directly-typed literal/set arguments matching the
//! declared `argumentTypes`. Field-path arguments (`context.input.X`) are
//! left to Cedar/temporal schema validation. Provider output/projection
//! typing is checked by Cedar over the augmented schema (the comparison was
//! lowered to native Cedar), so it is not re-checked here.

use crate::api::ProviderField;
use crate::error::{Span, ValidationError};
use crate::extension::dialect::{DogwoodDialect, Rendered, ValidationCtx};
use crate::extension::provider::ast::Arg;

/// One provider validation finding, with its span already rebased into the
/// `.dw` source.
pub struct ProviderFinding {
    pub message: String,
    pub span: Span,
}

/// The provider dialect. Owns its leaf type — the public [`ProviderField`],
/// which carries its resolved declaration and the block-body base for span
/// rebasing. `validate` calls it by name.
pub struct ProviderDialect;

impl DogwoodDialect for ProviderDialect {
    type Leaf = ProviderField;
    type Finding = ProviderFinding;

    fn marker(&self) -> &'static str {
        "provider"
    }

    fn validate(&self, leaves: &[ProviderField], _ctx: &ValidationCtx<'_>) -> Vec<ProviderFinding> {
        let mut findings = Vec::new();
        for field in leaves {
            let key = field.invocation.key();
            // The invocation's span is relative to the `provider { … }` block
            // body; `field.body_base` is that body's offset in the `.dw`
            // source.
            let span = field.invocation.span.rebased(field.body_base);

            let Some(decl) = field.declaration.as_ref() else {
                // An invocation of a provider that isn't declared (its
                // declaration did not resolve at parse time). The lowering
                // defaults its output to a permissive type and raises nothing,
                // so this is the only layer that catches it.
                findings.push(ProviderFinding {
                    message: format!(
                        "provider `{key}` is not present in the provider declarations"
                    ),
                    span,
                });
                continue;
            };

            let expected = &decl.argument_types;
            let got = &field.invocation.args;
            if expected.len() != got.len() {
                findings.push(ProviderFinding {
                    message: format!(
                        "provider `{key}` expects {} argument(s) but got {}",
                        expected.len(),
                        got.len()
                    ),
                    span,
                });
                continue;
            }

            for (arg, param) in got.iter().zip(expected) {
                if let Some(actual) = arg_kind(arg)
                    && !param_type_accepts(&param.param_type, actual)
                {
                    findings.push(ProviderFinding {
                        message: format!(
                            "provider `{key}`: argument of type `{actual}` does not match the \
                             declared `{}`",
                            param.param_type
                        ),
                        span,
                    });
                }
            }

            // ── Method chain ────────────────────────────────────────────
            // Each method must be declared on the provider, must not shadow a
            // Cedar extension-method name (which would be ambiguous with the
            // native comparison forms), must be given the declared number and
            // types of arguments, and — when `inputType` is declared — must be
            // fed a compatible value by the preceding pipeline stage. The
            // pipeline's running type starts at the provider's `outputType`.
            let mut pipeline_type = decl.output_type.param_type.clone();
            for method in &field.methods {
                let m_span = method.span.rebased(field.body_base);

                if is_cedar_extension_method(&method.name) {
                    findings.push(ProviderFinding {
                        message: format!(
                            "provider `{key}`: method `{}` collides with a built-in Cedar \
                             extension method; rename the declared method",
                            method.name
                        ),
                        span: m_span,
                    });
                    continue;
                }

                let Some(mdecl) = decl.methods.get(&method.name) else {
                    let available = if decl.methods.is_empty() {
                        format!("provider `{key}` declares no methods")
                    } else {
                        format!(
                            "declared methods on `{key}` are: {}",
                            decl.methods.keys().cloned().collect::<Vec<_>>().join(", ")
                        )
                    };
                    findings.push(ProviderFinding {
                        message: format!(
                            "provider `{key}`: method `{}` is not declared ({available})",
                            method.name
                        ),
                        span: m_span,
                    });
                    // Unknown method breaks the pipeline type; stop checking
                    // the rest of this chain.
                    break;
                };

                // Optional receiver-type check: the previous stage's output
                // type must match what this method expects to receive.
                if let Some(input) = mdecl.input_type.as_ref()
                    && input.param_type != pipeline_type
                {
                    findings.push(ProviderFinding {
                        message: format!(
                            "provider `{key}`: method `{}` expects an input of type `{}` but the \
                             preceding stage produces `{}`",
                            method.name, input.param_type, pipeline_type
                        ),
                        span: m_span,
                    });
                }

                // Method argument count + directly-typed argument types.
                if mdecl.argument_types.len() != method.args.len() {
                    findings.push(ProviderFinding {
                        message: format!(
                            "provider `{key}`: method `{}` expects {} argument(s) but got {}",
                            method.name,
                            mdecl.argument_types.len(),
                            method.args.len()
                        ),
                        span: m_span,
                    });
                } else {
                    for (arg, param) in method.args.iter().zip(&mdecl.argument_types) {
                        if let Some(actual) = arg_kind(arg)
                            && !param_type_accepts(&param.param_type, actual)
                        {
                            findings.push(ProviderFinding {
                                message: format!(
                                    "provider `{key}`: method `{}` argument of type `{actual}` \
                                     does not match the declared `{}`",
                                    method.name, param.param_type
                                ),
                                span: m_span,
                            });
                        }
                    }
                }

                // This method re-types the pipeline for the next stage.
                pipeline_type = mdecl.output_type.param_type.clone();
            }
        }
        findings
    }

    fn render(&self, finding: ProviderFinding, src: &std::sync::Arc<str>) -> Rendered {
        let help = derive_provider_help(&finding.message);
        Rendered::Error(ValidationError::Extension {
            code: self.marker(),
            message: finding.message,
            span: finding.span.into(),
            label: None,
            help,
            src: src.clone(),
            source: None,
        })
    }
}

/// Derive actionable help text from a provider validation finding's message.
fn derive_provider_help(message: &str) -> Option<String> {
    if message.contains("is not present in the provider declarations") {
        Some("check the `availableProviders` in your provider declarations JSON".to_string())
    } else if message.contains("expects") && message.contains("argument(s) but got") {
        Some("check the `argumentTypes` array in the provider declaration".to_string())
    } else if message.contains("does not match the declared") {
        Some(
            "provider arguments are typed: string, integer, decimal, bool, or set; \
             field-path arguments (context.input.X) are type-checked by Cedar"
                .to_string(),
        )
    } else if message.contains("is not declared") && message.contains("method") {
        Some("check the `availableMethods` in the provider declaration".to_string())
    } else if message.contains("collides with a built-in Cedar extension method") {
        Some(
            "Cedar extension methods (contains, lessThan, isIpv4, etc.) cannot be \
             shadowed by provider methods; rename the method in the declaration"
                .to_string(),
        )
    } else if message.contains("expects an input of type") {
        Some(
            "each method's `inputType` constrains what the preceding pipeline stage must produce"
                .to_string(),
        )
    } else {
        None
    }
}

/// The declared `paramType` token a directly-typed argument satisfies, or
/// `None` for a field path (deferred to schema validation).
fn arg_kind(arg: &Arg) -> Option<&'static str> {
    match arg {
        Arg::String(_) => Some("string"),
        Arg::Integer(_) => Some("integer"),
        Arg::Decimal(_) => Some("decimal"),
        Arg::Bool(_) => Some("bool"),
        Arg::Set(_) => Some("set"),
        Arg::Field(_) => None,
    }
}

/// Whether a declared `paramType` accepts an argument of the given kind.
/// `integer`/`long` and `bool`/`boolean` are accepted as synonyms.
fn param_type_accepts(declared: &str, actual: &str) -> bool {
    match actual {
        "string" => declared == "string",
        "integer" => declared == "integer" || declared == "long",
        "decimal" => declared == "decimal",
        "bool" => declared == "bool" || declared == "boolean",
        "set" => declared == "set",
        _ => false,
    }
}

/// The Cedar extension-method / built-in names a provider method may not
/// shadow. The decimal comparison methods (`lessThan`, …) are the terminal
/// comparison form of the provider grammar (`method_cmp`), and the rest are
/// Cedar's native set / entity-tag / IP / datetime methods; a declared
/// provider method sharing one of these names would be ambiguous, so it is
/// rejected. This mirrors the exclusion list the grammar uses to keep
/// `.lessThan(…)` a comparison rather than a projection method.
fn is_cedar_extension_method(name: &str) -> bool {
    matches!(
        name,
        "lessThan"
            | "lessThanOrEqual"
            | "greaterThan"
            | "greaterThanOrEqual"
            | "contains"
            | "containsAll"
            | "containsAny"
            | "isEmpty"
            | "hasTag"
            | "getTag"
            | "isIpv4"
            | "isIpv6"
            | "isLoopback"
            | "isMulticast"
            | "isInRange"
            | "offset"
            | "durationSince"
            | "toDate"
            | "toTime"
            | "toMilliseconds"
            | "toSeconds"
            | "toMinutes"
            | "toHours"
            | "toDays"
    )
}
