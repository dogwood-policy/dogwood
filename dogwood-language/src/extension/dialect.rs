//! The sublanguage-extension validation interface.
//!
//! Each Dogwood sublanguage ("dialect" — temporal, provider) contributes its
//! schema-aware checks through the [`DogwoodDialect`] trait: it owns its leaf
//! type, its private finding shape, and how a finding renders (with severity)
//! into the shared [`ValidationError`] / [`ValidationWarning`]
//! currency. `validate` calls each dialect **by name** — the dialect set is
//! concrete because the lowered artifacts ([`Lowered`](crate::api::Lowered))
//! are concrete about it (`Lowered.temporal` / `Lowered.providers` are named
//! fields), so there is no anonymous registry to fold over. A dialect's `run`
//! (a provided method) validates its leaves and partitions the rendered
//! findings into the error and warning channels.

use crate::error::{ValidationError, ValidationWarning};

/// A dialect finding rendered into the shared currency, tagged by severity.
/// The dialect chooses the channel by which variant it builds, so severity
/// and the concrete diagnostic are decided together in one place.
pub enum Rendered {
    Error(ValidationError),
    /// A dialect warning. No shipping dialect emits one yet (temporal and
    /// provider only build `Error`), but the variant keeps the severity axis
    /// symmetric so a future dialect — or a future lint on an existing one —
    /// can warn without reshaping this enum or the `run` partition.
    #[allow(dead_code)]
    Warning(ValidationWarning),
}

/// What a dialect's `validate` needs beyond its own leaves:
/// - the augmented Cedar [`Schema`](cedar_policy::Schema) (a dialect needing
///   typed schema info derives it from `schema.as_ref()`, a `ValidatorSchema`,
///   rather than re-parsing a source string),
/// - the derived event schema (the temporal dialect checks predicate event /
///   field names against it), and
/// - the `.dw` source, so a rendered finding can embed it and self-render.
pub struct ValidationCtx<'a> {
    pub schema: &'a cedar_policy::Schema,
    pub event_schema: &'a crate::event_schema::derive::DerivedEventSchema,
    pub dw_src: &'a std::sync::Arc<str>,
}

/// A Dogwood sublanguage dialect's validation contract. Implemented once per
/// dialect; `validate` produces the dialect's own findings, `render` maps one
/// to the shared currency with severity, and the provided [`run`](DogwoodDialect::run)
/// ties them together into the two output channels.
pub trait DogwoodDialect {
    /// This dialect's hoisted leaf — the `Lowered` field it validates
    /// (temporal `TemporalField`, provider `ProviderField`).
    type Leaf;

    /// This dialect's own validation finding shape — the dialect owns what a
    /// problem looks like before it is rendered to the shared diagnostic.
    type Finding;

    /// The marker keyword (`"temporal"` / `"provider"`), used as the
    /// diagnostic code so the shared error type need not name the dialect.
    fn marker(&self) -> &'static str;

    /// Validate this dialect's leaves against the schema.
    fn validate(&self, leaves: &[Self::Leaf], ctx: &ValidationCtx<'_>) -> Vec<Self::Finding>;

    /// Render one finding into the shared currency as a [`Rendered`], choosing
    /// the error or warning channel. The dialect owns the
    /// message/span/code/severity mapping; the validator core never matches on
    /// a dialect to build a finding. `src` is the `.dw` source to embed on the
    /// finding so it self-renders.
    fn render(&self, finding: Self::Finding, src: &std::sync::Arc<str>) -> Rendered;

    /// Validate `leaves` and partition the rendered findings into the error
    /// and warning channels. This is what `validate` calls per dialect.
    fn run(
        &self,
        leaves: &[Self::Leaf],
        ctx: &ValidationCtx<'_>,
    ) -> (Vec<ValidationError>, Vec<ValidationWarning>) {
        let mut errors = Vec::new();
        let mut warnings = Vec::new();
        for finding in self.validate(leaves, ctx) {
            match self.render(finding, ctx.dw_src) {
                Rendered::Error(e) => errors.push(e),
                Rendered::Warning(w) => warnings.push(w),
            }
        }
        (errors, warnings)
    }
}

#[cfg(test)]
mod tests {
    //! A brand-new dialect plugs into validation by implementing
    //! `DogwoodDialect` and nothing else: it owns its leaf and finding types,
    //! and its `run` (the provided method) maps findings through `render` into
    //! the shared error / warning channels — so a dialect can emit *both*
    //! severities, and the partition logic is written once on the trait. This
    //! toy dialect flags leaves either as errors or as warnings to exercise
    //! both channels.

    use super::*;
    use crate::error::{Span, ValidationError, ValidationWarning};

    /// A toy leaf: a name plus whether it should render as a warning.
    struct ToyLeaf {
        name: String,
        warn: bool,
    }

    struct ToyFinding {
        message: String,
        warn: bool,
    }

    struct ToyDialect;

    impl DogwoodDialect for ToyDialect {
        type Leaf = ToyLeaf;
        type Finding = ToyFinding;

        fn marker(&self) -> &'static str {
            "toy"
        }

        fn validate(&self, leaves: &[ToyLeaf], _ctx: &ValidationCtx<'_>) -> Vec<ToyFinding> {
            leaves
                .iter()
                .map(|l| ToyFinding {
                    message: format!("toy leaf `{}` flagged", l.name),
                    warn: l.warn,
                })
                .collect()
        }

        fn render(&self, finding: ToyFinding, src: &std::sync::Arc<str>) -> Rendered {
            if finding.warn {
                Rendered::Warning(ValidationWarning::Extension {
                    code: self.marker(),
                    message: finding.message,
                    span: Span::new(0, 1).into(),
                    label: None,
                    help: None,
                    src: src.clone(),
                    source: None,
                })
            } else {
                Rendered::Error(ValidationError::Extension {
                    code: self.marker(),
                    message: finding.message,
                    span: Span::new(0, 1).into(),
                    label: None,
                    help: None,
                    src: src.clone(),
                    source: None,
                })
            }
        }
    }

    /// A minimal empty Cedar schema for the context (the toy dialect ignores
    /// it, but `ValidationCtx` requires one).
    fn empty_schema() -> cedar_policy::Schema {
        cedar_policy::Schema::from_cedarschema_str("")
            .expect("empty schema parses")
            .0
    }

    /// An empty derived event schema (the toy dialect ignores it).
    fn empty_event_schema() -> crate::event_schema::derive::DerivedEventSchema {
        crate::event_schema::derive::DerivedEventSchema {
            events: Vec::new(),
            max_window: crate::event_schema::derive::DEFAULT_MAX_WINDOW,
        }
    }

    #[test]
    fn run_partitions_findings_into_error_and_warning_channels() {
        let leaves = vec![
            ToyLeaf {
                name: "alpha".into(),
                warn: false,
            },
            ToyLeaf {
                name: "beta".into(),
                warn: true,
            },
        ];
        let schema = empty_schema();
        let event_schema = empty_event_schema();
        let src: std::sync::Arc<str> = std::sync::Arc::from("");
        let ctx = ValidationCtx {
            schema: &schema,
            event_schema: &event_schema,
            dw_src: &src,
        };

        let (errors, warnings) = ToyDialect.run(&leaves, &ctx);

        assert_eq!(errors.len(), 1, "the non-warn leaf renders as an error");
        assert_eq!(warnings.len(), 1, "the warn leaf renders as a warning");
        assert!(matches!(
            errors[0],
            ValidationError::Extension { code: "toy", .. }
        ));
        assert!(matches!(
            warnings[0],
            ValidationWarning::Extension { code: "toy", .. }
        ));
    }

    #[test]
    fn run_on_no_leaves_finds_nothing() {
        let schema = empty_schema();
        let event_schema = empty_event_schema();
        let src: std::sync::Arc<str> = std::sync::Arc::from("");
        let ctx = ValidationCtx {
            schema: &schema,
            event_schema: &event_schema,
            dw_src: &src,
        };

        let (errors, warnings) = ToyDialect.run(&[], &ctx);

        assert!(errors.is_empty());
        assert!(warnings.is_empty());
    }
}
