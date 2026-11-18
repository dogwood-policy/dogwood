//! LSP-independent projection of Dogwood findings into LSP diagnostics.

use std::error::Error;
use std::fmt;

use lsp_types::{
    Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity, Location, NumberOrString,
    Position, PublishDiagnosticsParams, Range, Uri,
};

use crate::frontend::{
    DiagnosticLabel, EventSchemaParseReport, Finding, FrontendOutcome, OperationalLimitExceeded,
    OperationalLimitKind, Severity, SourceKind, ValidationReport,
};

pub const DIAGNOSTIC_SOURCE: &str = "dogwood";
pub const PROJECT_DIAGNOSTIC_CODE: &str = "dogwood.project";
pub const INPUT_DIAGNOSTIC_CODE: &str = "dogwood.input";
pub const OPERATIONAL_LIMIT_DIAGNOSTIC_CODE: &str = "dogwood.operationalLimit";

#[derive(Clone, Copy, Debug)]
pub struct SourceDocument<'a> {
    pub uri: &'a Uri,
    pub text: &'a str,
}

#[derive(Clone, Copy, Debug)]
pub struct BundleDocuments<'a> {
    pub policy: SourceDocument<'a>,
    pub action_schema: SourceDocument<'a>,
    pub event_schema: Option<SourceDocument<'a>>,
    pub providers: Option<SourceDocument<'a>>,
    pub macros: Option<SourceDocument<'a>>,
}

impl<'a> BundleDocuments<'a> {
    fn source(self, kind: SourceKind) -> Option<SourceDocument<'a>> {
        match kind {
            SourceKind::Policy => Some(self.policy),
            SourceKind::ActionSchema => Some(self.action_schema),
            SourceKind::EventSchema => self.event_schema,
            SourceKind::Providers => self.providers,
            SourceKind::Macros => self.macros,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DiagnosticRangeError {
    ArithmeticOverflow,
    OutOfBounds,
    InvalidUtf8Boundary,
    InsideLineTerminator,
}

impl fmt::Display for DiagnosticRangeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let message = match self {
            Self::ArithmeticOverflow => "diagnostic byte range overflows",
            Self::OutOfBounds => "diagnostic byte range is outside the source",
            Self::InvalidUtf8Boundary => "diagnostic byte range is not on UTF-8 boundaries",
            Self::InsideLineTerminator => "diagnostic byte range is inside a CRLF terminator",
        };
        formatter.write_str(message)
    }
}

impl Error for DiagnosticRangeError {}

pub fn byte_range_to_utf16(
    source: &str,
    start: usize,
    len: usize,
) -> Result<Range, DiagnosticRangeError> {
    Utf16Map::new(source).range(start, len)
}

pub fn project_frontend_outcome(
    version: i32,
    documents: BundleDocuments<'_>,
    outcome: FrontendOutcome<ValidationReport>,
) -> PublishDiagnosticsParams {
    let policy_uri = documents.policy.uri.clone();
    let mut projector = Projector::new(documents);
    let diagnostics = match outcome {
        FrontendOutcome::Report(report) => projector.project_report(report),
        FrontendOutcome::Fatal(fatal) => std::iter::once(*fatal.diagnostic)
            .chain(fatal.related)
            .map(|finding| projector.project_finding(finding))
            .collect(),
        FrontendOutcome::OperationalLimit(limit) => {
            vec![operational_limit_diagnostic(documents, limit)]
        }
    };
    PublishDiagnosticsParams::new(policy_uri, diagnostics, Some(version))
}

pub fn project_event_schema_outcome(
    version: i32,
    document: SourceDocument<'_>,
    outcome: FrontendOutcome<EventSchemaParseReport>,
) -> PublishDiagnosticsParams {
    let diagnostics = match outcome {
        FrontendOutcome::Report(_) => Vec::new(),
        FrontendOutcome::Fatal(fatal) => std::iter::once(*fatal.diagnostic)
            .chain(fatal.related)
            .map(|finding| project_standalone_finding(document, finding))
            .collect(),
        FrontendOutcome::OperationalLimit(limit) => vec![server_error_diagnostic(
            OPERATIONAL_LIMIT_DIAGNOSTIC_CODE,
            format!(
                "Dogwood {} input exceeds the {} limit: observed {}, limit {}",
                limit.source_kind.as_str(),
                operational_limit_name(limit.kind),
                limit.observed,
                limit.limit
            ),
            None,
        )],
    };
    PublishDiagnosticsParams::new(document.uri.clone(), diagnostics, Some(version))
}

fn project_standalone_finding(document: SourceDocument<'_>, finding: Finding) -> Diagnostic {
    let map = Utf16Map::new(document.text);
    let range = finding
        .labels
        .first()
        .and_then(|label| map.diagnostic_range(label.start, label.len).ok())
        .unwrap_or_else(zero_range);
    let related_information = finding.labels.get(1..).and_then(|labels| {
        (!labels.is_empty()).then(|| {
            labels
                .iter()
                .map(|label| DiagnosticRelatedInformation {
                    location: Location {
                        uri: document.uri.clone(),
                        range: map
                            .diagnostic_range(label.start, label.len)
                            .unwrap_or_else(|_| zero_range()),
                    },
                    message: label
                        .message
                        .clone()
                        .unwrap_or_else(|| finding.message.clone()),
                })
                .collect()
        })
    });

    Diagnostic {
        range,
        severity: Some(match finding.severity {
            Severity::Error => DiagnosticSeverity::ERROR,
            Severity::Warning => DiagnosticSeverity::WARNING,
            Severity::Advice => DiagnosticSeverity::INFORMATION,
        }),
        code: finding.code.map(NumberOrString::String),
        code_description: None,
        source: Some(DIAGNOSTIC_SOURCE.to_owned()),
        message: finding.message,
        related_information,
        tags: None,
        data: None,
    }
}

pub fn server_error_diagnostic(
    code: &'static str,
    message: String,
    related: Option<(Uri, Range, String)>,
) -> Diagnostic {
    Diagnostic {
        range: zero_range(),
        severity: Some(DiagnosticSeverity::ERROR),
        code: Some(NumberOrString::String(code.to_owned())),
        code_description: None,
        source: Some(DIAGNOSTIC_SOURCE.to_owned()),
        message,
        related_information: related.map(|(uri, range, message)| {
            vec![DiagnosticRelatedInformation {
                location: Location { uri, range },
                message,
            }]
        }),
        tags: None,
        data: None,
    }
}

pub fn zero_range() -> Range {
    Range::new(Position::new(0, 0), Position::new(0, 0))
}

struct Projector<'a> {
    documents: BundleDocuments<'a>,
    policy_map: Option<Utf16Map>,
    action_schema_map: Option<Utf16Map>,
    event_schema_map: Option<Utf16Map>,
    providers_map: Option<Utf16Map>,
    macros_map: Option<Utf16Map>,
}

impl<'a> Projector<'a> {
    fn new(documents: BundleDocuments<'a>) -> Self {
        Self {
            documents,
            policy_map: None,
            action_schema_map: None,
            event_schema_map: None,
            providers_map: None,
            macros_map: None,
        }
    }

    fn project_report(&mut self, report: ValidationReport) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::with_capacity(report.errors.len() + report.warnings.len());
        for finding in report.errors {
            diagnostics.push(self.project_finding(finding));
        }
        for finding in report.warnings {
            diagnostics.push(self.project_finding(finding));
        }
        if !report.passed_without_warnings && diagnostics.is_empty() {
            diagnostics.push(server_error_diagnostic(
                INPUT_DIAGNOSTIC_CODE,
                "Dogwood validation did not pass cleanly but emitted no findings".to_owned(),
                None,
            ));
        }
        diagnostics
    }

    fn project_finding(&mut self, finding: Finding) -> Diagnostic {
        let source_kind = finding.source_kind;
        let attributed = source_kind.and_then(|kind| self.documents.source(kind));
        let is_policy = source_kind == Some(SourceKind::Policy);
        let range = if is_policy {
            finding.labels.first().map_or_else(zero_range, |label| {
                self.label_range(SourceKind::Policy, label)
            })
        } else {
            zero_range()
        };
        let related_labels = if is_policy {
            finding.labels.get(1..).unwrap_or_default()
        } else {
            finding.labels.as_slice()
        };
        let related_information = attributed.and_then(|source| {
            let kind = source_kind.expect("an attributed source has a source kind");
            (!related_labels.is_empty() || !is_policy).then(|| {
                if related_labels.is_empty() {
                    return vec![DiagnosticRelatedInformation {
                        location: Location {
                            uri: source.uri.clone(),
                            range: zero_range(),
                        },
                        message: finding.message.clone(),
                    }];
                }
                related_labels
                    .iter()
                    .map(|label| DiagnosticRelatedInformation {
                        location: Location {
                            uri: source.uri.clone(),
                            range: self.label_range(kind, label),
                        },
                        message: label
                            .message
                            .clone()
                            .unwrap_or_else(|| finding.message.clone()),
                    })
                    .collect()
            })
        });

        Diagnostic {
            range,
            severity: Some(match finding.severity {
                Severity::Error => DiagnosticSeverity::ERROR,
                Severity::Warning => DiagnosticSeverity::WARNING,
                Severity::Advice => DiagnosticSeverity::INFORMATION,
            }),
            code: finding.code.map(NumberOrString::String),
            code_description: None,
            source: Some(DIAGNOSTIC_SOURCE.to_owned()),
            message: finding.message,
            related_information,
            tags: None,
            data: None,
        }
    }

    fn label_range(&mut self, kind: SourceKind, label: &DiagnosticLabel) -> Range {
        let Some(source) = self.documents.source(kind) else {
            return zero_range();
        };
        let map = match kind {
            SourceKind::Policy => &mut self.policy_map,
            SourceKind::ActionSchema => &mut self.action_schema_map,
            SourceKind::EventSchema => &mut self.event_schema_map,
            SourceKind::Providers => &mut self.providers_map,
            SourceKind::Macros => &mut self.macros_map,
        };
        map.get_or_insert_with(|| Utf16Map::new(source.text))
            .diagnostic_range(label.start, label.len)
            .unwrap_or_else(|_| zero_range())
    }
}

fn operational_limit_diagnostic(
    documents: BundleDocuments<'_>,
    limit: OperationalLimitExceeded,
) -> Diagnostic {
    let source = documents.source(limit.source_kind);
    let related = (limit.source_kind != SourceKind::Policy)
        .then_some(source)
        .flatten()
        .map(|source| {
            (
                source.uri.clone(),
                zero_range(),
                format!(
                    "{} input exceeds its validation resource limit",
                    limit.source_kind.as_str()
                ),
            )
        });
    server_error_diagnostic(
        OPERATIONAL_LIMIT_DIAGNOSTIC_CODE,
        format!(
            "Dogwood {} input exceeds the {} limit: observed {}, limit {}",
            limit.source_kind.as_str(),
            operational_limit_name(limit.kind),
            limit.observed,
            limit.limit
        ),
        related,
    )
}

fn operational_limit_name(kind: OperationalLimitKind) -> &'static str {
    match kind {
        OperationalLimitKind::SourceBytes => "source byte",
        OperationalLimitKind::StructuralNesting => "structural nesting",
        OperationalLimitKind::ExpressionChain => "expression chain",
    }
}

struct Utf16Map {
    positions: Vec<u64>,
}

impl Utf16Map {
    const INVALID: u64 = u64::MAX;
    const INVALID_UTF8: u64 = u64::MAX - 1;

    fn new(source: &str) -> Self {
        let mut positions = vec![Self::INVALID; source.len() + 1];
        let mut offset = 0;
        let mut line = 0_u32;
        let mut column = 0_u32;
        positions[0] = encode_position(line, column);

        while offset < source.len() {
            let tail = &source[offset..];
            if tail.starts_with("\r\n") {
                offset += 2;
                line += 1;
                column = 0;
                positions[offset] = encode_position(line, column);
                continue;
            }

            let character = tail
                .chars()
                .next()
                .expect("non-empty source tail has a character");
            let width = character.len_utf8();
            if matches!(character, '\r' | '\n') {
                offset += width;
                line += 1;
                column = 0;
            } else {
                for position in &mut positions[offset + 1..offset + width] {
                    *position = Self::INVALID_UTF8;
                }
                offset += width;
                column += u32::try_from(character.len_utf16())
                    .expect("one character's UTF-16 length fits u32");
            }
            positions[offset] = encode_position(line, column);
        }

        Self { positions }
    }

    fn range(&self, start: usize, len: usize) -> Result<Range, DiagnosticRangeError> {
        let end = start
            .checked_add(len)
            .ok_or(DiagnosticRangeError::ArithmeticOverflow)?;
        let start_position = self.position(start)?;
        let end_position = self.position(end)?;
        Ok(Range::new(start_position, end_position))
    }

    fn diagnostic_range(&self, start: usize, len: usize) -> Result<Range, DiagnosticRangeError> {
        let source_len = self.positions.len() - 1;
        if start == source_len && len == 1 {
            self.range(start, 0)
        } else {
            self.range(start, len)
        }
    }

    fn position(&self, offset: usize) -> Result<Position, DiagnosticRangeError> {
        let encoded = *self
            .positions
            .get(offset)
            .ok_or(DiagnosticRangeError::OutOfBounds)?;
        match encoded {
            Self::INVALID_UTF8 => return Err(DiagnosticRangeError::InvalidUtf8Boundary),
            Self::INVALID => return Err(DiagnosticRangeError::InsideLineTerminator),
            _ => {}
        }
        Ok(Position::new((encoded >> 32) as u32, encoded as u32))
    }
}

fn encode_position(line: u32, column: u32) -> u64 {
    (u64::from(line) << 32) | u64::from(column)
}

// dogwood-lsp handles Unix paths and file URIs only, so its tests run on Unix.
#[cfg(all(test, unix))]
mod tests {
    use std::str::FromStr;

    use crate::frontend::{DiagnosticLabel, Finding};

    use super::*;

    fn range(start_line: u32, start: u32, end_line: u32, end: u32) -> Range {
        Range::new(
            Position::new(start_line, start),
            Position::new(end_line, end),
        )
    }

    fn project_policy_label_range(source: &str, start: usize, len: usize) -> Range {
        let policy_uri = Uri::from_str("file:///policy.dw").unwrap();
        let schema_uri = Uri::from_str("file:///actions.cedarschema").unwrap();
        let documents = BundleDocuments {
            policy: SourceDocument {
                uri: &policy_uri,
                text: source,
            },
            action_schema: SourceDocument {
                uri: &schema_uri,
                text: "",
            },
            event_schema: None,
            providers: None,
            macros: None,
        };
        let fatal = crate::frontend::FatalReport {
            diagnostic: Box::new(Finding {
                severity: Severity::Error,
                code: None,
                message: "test diagnostic".to_owned(),
                labels: vec![DiagnosticLabel {
                    start,
                    len,
                    message: None,
                }],
                help: None,
                spanned: true,
                source_kind: Some(SourceKind::Policy),
            }),
            related: Vec::new(),
        };

        project_frontend_outcome(1, documents, FrontendOutcome::Fatal(fatal)).diagnostics[0].range
    }

    #[test]
    fn byte_ranges_project_ascii_astral_and_crlf_to_utf16() {
        let source = "ab\u{1f600}c\r\nde";

        assert_eq!(byte_range_to_utf16(source, 0, 2), Ok(range(0, 0, 0, 2)));
        assert_eq!(byte_range_to_utf16(source, 2, 4), Ok(range(0, 2, 0, 4)));
        assert_eq!(byte_range_to_utf16(source, 6, 1), Ok(range(0, 4, 0, 5)));
        assert_eq!(byte_range_to_utf16(source, 7, 2), Ok(range(0, 5, 1, 0)));
        assert_eq!(byte_range_to_utf16(source, 9, 2), Ok(range(1, 0, 1, 2)));
    }

    #[test]
    fn byte_ranges_support_zero_width_and_eof() {
        let source = "x\n";

        assert_eq!(byte_range_to_utf16(source, 0, 0), Ok(range(0, 0, 0, 0)));
        assert_eq!(byte_range_to_utf16(source, 1, 0), Ok(range(0, 1, 0, 1)));
        assert_eq!(byte_range_to_utf16(source, 2, 0), Ok(range(1, 0, 1, 0)));
        assert_eq!(byte_range_to_utf16(source, 1, 1), Ok(range(0, 1, 1, 0)));
    }

    #[test]
    fn invalid_ranges_fail_without_panicking() {
        let source = "\u{1f600}\r\n";

        assert_eq!(
            byte_range_to_utf16(source, usize::MAX, 2),
            Err(DiagnosticRangeError::ArithmeticOverflow)
        );
        assert_eq!(
            byte_range_to_utf16(source, source.len() + 1, 0),
            Err(DiagnosticRangeError::OutOfBounds)
        );
        assert_eq!(
            byte_range_to_utf16(source, 1, 0),
            Err(DiagnosticRangeError::InvalidUtf8Boundary)
        );
        assert_eq!(
            byte_range_to_utf16(source, 5, 0),
            Err(DiagnosticRangeError::InsideLineTerminator)
        );
    }

    #[test]
    fn fixed_synthetic_eof_label_projects_to_astral_utf16_eof() {
        let source = "a\u{1f600}";

        assert_eq!(
            project_policy_label_range(source, source.len(), 1),
            range(0, 3, 0, 3)
        );
    }

    #[test]
    fn pre_eof_overrun_uses_the_invalid_range_fallback() {
        let source = "a\u{1f600}";

        assert_eq!(
            project_policy_label_range(source, 1, source.len()),
            zero_range()
        );
    }

    #[test]
    fn label_starting_past_eof_uses_the_invalid_range_fallback() {
        let source = "a\u{1f600}";

        assert_eq!(
            project_policy_label_range(source, source.len() + 1, 1),
            zero_range()
        );
    }

    #[test]
    fn zero_width_eof_label_remains_a_valid_utf16_eof_range() {
        let source = "a\u{1f600}";

        assert_eq!(
            project_policy_label_range(source, source.len(), 0),
            range(0, 3, 0, 3)
        );
    }

    #[test]
    fn findings_preserve_message_code_severity_and_related_ranges() {
        let policy_uri = Uri::from_str("file:///policy.dw").unwrap();
        let schema_uri = Uri::from_str("file:///actions.cedarschema").unwrap();
        let documents = BundleDocuments {
            policy: SourceDocument {
                uri: &policy_uri,
                text: "a\u{1f600}z",
            },
            action_schema: SourceDocument {
                uri: &schema_uri,
                text: "schema",
            },
            event_schema: None,
            providers: None,
            macros: None,
        };
        let report = ValidationReport {
            passed: false,
            passed_without_warnings: false,
            errors: vec![Finding {
                severity: Severity::Error,
                code: Some("E1".to_owned()),
                message: "exact message".to_owned(),
                labels: vec![
                    DiagnosticLabel {
                        start: 1,
                        len: 4,
                        message: None,
                    },
                    DiagnosticLabel {
                        start: 5,
                        len: 1,
                        message: Some("related".to_owned()),
                    },
                ],
                help: None,
                spanned: true,
                source_kind: Some(SourceKind::Policy),
            }],
            warnings: Vec::new(),
        };

        let published = project_frontend_outcome(7, documents, FrontendOutcome::Report(report));
        assert_eq!(published.version, Some(7));
        assert_eq!(published.diagnostics[0].range, range(0, 1, 0, 3));
        assert_eq!(
            published.diagnostics[0].severity,
            Some(DiagnosticSeverity::ERROR)
        );
        assert_eq!(
            published.diagnostics[0].code,
            Some(NumberOrString::String("E1".to_owned()))
        );
        assert_eq!(
            published.diagnostics[0].source.as_deref(),
            Some(DIAGNOSTIC_SOURCE)
        );
        assert_eq!(published.diagnostics[0].message, "exact message");
        let related = published.diagnostics[0]
            .related_information
            .as_ref()
            .unwrap();
        assert_eq!(related[0].location.uri, policy_uri);
        assert_eq!(related[0].location.range, range(0, 3, 0, 4));
        assert_eq!(related[0].message, "related");
    }

    #[test]
    fn dependency_findings_use_policy_zero_range_and_dependency_related_information() {
        let policy_uri = Uri::from_str("file:///policy.dw").unwrap();
        let schema_uri = Uri::from_str("file:///actions.cedarschema").unwrap();
        let documents = BundleDocuments {
            policy: SourceDocument {
                uri: &policy_uri,
                text: "policy",
            },
            action_schema: SourceDocument {
                uri: &schema_uri,
                text: "bad schema",
            },
            event_schema: None,
            providers: None,
            macros: None,
        };
        let fatal = crate::frontend::FatalReport {
            diagnostic: Box::new(Finding {
                severity: Severity::Error,
                code: None,
                message: "schema failure".to_owned(),
                labels: vec![DiagnosticLabel {
                    start: 4,
                    len: 6,
                    message: None,
                }],
                help: None,
                spanned: true,
                source_kind: Some(SourceKind::ActionSchema),
            }),
            related: Vec::new(),
        };

        let published = project_frontend_outcome(3, documents, FrontendOutcome::Fatal(fatal));
        let diagnostic = &published.diagnostics[0];
        assert_eq!(diagnostic.range, zero_range());
        let related = diagnostic.related_information.as_ref().unwrap();
        assert_eq!(related[0].location.uri, schema_uri);
        assert_eq!(related[0].location.range, range(0, 4, 0, 10));
        assert_eq!(related[0].message, "schema failure");
    }

    #[test]
    fn spanless_dependency_findings_still_point_to_the_dependency_uri() {
        let policy_uri = Uri::from_str("file:///policy.dw").unwrap();
        let schema_uri = Uri::from_str("file:///actions.cedarschema").unwrap();
        let documents = BundleDocuments {
            policy: SourceDocument {
                uri: &policy_uri,
                text: "policy",
            },
            action_schema: SourceDocument {
                uri: &schema_uri,
                text: "schema",
            },
            event_schema: None,
            providers: None,
            macros: None,
        };
        let fatal = crate::frontend::FatalReport {
            diagnostic: Box::new(Finding {
                severity: Severity::Error,
                code: None,
                message: "spanless schema failure".to_owned(),
                labels: Vec::new(),
                help: None,
                spanned: false,
                source_kind: Some(SourceKind::ActionSchema),
            }),
            related: Vec::new(),
        };

        let published = project_frontend_outcome(3, documents, FrontendOutcome::Fatal(fatal));
        let related = published.diagnostics[0]
            .related_information
            .as_ref()
            .unwrap();
        assert_eq!(related[0].location.uri, schema_uri);
        assert_eq!(related[0].location.range, zero_range());
        assert_eq!(related[0].message, "spanless schema failure");
    }

    #[test]
    fn report_order_and_all_severity_mappings_are_stable() {
        let policy_uri = Uri::from_str("file:///policy.dw").unwrap();
        let schema_uri = Uri::from_str("file:///actions.cedarschema").unwrap();
        let documents = BundleDocuments {
            policy: SourceDocument {
                uri: &policy_uri,
                text: "policy",
            },
            action_schema: SourceDocument {
                uri: &schema_uri,
                text: "schema",
            },
            event_schema: None,
            providers: None,
            macros: None,
        };
        let finding = |severity, message: &str| Finding {
            severity,
            code: None,
            message: message.to_owned(),
            labels: Vec::new(),
            help: None,
            spanned: false,
            source_kind: Some(SourceKind::Policy),
        };
        let report = ValidationReport {
            passed: false,
            passed_without_warnings: false,
            errors: vec![
                finding(Severity::Error, "first"),
                finding(Severity::Advice, "second"),
            ],
            warnings: vec![finding(Severity::Warning, "third")],
        };

        let published = project_frontend_outcome(1, documents, FrontendOutcome::Report(report));
        assert_eq!(
            published
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.message.as_str())
                .collect::<Vec<_>>(),
            ["first", "second", "third"]
        );
        assert_eq!(
            published
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.severity)
                .collect::<Vec<_>>(),
            [
                Some(DiagnosticSeverity::ERROR),
                Some(DiagnosticSeverity::INFORMATION),
                Some(DiagnosticSeverity::WARNING)
            ]
        );
    }

    #[test]
    fn event_schema_projection_preserves_exact_primary_and_related_fields() {
        let schema_uri = Uri::from_str("file:///events.dwschema").unwrap();
        let source = "// 🚀\r\nschema field";
        let fatal = crate::frontend::FatalReport {
            diagnostic: Box::new(Finding {
                severity: Severity::Warning,
                code: Some("schema.code".to_owned()),
                message: "primary schema finding".to_owned(),
                labels: vec![
                    DiagnosticLabel {
                        start: 9,
                        len: 6,
                        message: Some("primary label".to_owned()),
                    },
                    DiagnosticLabel {
                        start: 16,
                        len: 5,
                        message: Some("related label".to_owned()),
                    },
                ],
                help: Some("upstream help remains outside LSP Diagnostic".to_owned()),
                spanned: true,
                source_kind: Some(SourceKind::EventSchema),
            }),
            related: vec![Finding {
                severity: Severity::Advice,
                code: None,
                message: "second schema finding".to_owned(),
                labels: Vec::new(),
                help: None,
                spanned: false,
                source_kind: Some(SourceKind::EventSchema),
            }],
        };

        let published = project_event_schema_outcome(
            12,
            SourceDocument {
                uri: &schema_uri,
                text: source,
            },
            FrontendOutcome::Fatal(fatal),
        );

        assert_eq!(published.uri, schema_uri);
        assert_eq!(published.version, Some(12));
        assert_eq!(published.diagnostics.len(), 2);
        assert_eq!(
            published.diagnostics[0],
            Diagnostic {
                range: range(1, 0, 1, 6),
                severity: Some(DiagnosticSeverity::WARNING),
                code: Some(NumberOrString::String("schema.code".to_owned())),
                code_description: None,
                source: Some(DIAGNOSTIC_SOURCE.to_owned()),
                message: "primary schema finding".to_owned(),
                related_information: Some(vec![DiagnosticRelatedInformation {
                    location: Location {
                        uri: schema_uri.clone(),
                        range: range(1, 7, 1, 12),
                    },
                    message: "related label".to_owned(),
                }]),
                tags: None,
                data: None,
            }
        );
        assert_eq!(
            published.diagnostics[1],
            Diagnostic {
                range: zero_range(),
                severity: Some(DiagnosticSeverity::INFORMATION),
                code: None,
                code_description: None,
                source: Some(DIAGNOSTIC_SOURCE.to_owned()),
                message: "second schema finding".to_owned(),
                related_information: None,
                tags: None,
                data: None,
            }
        );
    }

    #[test]
    fn authoritative_event_schema_parse_failure_is_exact_and_spanless() {
        let schema_uri = Uri::from_str("file:///events.dwschema").unwrap();
        let source = "// Truncated adaptation of login_attempt_custom_kind/event.dwschema.\n\
                      decision event <A>::attempt {\n\
                          ...inputs(A),\n\
                          actor: principalType(A),\n";
        let published = project_event_schema_outcome(
            4,
            SourceDocument {
                uri: &schema_uri,
                text: source,
            },
            crate::frontend::parse_event_schema(source),
        );

        assert_eq!(
            published,
            PublishDiagnosticsParams::new(
                schema_uri,
                vec![Diagnostic {
                    range: zero_range(),
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: None,
                    code_description: None,
                    source: Some(DIAGNOSTIC_SOURCE.to_owned()),
                    message: "event schema error: event schema parse error:  --> 5:1\n  |\n\
                              5 | \n  | ^---\n  |\n  = expected field"
                        .to_owned(),
                    related_information: None,
                    tags: None,
                    data: None,
                }],
                Some(4),
            )
        );
    }

    #[test]
    fn valid_and_operational_event_schema_outcomes_are_exact() {
        let schema_uri = Uri::from_str("file:///events.dwschema").unwrap();
        let document = SourceDocument {
            uri: &schema_uri,
            text: "event <A>::audit {}",
        };
        let valid = project_event_schema_outcome(
            1,
            document,
            crate::frontend::parse_event_schema(document.text),
        );
        assert_eq!(
            valid,
            PublishDiagnosticsParams::new(schema_uri.clone(), Vec::new(), Some(1))
        );

        let operational = project_event_schema_outcome(
            2,
            document,
            FrontendOutcome::OperationalLimit(OperationalLimitExceeded {
                source_kind: SourceKind::EventSchema,
                kind: OperationalLimitKind::SourceBytes,
                limit: 10,
                observed: 11,
            }),
        );
        assert_eq!(
            operational.diagnostics,
            vec![server_error_diagnostic(
                OPERATIONAL_LIMIT_DIAGNOSTIC_CODE,
                "Dogwood event schema input exceeds the source byte limit: observed 11, limit 10"
                    .to_owned(),
                None,
            )]
        );
    }
}
