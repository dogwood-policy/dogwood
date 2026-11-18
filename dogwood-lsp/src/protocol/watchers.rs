use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use lsp_server::{Request, RequestId};
use lsp_types::{
    DidChangeWatchedFilesRegistrationOptions, FileSystemWatcher, GlobPattern, OneOf, Registration,
    RegistrationParams, RelativePattern, Uri, WatchKind,
};

use super::DID_CHANGE_WATCHED_FILES;
use dogwood_lsp::project::{
    CONVENTIONAL_WATCH_PATTERNS, is_conventional_input_path, path_to_file_uri,
};

pub(super) const REGISTER_CAPABILITY: &str = "client/registerCapability";
const WATCH_REGISTRATION_ID: &str = "dogwood-lsp/watched-files";

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
enum WatchPattern {
    String(String),
    Relative { base_uri: String, pattern: String },
}

pub(super) fn registration_request(
    request_id: RequestId,
    workspace_roots: Vec<PathBuf>,
    explicit_dependencies: Vec<PathBuf>,
    relative_pattern_support: bool,
) -> Request {
    let options = DidChangeWatchedFilesRegistrationOptions {
        watchers: watched_file_watchers(
            workspace_roots,
            explicit_dependencies,
            relative_pattern_support,
        ),
    };
    Request::new(
        request_id,
        REGISTER_CAPABILITY.to_owned(),
        RegistrationParams {
            registrations: vec![Registration {
                id: WATCH_REGISTRATION_ID.to_owned(),
                method: DID_CHANGE_WATCHED_FILES.to_owned(),
                register_options: Some(
                    serde_json::to_value(options)
                        .expect("watched-file registration options should serialize"),
                ),
            }],
        },
    )
}

pub(super) fn watched_file_watchers(
    workspace_roots: Vec<PathBuf>,
    explicit_dependencies: Vec<PathBuf>,
    relative_pattern_support: bool,
) -> Vec<FileSystemWatcher> {
    let roots = minimal_workspace_roots(workspace_roots);
    let mut patterns = BTreeSet::new();
    for root in &roots {
        let root = glob_escape_path(root);
        let separator = if root.ends_with('/') { "" } else { "/" };
        for pattern in CONVENTIONAL_WATCH_PATTERNS {
            patterns.insert(WatchPattern::String(format!(
                "{root}{separator}**/{pattern}"
            )));
        }
    }
    for dependency in explicit_dependencies {
        let inside_workspace = roots.iter().any(|root| dependency.starts_with(root));
        let covered_by_conventional = is_conventional_input_path(&dependency) && inside_workspace;
        if covered_by_conventional {
            continue;
        }
        if inside_workspace {
            patterns.insert(WatchPattern::String(glob_escape_path(&dependency)));
        } else if relative_pattern_support
            && let Some(pattern) = external_relative_watch_pattern(&dependency)
        {
            patterns.insert(pattern);
        }
    }

    patterns
        .into_iter()
        .map(|pattern| FileSystemWatcher {
            glob_pattern: match pattern {
                WatchPattern::String(pattern) => GlobPattern::String(pattern),
                WatchPattern::Relative { base_uri, pattern } => {
                    GlobPattern::Relative(RelativePattern {
                        base_uri: OneOf::Right(
                            Uri::from_str(&base_uri)
                                .expect("generated watcher base URI should remain valid"),
                        ),
                        pattern,
                    })
                }
            },
            kind: Some(WatchKind::Create | WatchKind::Change | WatchKind::Delete),
        })
        .collect()
}

fn external_relative_watch_pattern(path: &Path) -> Option<WatchPattern> {
    let Some(parent) = path.parent() else {
        eprintln!(
            "cannot register external dependency without a parent: {}",
            path.display()
        );
        return None;
    };
    let Some(file_name) = path.file_name().and_then(|name| name.to_str()) else {
        eprintln!(
            "cannot register external dependency without a UTF-8 file name: {}",
            path.display()
        );
        return None;
    };
    let base_uri = match path_to_file_uri(parent) {
        Ok(uri) => uri,
        Err(error) => {
            eprintln!(
                "cannot register external dependency parent {}: {error}",
                parent.display()
            );
            return None;
        }
    };
    Some(WatchPattern::Relative {
        base_uri: base_uri.as_str().to_owned(),
        pattern: glob_escape_text(file_name),
    })
}

fn minimal_workspace_roots(mut roots: Vec<PathBuf>) -> Vec<PathBuf> {
    roots.sort_by(|left, right| {
        left.components()
            .count()
            .cmp(&right.components().count())
            .then_with(|| left.cmp(right))
    });
    roots.dedup();
    let mut minimal = Vec::<PathBuf>::new();
    for root in roots {
        if !minimal.iter().any(|ancestor| root.starts_with(ancestor)) {
            minimal.push(root);
        }
    }
    minimal
}

fn glob_escape_path(path: &Path) -> String {
    let path = path
        .to_str()
        .expect("workspace and configured paths originate from UTF-8 protocol values");
    glob_escape_text(path)
}

fn glob_escape_text(text: &str) -> String {
    let mut escaped = String::with_capacity(text.len());
    for character in text.chars() {
        if character == std::path::MAIN_SEPARATOR {
            escaped.push('/');
            continue;
        }
        match character {
            '*' => escaped.push_str("[*]"),
            '?' => escaped.push_str("[?]"),
            '[' => escaped.push_str("[[]"),
            ']' => escaped.push_str("[]]"),
            '{' => escaped.push_str("[{]"),
            '}' => escaped.push_str("[}]"),
            _ => escaped.push(character),
        }
    }
    escaped
}
