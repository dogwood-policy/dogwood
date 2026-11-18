//! Deterministic workspace and Dogwood bundle resolution.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::str::FromStr;

use lsp_types::{InitializeParams, Uri};
use serde::Deserialize;

use crate::frontend::SourceKind;

const MAX_DISCOVERY_ANCESTORS: usize = 256;

pub const ACTION_SCHEMA_FILE_NAME: &str = "actions.cedarschema";
pub const EVENT_SCHEMA_FILE_NAME: &str = "events.dwschema";
pub const PROVIDERS_FILE_NAME: &str = "providers.json";
pub const MACROS_FILE_NAME: &str = "macros.dw";
pub const CONVENTIONAL_OPTIONAL_INPUT_NAMES: [&str; 3] = [
    EVENT_SCHEMA_FILE_NAME,
    PROVIDERS_FILE_NAME,
    MACROS_FILE_NAME,
];
pub const CONVENTIONAL_WATCH_PATTERNS: [&str; 4] = [
    "*.cedarschema",
    EVENT_SCHEMA_FILE_NAME,
    PROVIDERS_FILE_NAME,
    MACROS_FILE_NAME,
];

pub fn is_action_schema_path(path: &Path) -> bool {
    path.extension() == Some(OsStr::new("cedarschema"))
}

pub fn is_conventional_input_path(path: &Path) -> bool {
    is_action_schema_path(path)
        || path
            .file_name()
            .and_then(OsStr::to_str)
            .is_some_and(|name| CONVENTIONAL_OPTIONAL_INPUT_NAMES.contains(&name))
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedBundlePaths {
    pub workspace_root: PathBuf,
    pub action_schema: PathBuf,
    pub event_schema: Option<PathBuf>,
    pub providers: Option<PathBuf>,
    pub macros: Option<PathBuf>,
}

impl ResolvedBundlePaths {
    pub fn dependencies(&self) -> Vec<(SourceKind, PathBuf)> {
        let mut dependencies = vec![(SourceKind::ActionSchema, self.action_schema.clone())];
        dependencies.extend(
            self.event_schema
                .iter()
                .cloned()
                .map(|path| (SourceKind::EventSchema, path)),
        );
        dependencies.extend(
            self.providers
                .iter()
                .cloned()
                .map(|path| (SourceKind::Providers, path)),
        );
        dependencies.extend(
            self.macros
                .iter()
                .cloned()
                .map(|path| (SourceKind::Macros, path)),
        );
        dependencies
    }

    pub fn bundle_directory(&self) -> &Path {
        self.action_schema
            .parent()
            .expect("resolved action schema always has a parent")
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectFailure {
    pub message: String,
    pub related_path: Option<PathBuf>,
    pub dependencies: Vec<(SourceKind, PathBuf)>,
}

impl ProjectFailure {
    fn configuration(message: impl Into<String>) -> Self {
        Self {
            message: format!("Dogwood project configuration error: {}", message.into()),
            related_path: None,
            dependencies: Vec::new(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct ProjectResolver {
    workspaces: Vec<Workspace>,
    configuration_failure: Option<ProjectFailure>,
}

#[derive(Clone, Debug)]
struct Workspace {
    uri: Uri,
    root: PathBuf,
    explicit: Option<ExplicitBundle>,
}

#[derive(Clone, Debug)]
struct ExplicitBundle {
    action_schema: String,
    event_schema: Option<String>,
    providers: Option<String>,
    macros: Option<String>,
}

#[derive(Debug, Default, Deserialize)]
#[serde(default, deny_unknown_fields)]
struct InitializationOptions {
    bundles: Vec<BundleOptions>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct BundleOptions {
    workspace_folder: Uri,
    action_schema: String,
    event_schema: Option<String>,
    providers: Option<String>,
    macros: Option<String>,
}

impl ProjectResolver {
    #[allow(
        deprecated,
        reason = "rootUri is the required single-workspace fallback"
    )]
    pub fn from_initialize(params: &InitializeParams) -> Self {
        let mut failure = None;
        let folder_uris: Vec<Uri> = match params.workspace_folders.as_ref() {
            Some(folders) if !folders.is_empty() => {
                folders.iter().map(|folder| folder.uri.clone()).collect()
            }
            _ => params.root_uri.iter().cloned().collect(),
        };

        let mut workspaces = Vec::new();
        let mut roots = BTreeSet::new();
        for uri in folder_uris {
            match file_uri_to_path(&uri) {
                Ok(root) if roots.insert(root.clone()) => workspaces.push(Workspace {
                    uri,
                    root,
                    explicit: None,
                }),
                Ok(_) => set_first_failure(
                    &mut failure,
                    ProjectFailure::configuration(
                        "workspace folder URIs must resolve to distinct paths",
                    ),
                ),
                Err(error) => set_first_failure(
                    &mut failure,
                    ProjectFailure::configuration(format!(
                        "workspace folder URI `{}` is invalid: {error}",
                        uri.as_str()
                    )),
                ),
            }
        }

        let options = match params.initialization_options.clone() {
            None | Some(serde_json::Value::Null) => InitializationOptions::default(),
            Some(value) => match serde_json::from_value(value) {
                Ok(options) => options,
                Err(error) => {
                    set_first_failure(
                        &mut failure,
                        ProjectFailure::configuration(format!(
                            "initializationOptions must match the documented `bundles` shape: \
                             {error}"
                        )),
                    );
                    InitializationOptions::default()
                }
            },
        };

        let mut explicit_by_root = BTreeMap::new();
        for bundle in options.bundles {
            let root = match file_uri_to_path(&bundle.workspace_folder) {
                Ok(root) => root,
                Err(error) => {
                    set_first_failure(
                        &mut failure,
                        ProjectFailure::configuration(format!(
                            "bundle workspaceFolder `{}` is invalid: {error}",
                            bundle.workspace_folder.as_str()
                        )),
                    );
                    continue;
                }
            };
            if !roots.contains(&root) {
                set_first_failure(
                    &mut failure,
                    ProjectFailure::configuration(format!(
                        "bundle workspaceFolder `{}` is not a configured workspace folder",
                        bundle.workspace_folder.as_str()
                    )),
                );
                continue;
            }
            let explicit = ExplicitBundle {
                action_schema: bundle.action_schema,
                event_schema: bundle.event_schema,
                providers: bundle.providers,
                macros: bundle.macros,
            };
            if explicit_by_root.insert(root, explicit).is_some() {
                set_first_failure(
                    &mut failure,
                    ProjectFailure::configuration(
                        "at most one bundle entry is allowed per workspace folder",
                    ),
                );
            }
        }

        for workspace in &mut workspaces {
            workspace.explicit = explicit_by_root.remove(&workspace.root);
        }
        workspaces.sort_by(|left, right| {
            right
                .root
                .components()
                .count()
                .cmp(&left.root.components().count())
                .then_with(|| left.root.cmp(&right.root))
        });

        Self {
            workspaces,
            configuration_failure: failure,
        }
    }

    pub fn resolve(
        &self,
        policy_path: &Path,
        exists: impl FnMut(&Path) -> bool,
    ) -> Result<ResolvedBundlePaths, ProjectFailure> {
        self.resolve_with_schema_candidates(policy_path, exists, std::iter::empty())
    }

    pub fn resolve_with_schema_candidates(
        &self,
        policy_path: &Path,
        mut exists: impl FnMut(&Path) -> bool,
        schema_candidates: impl IntoIterator<Item = PathBuf>,
    ) -> Result<ResolvedBundlePaths, ProjectFailure> {
        if let Some(failure) = &self.configuration_failure {
            return Err(failure.clone());
        }
        let workspace = self.workspace_for(policy_path).ok_or_else(|| {
            ProjectFailure::configuration("policy is outside every configured workspace folder")
        })?;

        if let Some(explicit) = &workspace.explicit {
            return resolve_explicit(workspace, explicit);
        }

        let schema_candidates = schema_candidates
            .into_iter()
            .filter(|path| is_action_schema_path(path))
            .collect();
        discover_bundle(workspace, policy_path, &mut exists, &schema_candidates)
    }

    pub fn discovery_root_for(&self, policy_path: &Path) -> Option<&Path> {
        if self.configuration_failure.is_some() {
            return None;
        }
        self.workspace_for(policy_path)
            .filter(|workspace| workspace.explicit.is_none())
            .map(|workspace| workspace.root.as_path())
    }

    pub fn is_explicit_dependency_path(&self, path: &Path) -> bool {
        self.explicit_dependency_paths()
            .into_iter()
            .any(|dependency| dependency == path)
    }

    pub fn workspace_roots(&self) -> Vec<PathBuf> {
        self.workspaces
            .iter()
            .map(|workspace| workspace.root.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    pub fn explicit_dependency_paths(&self) -> Vec<PathBuf> {
        if self.configuration_failure.is_some() {
            return Vec::new();
        }
        self.workspaces
            .iter()
            .filter_map(|workspace| {
                workspace
                    .explicit
                    .as_ref()
                    .and_then(|explicit| resolve_explicit(workspace, explicit).ok())
            })
            .flat_map(|bundle| bundle.dependencies().into_iter().map(|(_, path)| path))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    pub fn external_dependency_paths(&self, bundle: &ResolvedBundlePaths) -> Vec<PathBuf> {
        bundle
            .dependencies()
            .into_iter()
            .map(|(_, path)| path)
            .filter(|path| self.is_external_dependency_path(path))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    pub fn is_external_dependency_path(&self, path: &Path) -> bool {
        !self
            .workspaces
            .iter()
            .any(|workspace| path.starts_with(&workspace.root))
    }

    fn workspace_for(&self, policy_path: &Path) -> Option<&Workspace> {
        self.workspaces
            .iter()
            .find(|workspace| policy_path.starts_with(&workspace.root))
    }
}

fn resolve_explicit(
    workspace: &Workspace,
    explicit: &ExplicitBundle,
) -> Result<ResolvedBundlePaths, ProjectFailure> {
    let action_schema =
        resolve_explicit_path(workspace, &explicit.action_schema, SourceKind::ActionSchema)?;
    let event_schema = explicit
        .event_schema
        .as_deref()
        .map(|path| resolve_explicit_path(workspace, path, SourceKind::EventSchema))
        .transpose()?;
    let providers = explicit
        .providers
        .as_deref()
        .map(|path| resolve_explicit_path(workspace, path, SourceKind::Providers))
        .transpose()?;
    let macros = explicit
        .macros
        .as_deref()
        .map(|path| resolve_explicit_path(workspace, path, SourceKind::Macros))
        .transpose()?;

    Ok(ResolvedBundlePaths {
        workspace_root: workspace.root.clone(),
        action_schema,
        event_schema,
        providers,
        macros,
    })
}

fn resolve_explicit_path(
    workspace: &Workspace,
    configured: &str,
    source_kind: SourceKind,
) -> Result<PathBuf, ProjectFailure> {
    let candidate = configured_path(&workspace.root, configured).map_err(|message| {
        ProjectFailure::configuration(format!(
            "invalid {} path `{configured}` for workspace `{}`: {message}",
            source_kind.as_str(),
            workspace.uri.as_str()
        ))
    })?;

    if !Path::new(configured).is_absolute() {
        ensure_relative_path_is_contained(&workspace.root, &candidate).map_err(|message| {
            ProjectFailure {
                message: format!(
                    "Dogwood project configuration error: {} path `{configured}` escapes or \
                     cannot be resolved within workspace `{}`: {message}",
                    source_kind.as_str(),
                    workspace.uri.as_str()
                ),
                related_path: Some(candidate.clone()),
                dependencies: vec![(source_kind, candidate.clone())],
            }
        })?;
    }
    ensure_explicit_path_has_no_alias(&candidate).map_err(|message| ProjectFailure {
        message: format!(
            "Dogwood project configuration error: {} path `{configured}` for workspace `{}` \
             cannot be used: {message}",
            source_kind.as_str(),
            workspace.uri.as_str()
        ),
        related_path: Some(candidate.clone()),
        dependencies: vec![(source_kind, candidate.clone())],
    })?;
    Ok(candidate)
}

fn configured_path(root: &Path, configured: &str) -> Result<PathBuf, String> {
    if configured.is_empty() {
        return Err("path must not be empty".to_owned());
    }
    if configured.as_bytes().contains(&0) {
        return Err("path must not contain NUL".to_owned());
    }

    let path = Path::new(configured);
    if path.is_absolute() {
        normalize_absolute(path)
    } else {
        normalize_absolute(&root.join(path))
    }
}

fn ensure_relative_path_is_contained(root: &Path, candidate: &Path) -> Result<(), String> {
    if !candidate.starts_with(root) {
        return Err("path escapes the workspace after lexical normalization".to_owned());
    }
    let canonical_root =
        fs::canonicalize(root).map_err(|_| "workspace root cannot be canonicalized".to_owned())?;
    let mut probe = candidate;

    for _ in 0..=MAX_DISCOVERY_ANCESTORS {
        match fs::canonicalize(probe) {
            Ok(canonical_probe) => {
                return if canonical_probe.starts_with(&canonical_root) {
                    Ok(())
                } else {
                    Err("a symlink resolves outside the workspace".to_owned())
                };
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                probe = probe
                    .parent()
                    .ok_or_else(|| "no existing ancestor can be canonicalized".to_owned())?;
            }
            Err(_) => return Err("path cannot be canonicalized".to_owned()),
        }
    }
    Err("path ancestor depth exceeds the 256-component limit".to_owned())
}

fn ensure_explicit_path_has_no_alias(candidate: &Path) -> Result<(), String> {
    let mut probe = candidate;
    for _ in 0..=MAX_DISCOVERY_ANCESTORS {
        match fs::canonicalize(probe) {
            Ok(canonical) if canonical == probe => return Ok(()),
            Ok(_) => {
                return Err(
                    "an existing path component resolves through a symlink alias".to_owned(),
                );
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                probe = probe.parent().ok_or_else(|| {
                    "no existing ancestor can be checked for symlink aliases".to_owned()
                })?;
            }
            Err(_) => {
                return Err(
                    "an existing path component cannot be canonicalized to exclude a symlink alias"
                        .to_owned(),
                );
            }
        }
    }
    Err("path ancestor depth exceeds the 256-component limit".to_owned())
}

fn discover_bundle(
    workspace: &Workspace,
    policy_path: &Path,
    exists: &mut impl FnMut(&Path) -> bool,
    additional_schema_candidates: &BTreeSet<PathBuf>,
) -> Result<ResolvedBundlePaths, ProjectFailure> {
    let Some(mut directory) = policy_path.parent() else {
        return Err(ProjectFailure::configuration(
            "policy path has no containing directory",
        ));
    };
    let mut candidates = Vec::new();

    for _ in 0..=MAX_DISCOVERY_ANCESTORS {
        if !directory.starts_with(&workspace.root) {
            break;
        }
        let action_schema = directory.join(ACTION_SCHEMA_FILE_NAME);
        candidates.push((SourceKind::ActionSchema, action_schema.clone()));
        if action_schema_candidate_is_file(
            &action_schema,
            exists,
            additional_schema_candidates.contains(&action_schema),
        ) {
            ensure_conventional_path_is_contained(
                workspace,
                SourceKind::ActionSchema,
                &action_schema,
                &candidates,
            )?;
            return resolve_conventional_bundle(
                workspace,
                directory,
                action_schema,
                candidates,
                exists,
            );
        }

        let discovered = discover_action_schema_candidates(
            directory,
            &action_schema,
            exists,
            additional_schema_candidates,
        );
        if discovered.len() > 1 {
            let dependencies = candidates
                .iter()
                .cloned()
                .chain(
                    discovered
                        .iter()
                        .cloned()
                        .map(|path| (SourceKind::ActionSchema, path)),
                )
                .collect();
            let names = discovered
                .iter()
                .map(|path| {
                    path.file_name()
                        .unwrap_or(path.as_os_str())
                        .to_string_lossy()
                })
                .collect::<Vec<_>>()
                .join(", ");
            return Err(ProjectFailure {
                message: format!(
                    "Dogwood project configuration error: multiple `.cedarschema` action schemas \
                     were found in `{}` ({names}); name the intended schema \
                     `{ACTION_SCHEMA_FILE_NAME}` or configure the bundle explicitly",
                    directory.display()
                ),
                related_path: discovered.first().cloned(),
                dependencies,
            });
        }
        if let Some(action_schema) = discovered.first().cloned() {
            candidates.push((SourceKind::ActionSchema, action_schema.clone()));
            ensure_conventional_path_is_contained(
                workspace,
                SourceKind::ActionSchema,
                &action_schema,
                &candidates,
            )?;
            return resolve_conventional_bundle(
                workspace,
                directory,
                action_schema,
                candidates,
                exists,
            );
        }
        if directory == workspace.root {
            break;
        }
        directory = directory.parent().ok_or_else(|| {
            ProjectFailure::configuration("workspace ancestor walk ended unexpectedly")
        })?;
    }

    let related_path = candidates.first().map(|(_, path)| path.clone());
    Err(ProjectFailure {
        message: "Dogwood project configuration error: no `.cedarschema` action schema was found \
                  from the policy directory through its workspace root"
            .to_owned(),
        related_path,
        dependencies: candidates,
    })
}

fn discover_action_schema_candidates(
    directory: &Path,
    preferred: &Path,
    exists: &mut impl FnMut(&Path) -> bool,
    additional: &BTreeSet<PathBuf>,
) -> BTreeSet<PathBuf> {
    let mut candidates: BTreeSet<_> = additional
        .iter()
        .filter(|path| path.parent() == Some(directory) && path.as_path() != preferred)
        .cloned()
        .collect();
    if let Ok(entries) = fs::read_dir(directory) {
        candidates.extend(
            entries
                .filter_map(Result::ok)
                .map(|entry| entry.path())
                .filter(|path| path != preferred && is_action_schema_path(path)),
        );
    }
    candidates
        .retain(|path| action_schema_candidate_is_file(path, exists, additional.contains(path)));
    candidates
}

fn action_schema_candidate_is_file(
    path: &Path,
    exists: &mut impl FnMut(&Path) -> bool,
    open_document: bool,
) -> bool {
    if !exists(path) {
        return false;
    }
    if open_document {
        return true;
    }
    match fs::metadata(path) {
        Ok(metadata) => metadata.is_file(),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            match fs::symlink_metadata(path) {
                Ok(metadata) => metadata.file_type().is_symlink(),
                Err(error) => error.kind() != std::io::ErrorKind::NotFound,
            }
        }
        Err(_) => true,
    }
}

fn resolve_conventional_bundle(
    workspace: &Workspace,
    directory: &Path,
    action_schema: PathBuf,
    mut dependencies: Vec<(SourceKind, PathBuf)>,
    exists: &mut impl FnMut(&Path) -> bool,
) -> Result<ResolvedBundlePaths, ProjectFailure> {
    let event_schema = resolve_conventional_optional(
        workspace,
        directory,
        EVENT_SCHEMA_FILE_NAME,
        SourceKind::EventSchema,
        exists,
        &mut dependencies,
    )?;
    let providers = resolve_conventional_optional(
        workspace,
        directory,
        PROVIDERS_FILE_NAME,
        SourceKind::Providers,
        exists,
        &mut dependencies,
    )?;
    let macros = resolve_conventional_optional(
        workspace,
        directory,
        MACROS_FILE_NAME,
        SourceKind::Macros,
        exists,
        &mut dependencies,
    )?;
    Ok(ResolvedBundlePaths {
        workspace_root: workspace.root.clone(),
        action_schema,
        event_schema,
        providers,
        macros,
    })
}

fn resolve_conventional_optional(
    workspace: &Workspace,
    directory: &Path,
    name: &str,
    source_kind: SourceKind,
    exists: &mut impl FnMut(&Path) -> bool,
    dependencies: &mut Vec<(SourceKind, PathBuf)>,
) -> Result<Option<PathBuf>, ProjectFailure> {
    let path = directory.join(name);
    if !exists(&path) {
        return Ok(None);
    }
    dependencies.push((source_kind, path.clone()));
    ensure_conventional_path_is_contained(workspace, source_kind, &path, dependencies)?;
    Ok(Some(path))
}

fn ensure_conventional_path_is_contained(
    workspace: &Workspace,
    source_kind: SourceKind,
    path: &Path,
    dependencies: &[(SourceKind, PathBuf)],
) -> Result<(), ProjectFailure> {
    ensure_relative_path_is_contained(&workspace.root, path).map_err(|message| ProjectFailure {
        message: format!(
            "Dogwood project configuration error: conventionally discovered {} `{}` escapes or \
             cannot be resolved within workspace `{}`: {message}",
            source_kind.as_str(),
            path.display(),
            workspace.uri.as_str()
        ),
        related_path: Some(path.to_path_buf()),
        dependencies: dependencies.to_vec(),
    })
}

fn set_first_failure(slot: &mut Option<ProjectFailure>, failure: ProjectFailure) {
    if slot.is_none() {
        *slot = Some(failure);
    }
}

pub fn file_uri_to_path(uri: &Uri) -> Result<PathBuf, String> {
    if !uri
        .scheme()
        .is_some_and(|scheme| scheme.eq_lowercase("file"))
    {
        return Err("URI scheme must be `file`".to_owned());
    }
    if uri.authority().is_some_and(|authority| {
        !authority.as_str().is_empty() && !authority.as_str().eq_ignore_ascii_case("localhost")
    }) {
        return Err("file URI authority must be empty or `localhost`".to_owned());
    }
    if uri.query().is_some() || uri.fragment().is_some() {
        return Err("file URI must not contain a query or fragment".to_owned());
    }

    let decoded = uri
        .path()
        .as_estr()
        .decode()
        .into_string()
        .map_err(|_| "file URI path is not valid UTF-8".to_owned())?;
    if decoded.as_bytes().contains(&0) {
        return Err("file URI path must not contain NUL".to_owned());
    }
    let path = Path::new(decoded.as_ref());
    if !path.is_absolute() {
        return Err("file URI path must be absolute".to_owned());
    }
    normalize_absolute(path)
}

pub fn path_to_file_uri(path: &Path) -> Result<Uri, String> {
    let path = normalize_absolute(path)?;
    let source = path
        .to_str()
        .ok_or_else(|| "filesystem path is not valid UTF-8".to_owned())?;
    let mut encoded = String::with_capacity(source.len());
    for byte in source.bytes() {
        if byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'.' | b'_' | b'~' | b'/' | b':') {
            encoded.push(char::from(byte));
        } else {
            use std::fmt::Write as _;
            write!(&mut encoded, "%{byte:02X}").expect("writing to a String cannot fail");
        }
    }
    Uri::from_str(&format!("file://{encoded}"))
        .map_err(|error| format!("cannot construct file URI: {error}"))
}

fn normalize_absolute(path: &Path) -> Result<PathBuf, String> {
    if !path.is_absolute() {
        return Err("path must be absolute".to_owned());
    }
    let mut prefix = None;
    let mut rooted = false;
    let mut components = Vec::new();

    for component in path.components() {
        match component {
            Component::Prefix(value) => prefix = Some(value.as_os_str().to_owned()),
            Component::RootDir => rooted = true,
            Component::CurDir => {}
            Component::ParentDir => {
                if components.pop().is_none() {
                    return Err("path traverses above its filesystem root".to_owned());
                }
            }
            Component::Normal(value) => components.push(value.to_owned()),
        }
    }

    let mut normalized = PathBuf::new();
    if let Some(prefix) = prefix {
        normalized.push(prefix);
    }
    if rooted {
        normalized.push(Path::new(std::path::MAIN_SEPARATOR_STR));
    }
    for component in components {
        normalized.push(component);
    }
    Ok(normalized)
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::str::FromStr;
    use std::sync::atomic::{AtomicU64, Ordering};

    use lsp_types::InitializeParams;
    use serde_json::json;

    use super::*;

    static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);

    fn params(value: serde_json::Value) -> InitializeParams {
        serde_json::from_value(value).expect("initialize params should deserialize")
    }

    fn temp_root() -> PathBuf {
        let root = std::env::temp_dir().join(format!(
            "dogwood-lsp-project-{}-{}",
            std::process::id(),
            TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&root).expect("temporary workspace should be created");
        root
    }

    #[test]
    fn file_uri_round_trip_handles_spaces_and_unicode() {
        let path = Path::new("/tmp/dogwood space/\u{1f600}.dw");
        let uri = path_to_file_uri(path).expect("path should convert");

        assert_eq!(uri.as_str(), "file:///tmp/dogwood%20space/%F0%9F%98%80.dw");
        assert_eq!(file_uri_to_path(&uri), Ok(path.to_path_buf()));
    }

    #[test]
    fn non_file_and_ambiguous_file_uris_are_rejected() {
        for source in [
            "https://example.com/policy.dw",
            "file://server/share/policy.dw",
            "file:///policy.dw?query",
            "file:relative.dw",
        ] {
            let uri = Uri::from_str(source).expect("URI syntax should be valid");
            assert!(file_uri_to_path(&uri).is_err(), "{source}");
        }
    }

    #[test]
    fn deepest_workspace_and_nearest_schema_win() {
        let root = temp_root();
        let nested = root.join("nested");
        let policy_dir = nested.join("policies/deeper");
        fs::create_dir_all(&policy_dir).unwrap();
        fs::write(root.join("actions.cedarschema"), "").unwrap();
        fs::write(nested.join("actions.cedarschema"), "").unwrap();
        fs::write(nested.join("events.dwschema"), "").unwrap();
        let root_uri = path_to_file_uri(&root).unwrap();
        let nested_uri = path_to_file_uri(&nested).unwrap();
        let resolver = ProjectResolver::from_initialize(&params(json!({
            "capabilities": {},
            "workspaceFolders": [
                {"uri": root_uri, "name": "root"},
                {"uri": nested_uri, "name": "nested"}
            ]
        })));

        let resolved = resolver
            .resolve(&policy_dir.join("policy.dw"), Path::exists)
            .unwrap();
        assert_eq!(resolved.workspace_root, nested);
        assert_eq!(
            resolved.action_schema,
            resolved.workspace_root.join("actions.cedarschema")
        );
        assert_eq!(
            resolved.event_schema,
            Some(resolved.workspace_root.join("events.dwschema"))
        );

        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn conventional_discovery_accepts_arbitrary_schema_names_deterministically() {
        let root = temp_root();
        let policy_dir = root.join("nested/policies");
        fs::create_dir_all(&policy_dir).unwrap();
        let root_schema = root.join("root.cedarschema");
        let nearest_schema = root.join("nested/schema.cedarschema");
        fs::write(&root_schema, "").unwrap();
        fs::write(&nearest_schema, "").unwrap();
        let root_uri = path_to_file_uri(&root).unwrap();
        let resolver = ProjectResolver::from_initialize(&params(json!({
            "capabilities": {},
            "rootUri": root_uri
        })));
        let policy = policy_dir.join("policy.dw");

        let resolved = resolver.resolve(&policy, Path::exists).unwrap();
        assert_eq!(resolved.action_schema, nearest_schema);

        let second = root.join("nested/other.cedarschema");
        fs::write(&second, "").unwrap();
        let failure = resolver.resolve(&policy, Path::exists).unwrap_err();
        assert!(failure.message.contains("multiple `.cedarschema`"));
        assert!(failure.message.contains("other.cedarschema"));
        assert!(failure.message.contains("schema.cedarschema"));

        let preferred = root.join("nested/actions.cedarschema");
        fs::write(&preferred, "").unwrap();
        let resolved = resolver.resolve(&policy, Path::exists).unwrap();
        assert_eq!(resolved.action_schema, preferred);

        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn conventional_discovery_includes_open_unsaved_schema_candidates() {
        let root = temp_root();
        let root_uri = path_to_file_uri(&root).unwrap();
        let resolver = ProjectResolver::from_initialize(&params(json!({
            "capabilities": {},
            "rootUri": root_uri
        })));
        let schema = root.join("schema.cedarschema");

        let resolved = resolver
            .resolve_with_schema_candidates(
                &root.join("policy.dw"),
                |path| path == schema,
                [schema.clone()],
            )
            .unwrap();
        assert_eq!(resolved.action_schema, schema);

        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn conventional_discovery_ignores_schema_named_directories() {
        let root = temp_root();
        let policy_dir = root.join("nested");
        fs::create_dir_all(policy_dir.join("schema.cedarschema")).unwrap();
        fs::create_dir_all(policy_dir.join("actions.cedarschema")).unwrap();
        let schema = root.join("schema.cedarschema");
        fs::write(&schema, "").unwrap();
        let root_uri = path_to_file_uri(&root).unwrap();
        let resolver = ProjectResolver::from_initialize(&params(json!({
            "capabilities": {},
            "rootUri": root_uri
        })));

        let resolved = resolver
            .resolve(&policy_dir.join("policy.dw"), Path::exists)
            .unwrap();
        assert_eq!(resolved.action_schema, schema);

        fs::remove_dir_all(root).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn conventional_discovery_preserves_dangling_schema_candidates() {
        use std::os::unix::fs::symlink;

        let root = temp_root();
        let policy_dir = root.join("nested");
        fs::create_dir_all(&policy_dir).unwrap();
        fs::write(root.join("schema.cedarschema"), "").unwrap();
        let dangling = policy_dir.join("broken.cedarschema");
        symlink(policy_dir.join("missing"), &dangling).unwrap();
        let root_uri = path_to_file_uri(&root).unwrap();
        let resolver = ProjectResolver::from_initialize(&params(json!({
            "capabilities": {},
            "rootUri": root_uri
        })));

        let resolved = resolver
            .resolve(&policy_dir.join("policy.dw"), |path| {
                fs::symlink_metadata(path).is_ok()
            })
            .unwrap();
        assert_eq!(resolved.action_schema, dangling);

        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn explicit_config_precedes_discovery_and_rejects_duplicates() {
        let root = temp_root();
        fs::create_dir_all(root.join("config")).unwrap();
        let root_uri = path_to_file_uri(&root).unwrap();
        let resolver = ProjectResolver::from_initialize(&params(json!({
            "capabilities": {},
            "rootUri": root_uri,
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": root_uri,
                    "actionSchema": "config/schema.cedarschema",
                    "eventSchema": "config/events.dwschema"
                }]
            }
        })));
        let resolved = resolver
            .resolve(&root.join("policy.dw"), |_| false)
            .unwrap();
        assert_eq!(
            resolved.action_schema,
            root.join("config/schema.cedarschema")
        );
        assert_eq!(
            resolved.event_schema,
            Some(root.join("config/events.dwschema"))
        );

        let duplicate = ProjectResolver::from_initialize(&params(json!({
            "capabilities": {},
            "rootUri": root_uri,
            "initializationOptions": {
                "bundles": [
                    {"workspaceFolder": root_uri, "actionSchema": "one"},
                    {"workspaceFolder": root_uri, "actionSchema": "two"}
                ]
            }
        })));
        assert!(
            duplicate
                .resolve(&root.join("policy.dw"), |_| false)
                .unwrap_err()
                .message
                .contains("at most one bundle entry")
        );
        assert!(!duplicate.is_explicit_dependency_path(&root.join("one")));

        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn explicit_dependency_query_accepts_only_resolved_configured_paths() {
        let root = temp_root();
        let root_uri = path_to_file_uri(&root).unwrap();
        let resolver = ProjectResolver::from_initialize(&params(json!({
            "capabilities": {},
            "rootUri": root_uri,
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": root_uri,
                    "actionSchema": "schema.txt",
                    "eventSchema": "config/events.input",
                    "providers": "providers.input",
                    "macros": "macros.input"
                }]
            }
        })));

        for relative in [
            "schema.txt",
            "config/events.input",
            "providers.input",
            "macros.input",
        ] {
            assert!(
                resolver.is_explicit_dependency_path(&root.join(relative)),
                "{relative} should be recognized as an explicit dependency"
            );
        }
        assert!(!resolver.is_explicit_dependency_path(&root.join("unconfigured.txt")));
        assert_eq!(resolver.workspace_roots(), vec![root.clone()]);
        assert_eq!(
            resolver.explicit_dependency_paths(),
            vec![
                root.join("config/events.input"),
                root.join("macros.input"),
                root.join("providers.input"),
                root.join("schema.txt"),
            ]
        );
        assert!(!resolver.is_external_dependency_path(&root.join("schema.txt")));
        assert!(resolver.is_external_dependency_path(&root.with_extension("outside")));

        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn policy_outside_configured_workspace_is_rejected() {
        let root = temp_root();
        let outside = temp_root();
        let root_uri = path_to_file_uri(&root).unwrap();
        let resolver = ProjectResolver::from_initialize(&params(json!({
            "capabilities": {},
            "rootUri": root_uri
        })));

        let failure = resolver
            .resolve(&outside.join("policy.dw"), |_| false)
            .unwrap_err();
        assert!(
            failure
                .message
                .contains("outside every configured workspace")
        );

        fs::remove_dir_all(root).unwrap();
        fs::remove_dir_all(outside).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn explicit_relative_symlink_escape_is_rejected() {
        use std::os::unix::fs::symlink;

        let root = temp_root();
        let outside = temp_root();
        symlink(&outside, root.join("escape")).unwrap();
        let root_uri = path_to_file_uri(&root).unwrap();
        let resolver = ProjectResolver::from_initialize(&params(json!({
            "capabilities": {},
            "rootUri": root_uri,
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": root_uri,
                    "actionSchema": "escape/actions.cedarschema"
                }]
            }
        })));

        assert!(
            resolver
                .resolve(&root.join("policy.dw"), |_| false)
                .unwrap_err()
                .message
                .contains("symlink resolves outside")
        );

        fs::remove_file(root.join("escape")).unwrap();
        fs::remove_dir_all(root).unwrap();
        fs::remove_dir_all(outside).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn explicit_absolute_file_and_parent_symlink_aliases_are_rejected() {
        use std::os::unix::fs::symlink;

        let root = temp_root();
        let outside = temp_root();
        let target = outside.join("schema.txt");
        fs::write(&target, "").unwrap();
        let root_uri = path_to_file_uri(&root).unwrap();

        let file_alias = root.join("schema.txt");
        symlink(&target, &file_alias).unwrap();
        let resolver = ProjectResolver::from_initialize(&params(json!({
            "capabilities": {},
            "rootUri": root_uri,
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": root_uri,
                    "actionSchema": file_alias.to_string_lossy()
                }]
            }
        })));
        let failure = resolver
            .resolve(&root.join("policy.dw"), |_| false)
            .unwrap_err();
        assert!(failure.message.contains("symlink alias"));
        assert_eq!(failure.related_path.as_deref(), Some(file_alias.as_path()));
        fs::remove_file(&file_alias).unwrap();

        let parent_alias = root.join("external-parent");
        symlink(&outside, &parent_alias).unwrap();
        let configured = parent_alias.join("schema.txt");
        let resolver = ProjectResolver::from_initialize(&params(json!({
            "capabilities": {},
            "rootUri": root_uri,
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": root_uri,
                    "actionSchema": configured.to_string_lossy()
                }]
            }
        })));
        let failure = resolver
            .resolve(&root.join("policy.dw"), |_| false)
            .unwrap_err();
        assert!(failure.message.contains("symlink alias"));
        assert_eq!(failure.related_path.as_deref(), Some(configured.as_path()));
        fs::remove_file(parent_alias).unwrap();

        fs::remove_dir_all(root).unwrap();
        fs::remove_dir_all(outside).unwrap();
    }

    #[test]
    fn nonexistent_explicit_absolute_path_remains_resolvable() {
        let root = temp_root();
        let outside = temp_root();
        let missing = outside.join("future/schema.txt");
        let root_uri = path_to_file_uri(&root).unwrap();
        let resolver = ProjectResolver::from_initialize(&params(json!({
            "capabilities": {},
            "rootUri": root_uri,
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": root_uri,
                    "actionSchema": missing.to_string_lossy()
                }]
            }
        })));

        let resolved = resolver
            .resolve(&root.join("policy.dw"), |_| false)
            .unwrap();
        assert_eq!(resolved.action_schema, missing);

        fs::remove_dir_all(root).unwrap();
        fs::remove_dir_all(outside).unwrap();
    }

    #[test]
    fn explicit_relative_parent_components_are_normalized_within_workspace() {
        let root = temp_root();
        let root_uri = path_to_file_uri(&root).unwrap();
        let resolver = ProjectResolver::from_initialize(&params(json!({
            "capabilities": {},
            "rootUri": root_uri,
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": root_uri,
                    "actionSchema": "config/../actions.cedarschema"
                }]
            }
        })));

        let resolved = resolver
            .resolve(&root.join("policy.dw"), |_| false)
            .expect("a normalized path inside the workspace should resolve");
        assert_eq!(resolved.action_schema, root.join("actions.cedarschema"));

        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn explicit_relative_parent_components_cannot_escape_workspace() {
        let root = temp_root();
        let root_uri = path_to_file_uri(&root).unwrap();
        let resolver = ProjectResolver::from_initialize(&params(json!({
            "capabilities": {},
            "rootUri": root_uri,
            "initializationOptions": {
                "bundles": [{
                    "workspaceFolder": root_uri,
                    "actionSchema": "../actions.cedarschema"
                }]
            }
        })));

        assert!(
            resolver
                .resolve(&root.join("policy.dw"), |_| false)
                .unwrap_err()
                .message
                .contains("escapes")
        );

        fs::remove_dir_all(root).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn conventional_symlink_escapes_are_rejected_for_required_and_optional_inputs() {
        use std::os::unix::fs::symlink;

        let root = temp_root();
        let outside = temp_root();
        fs::write(outside.join("actions.cedarschema"), "").unwrap();
        fs::write(outside.join("providers.json"), "{}").unwrap();
        symlink(
            outside.join("actions.cedarschema"),
            root.join("actions.cedarschema"),
        )
        .unwrap();
        let root_uri = path_to_file_uri(&root).unwrap();
        let resolver = ProjectResolver::from_initialize(&params(json!({
            "capabilities": {},
            "rootUri": root_uri
        })));

        assert!(
            resolver
                .resolve(&root.join("policy.dw"), Path::exists)
                .unwrap_err()
                .message
                .contains("symlink resolves outside")
        );

        fs::remove_file(root.join("actions.cedarschema")).unwrap();
        fs::write(root.join("actions.cedarschema"), "").unwrap();
        symlink(outside.join("providers.json"), root.join("providers.json")).unwrap();
        assert!(
            resolver
                .resolve(&root.join("policy.dw"), Path::exists)
                .unwrap_err()
                .message
                .contains("symlink resolves outside")
        );

        fs::remove_dir_all(root).unwrap();
        fs::remove_dir_all(outside).unwrap();
    }
}
