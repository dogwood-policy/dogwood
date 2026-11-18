use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File};
use std::io::{Read, Take};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use dogwood_lsp::diagnostics::{
    INPUT_DIAGNOSTIC_CODE, PROJECT_DIAGNOSTIC_CODE, project_frontend_outcome,
    server_error_diagnostic, zero_range,
};
use dogwood_lsp::frontend::{
    FrontendOutcome, MAX_FRONTEND_SOURCE_BYTES, SourceKind, validate_bundle,
};
use dogwood_lsp::project::{
    CONVENTIONAL_OPTIONAL_INPUT_NAMES, ProjectFailure, ProjectResolver, ResolvedBundlePaths,
    is_action_schema_path, path_to_file_uri,
};
use lsp_types::{FileEvent, InitializeParams, PublishDiagnosticsParams, Uri};

use super::documents::{DocumentKind, DocumentStore};
use super::snapshots::{
    BundleIdentity, BundleSnapshot, SourceIdentity, SourceOrigin, SourceSnapshot,
};

const EXTERNAL_DEPENDENCY_WATCH_MESSAGE: &str = "Dogwood project configuration error: external \
    explicit dependencies require successful dynamic watched-file registration with \
    relativePatternSupport";

#[derive(Debug, Default)]
pub(crate) struct PolicyDiagnostics {
    resolver: Option<ProjectResolver>,
    policies: BTreeMap<PathBuf, PolicyTracking>,
    reverse_dependencies: BTreeMap<PathBuf, BTreeSet<PathBuf>>,
    disk_sources: DiskSourceStore,
    invalid_policies: BTreeMap<Uri, i32>,
    external_dependencies_watchable: bool,
    next_generation: u64,
}

#[derive(Debug, Default)]
struct PolicyTracking {
    dependencies: BTreeSet<PathBuf>,
    bundle_directory: Option<PathBuf>,
    discovery_root: Option<PathBuf>,
    generation: u64,
    current_identity: Option<BundleIdentity>,
    validation_pending: bool,
    semantic_snapshot: Option<Arc<BundleSnapshot>>,
    pending_validation: Option<PendingPolicyValidation>,
}

#[derive(Clone, Debug)]
struct PendingPolicyValidation {
    paths: ResolvedBundlePaths,
    generation: u64,
    version: i32,
    identity: BundleIdentity,
}

#[derive(Debug)]
struct CachedDiskSource {
    revision: u64,
    text: Arc<str>,
}

#[derive(Debug, Default)]
struct DiskSourceStore {
    sources: BTreeMap<PathBuf, CachedDiskSource>,
    #[cfg(feature = "test-control")]
    reads: u64,
}

impl DiskSourceStore {
    fn remove(&mut self, path: &Path) {
        self.sources.remove(path);
    }

    fn clear(&mut self) {
        self.sources.clear();
    }
}

pub(crate) enum SemanticSnapshot {
    Standalone {
        policy: Arc<str>,
    },
    Project {
        policy: Arc<str>,
        event_schema: Option<Arc<str>>,
        providers: Option<Arc<str>>,
        macros: Option<Arc<str>>,
    },
    Pending {
        generation: u64,
        identity: BundleIdentity,
    },
    Unavailable {
        policy: Arc<str>,
    },
}

#[derive(Debug, Default)]
pub(crate) struct DiagnosticActions {
    pub(crate) invalidated_policies: BTreeSet<PathBuf>,
    pub(crate) publications: Vec<PublishDiagnosticsParams>,
    pub(crate) pending_validations: BTreeSet<PathBuf>,
}

impl DiagnosticActions {
    pub(crate) fn extend(&mut self, other: Self) {
        self.invalidated_policies.extend(other.invalidated_policies);
        self.publications.extend(other.publications);
        self.pending_validations.extend(other.pending_validations);
    }
}

#[derive(Clone, Debug)]
pub(crate) struct PolicyValidationWork {
    pub(crate) policy_path: PathBuf,
    pub(crate) generation: u64,
    pub(crate) version: i32,
    pub(crate) identity: BundleIdentity,
    pub(crate) snapshot: Arc<BundleSnapshot>,
}

#[derive(Debug)]
pub(crate) struct PolicyValidationResult {
    pub(crate) policy_path: PathBuf,
    pub(crate) generation: u64,
    pub(crate) identity: BundleIdentity,
    pub(crate) publication: PublishDiagnosticsParams,
    pub(crate) snapshot: Arc<BundleSnapshot>,
    pub(crate) parser_backed: bool,
}

#[derive(Debug)]
pub(crate) struct PolicyValidationFailure {
    pub(crate) policy_path: PathBuf,
    pub(crate) generation: u64,
    pub(crate) identity: BundleIdentity,
    pub(crate) policy: Arc<str>,
    pub(crate) publication: PublishDiagnosticsParams,
}

#[derive(Debug)]
pub(crate) enum MaterializedPolicyValidation {
    Work(PolicyValidationWork),
    Failure(PolicyValidationFailure),
}

#[cfg(feature = "test-control")]
#[derive(Debug)]
pub(crate) struct PolicySnapshotStats {
    pub(crate) completed_policy_snapshots: usize,
    pub(crate) shared_disk_sources: usize,
    pub(crate) shared_disk_source_bytes: usize,
    pub(crate) disk_source_reads: u64,
}

#[cfg(feature = "test-control")]
#[derive(Debug)]
pub(crate) struct PolicyTestObservation {
    pub(crate) path: PathBuf,
    pub(crate) generation: u64,
    pub(crate) dependencies: Vec<PathBuf>,
    pub(crate) identity: Option<BundleIdentity>,
    pub(crate) validation_pending: bool,
    pub(crate) parser_backed: bool,
}

struct PreparedPolicy {
    publication: Option<PublishDiagnosticsParams>,
    validation_pending: bool,
    tracking_changes: TrackingChanges,
}

#[derive(Default)]
struct TrackingChanges {
    blocked_policies: BTreeSet<PathBuf>,
    released_dependencies: BTreeSet<PathBuf>,
}

impl PolicyDiagnostics {
    pub(crate) fn configure(&mut self, params: &InitializeParams) {
        self.resolver = Some(ProjectResolver::from_initialize(params));
    }

    pub(crate) fn is_explicit_dependency_path(&self, path: &Path) -> bool {
        self.resolver
            .as_ref()
            .is_some_and(|resolver| resolver.is_explicit_dependency_path(path))
    }

    pub(crate) fn watch_targets(&self) -> (Vec<PathBuf>, Vec<PathBuf>) {
        self.resolver
            .as_ref()
            .map(|resolver| {
                (
                    resolver.workspace_roots(),
                    resolver.explicit_dependency_paths(),
                )
            })
            .unwrap_or_default()
    }

    pub(crate) fn reset_external_dependencies_watchable(&mut self) {
        self.external_dependencies_watchable = false;
    }

    pub(crate) fn watch_registration_succeeded(
        &mut self,
        documents: &DocumentStore,
    ) -> DiagnosticActions {
        if self.external_dependencies_watchable {
            return DiagnosticActions::default();
        }
        self.external_dependencies_watchable = true;
        let affected = self.tracked_external_policies();
        self.revalidate(affected, BTreeSet::new(), documents)
    }

    pub(crate) fn watch_registration_failed(
        &mut self,
        documents: &DocumentStore,
    ) -> DiagnosticActions {
        if !self.external_dependencies_watchable {
            return DiagnosticActions::default();
        }
        self.external_dependencies_watchable = false;
        let affected = self.tracked_external_policies();
        self.revalidate(affected, BTreeSet::new(), documents)
    }

    fn tracked_external_policies(&self) -> BTreeSet<PathBuf> {
        let Some(resolver) = &self.resolver else {
            return BTreeSet::new();
        };
        self.policies
            .iter()
            .filter(|(_, tracking)| {
                tracking
                    .dependencies
                    .iter()
                    .any(|path| resolver.is_external_dependency_path(path))
            })
            .map(|(policy, _)| policy.clone())
            .collect()
    }

    pub(crate) fn document_opened(
        &mut self,
        path: &Path,
        kind: DocumentKind,
        documents: &DocumentStore,
    ) -> DiagnosticActions {
        self.disk_sources.remove(path);
        let mut affected = self.affected_by_dependency(path);
        if kind == DocumentKind::Policy && self.is_policy_candidate(path) {
            self.policies
                .insert(path.to_path_buf(), PolicyTracking::default());
            affected.insert(path.to_path_buf());
        }
        self.revalidate(affected, BTreeSet::new(), documents)
    }

    pub(crate) fn document_changed(
        &mut self,
        path: &Path,
        documents: &DocumentStore,
    ) -> DiagnosticActions {
        let mut affected = self.affected_by_dependency(path);
        if self.policies.contains_key(path) {
            affected.insert(path.to_path_buf());
        }
        self.revalidate(affected, BTreeSet::new(), documents)
    }

    pub(crate) fn document_closed(
        &mut self,
        path: &Path,
        uri: Uri,
        version: i32,
        documents: &DocumentStore,
    ) -> DiagnosticActions {
        self.disk_sources.remove(path);
        let affected = self.affected_by_dependency(path);
        let mut actions = DiagnosticActions::default();
        let released_dependencies = if self.policies.contains_key(path) {
            actions.invalidated_policies.insert(path.to_path_buf());
            let released = self.remove_policy(path);
            actions.publications.push(PublishDiagnosticsParams::new(
                uri,
                Vec::new(),
                Some(version),
            ));
            released
        } else {
            BTreeSet::new()
        };

        actions.extend(self.revalidate(affected, released_dependencies, documents));
        actions.publications = coalesce_publications(actions.publications);
        actions
    }

    pub(crate) fn watched_files(
        &mut self,
        events: &[FileEvent],
        documents: &DocumentStore,
    ) -> DiagnosticActions {
        let mut affected = BTreeSet::new();
        for event in events {
            let Ok(path) = dogwood_lsp::project::file_uri_to_path(&event.uri) else {
                continue;
            };
            self.disk_sources.remove(&path);
            affected.extend(self.affected_by_dependency(&path));
        }
        self.revalidate(affected, BTreeSet::new(), documents)
    }

    pub(crate) fn invalid_policy_opened(
        &mut self,
        uri: Uri,
        version: i32,
        message: String,
    ) -> PublishDiagnosticsParams {
        self.invalid_policies.insert(uri.clone(), version);
        PublishDiagnosticsParams::new(
            uri,
            vec![server_error_diagnostic(
                PROJECT_DIAGNOSTIC_CODE,
                format!("Dogwood project configuration error: {message}"),
                None,
            )],
            Some(version),
        )
    }

    pub(crate) fn invalid_policy_closed(&mut self, uri: &Uri) -> Option<PublishDiagnosticsParams> {
        self.invalid_policies
            .remove(uri)
            .map(|version| PublishDiagnosticsParams::new(uri.clone(), Vec::new(), Some(version)))
    }

    pub(crate) fn semantic_snapshot(
        &self,
        policy_path: &Path,
        documents: &DocumentStore,
    ) -> Option<SemanticSnapshot> {
        let (_, policy) = documents.get_by_path(policy_path)?;
        let policy_text = policy.text_snapshot();
        let Some(tracking) = self.policies.get(policy_path) else {
            return Some(SemanticSnapshot::Standalone {
                policy: policy_text,
            });
        };
        if let Some(snapshot) = &tracking.semantic_snapshot {
            return Some(SemanticSnapshot::Project {
                policy: Arc::clone(&snapshot.policy.text),
                event_schema: snapshot
                    .event_schema
                    .as_ref()
                    .map(|source| Arc::clone(&source.text)),
                providers: snapshot
                    .providers
                    .as_ref()
                    .map(|source| Arc::clone(&source.text)),
                macros: snapshot
                    .macros
                    .as_ref()
                    .map(|source| Arc::clone(&source.text)),
            });
        }
        if tracking.validation_pending
            && let Some(identity) = &tracking.current_identity
        {
            return Some(SemanticSnapshot::Pending {
                generation: tracking.generation,
                identity: identity.clone(),
            });
        }
        Some(SemanticSnapshot::Unavailable {
            policy: policy_text,
        })
    }

    pub(crate) fn complete_validation(
        &mut self,
        result: PolicyValidationResult,
    ) -> Option<PublishDiagnosticsParams> {
        let tracking = self.policies.get_mut(&result.policy_path)?;
        if tracking.generation != result.generation
            || tracking.current_identity.as_ref() != Some(&result.identity)
        {
            return None;
        }
        tracking.validation_pending = false;
        tracking.semantic_snapshot = result.parser_backed.then(|| Arc::clone(&result.snapshot));
        Some(result.publication)
    }

    pub(crate) fn materialize_validation(
        &mut self,
        policy_path: &Path,
        documents: &DocumentStore,
    ) -> Option<MaterializedPolicyValidation> {
        let pending = self.policies.get(policy_path)?.pending_validation.clone()?;
        let (policy_uri, policy) = documents.get_by_path(policy_path)?;
        let policy_text = policy.text_snapshot();
        let policy_source = SourceSnapshot {
            uri: policy_uri.clone(),
            identity: pending.identity.policy.clone(),
            text: Arc::clone(&policy_text),
        };
        let snapshot = load_bundle(
            policy_source,
            &pending.paths,
            documents,
            &mut self.disk_sources,
        );

        match snapshot {
            Ok(snapshot) => {
                let snapshot = Arc::new(snapshot);
                debug_assert_eq!(snapshot.identity(), pending.identity);
                Some(MaterializedPolicyValidation::Work(PolicyValidationWork {
                    policy_path: policy_path.to_path_buf(),
                    generation: pending.generation,
                    version: pending.version,
                    identity: pending.identity,
                    snapshot,
                }))
            }
            Err(failure) => {
                let tracking = self.policies.get_mut(policy_path)?;
                if tracking.generation != pending.generation
                    || tracking.current_identity.as_ref() != Some(&pending.identity)
                {
                    return None;
                }
                tracking.pending_validation = None;
                tracking.validation_pending = false;
                Some(MaterializedPolicyValidation::Failure(
                    PolicyValidationFailure {
                        policy_path: policy_path.to_path_buf(),
                        generation: pending.generation,
                        identity: pending.identity,
                        policy: policy_text,
                        publication: load_failure_publication(
                            policy_uri,
                            pending.version,
                            failure,
                            documents,
                        ),
                    },
                ))
            }
        }
    }

    pub(crate) fn validation_scheduled(&mut self, policy: &Path, generation: u64) {
        let Some(tracking) = self.policies.get_mut(policy) else {
            return;
        };
        if tracking
            .pending_validation
            .as_ref()
            .is_some_and(|pending| pending.generation == generation)
        {
            tracking.pending_validation = None;
        }
    }

    pub(crate) fn release_snapshots(&mut self) {
        for tracking in self.policies.values_mut() {
            tracking.pending_validation = None;
            tracking.validation_pending = false;
            tracking.semantic_snapshot = None;
        }
        self.disk_sources.clear();
    }

    #[cfg(feature = "test-control")]
    pub(crate) fn snapshot_stats(&self) -> PolicySnapshotStats {
        PolicySnapshotStats {
            completed_policy_snapshots: self
                .policies
                .values()
                .filter(|tracking| tracking.semantic_snapshot.is_some())
                .count(),
            shared_disk_sources: self.disk_sources.sources.len(),
            shared_disk_source_bytes: self
                .disk_sources
                .sources
                .values()
                .map(|source| source.text.len())
                .sum(),
            disk_source_reads: self.disk_sources.reads,
        }
    }

    #[cfg(feature = "test-control")]
    pub(crate) fn test_observations(&self) -> Vec<PolicyTestObservation> {
        self.policies
            .iter()
            .map(|(path, tracking)| PolicyTestObservation {
                path: path.clone(),
                generation: tracking.generation,
                dependencies: tracking.dependencies.iter().cloned().collect(),
                identity: tracking.current_identity.clone(),
                validation_pending: tracking.validation_pending,
                parser_backed: tracking.semantic_snapshot.is_some(),
            })
            .collect()
    }

    fn is_policy_candidate(&self, path: &Path) -> bool {
        path.extension().and_then(|extension| extension.to_str()) == Some("dw")
            && !self.has_external_dependents(path)
    }

    fn has_external_dependents(&self, path: &Path) -> bool {
        self.reverse_dependencies
            .get(path)
            .is_some_and(|policies| policies.iter().any(|policy| policy != path))
    }

    fn affected_by_dependency(&self, path: &Path) -> BTreeSet<PathBuf> {
        let mut affected = self
            .reverse_dependencies
            .get(path)
            .cloned()
            .unwrap_or_default();
        affected.extend(self.affected_by_conventional_path(path));
        affected
    }

    fn affected_by_conventional_path(&self, path: &Path) -> BTreeSet<PathBuf> {
        let action_schema = is_action_schema_path(path);
        let optional_name = path
            .file_name()
            .and_then(|name| name.to_str())
            .filter(|name| CONVENTIONAL_OPTIONAL_INPUT_NAMES.contains(name));
        if !action_schema && optional_name.is_none() {
            return BTreeSet::new();
        }
        let Some(directory) = path.parent() else {
            return BTreeSet::new();
        };
        self.policies
            .iter()
            .filter_map(|(policy, tracking)| {
                let root = tracking.discovery_root.as_deref()?;
                let policy_directory = policy.parent()?;
                let relevant = if action_schema {
                    directory.starts_with(root)
                        && policy_directory.starts_with(directory)
                        && tracking
                            .bundle_directory
                            .as_deref()
                            .is_none_or(|bundle| directory.starts_with(bundle))
                } else {
                    tracking.bundle_directory.as_deref() == Some(directory)
                };
                relevant.then(|| policy.clone())
            })
            .collect()
    }

    fn revalidate(
        &mut self,
        mut affected: BTreeSet<PathBuf>,
        mut promotion_candidates: BTreeSet<PathBuf>,
        documents: &DocumentStore,
    ) -> DiagnosticActions {
        let mut actions = DiagnosticActions::default();
        loop {
            while let Some(policy) = affected.pop_first() {
                if !self.policies.contains_key(&policy) {
                    continue;
                }
                let Some(prepared) = self.prepare_policy(&policy, documents) else {
                    continue;
                };
                actions.invalidated_policies.insert(policy.clone());

                for blocked in prepared.tracking_changes.blocked_policies {
                    if !self.policies.contains_key(&blocked)
                        || !self.has_external_dependents(&blocked)
                    {
                        continue;
                    }
                    let clear = documents.get_by_path(&blocked).map(|(uri, document)| {
                        PublishDiagnosticsParams::new(
                            uri.clone(),
                            Vec::new(),
                            Some(document.version()),
                        )
                    });
                    actions.invalidated_policies.insert(blocked.clone());
                    promotion_candidates.extend(self.remove_policy(&blocked));
                    if let Some(clear) = clear {
                        actions.publications.push(clear);
                    }
                }
                promotion_candidates.extend(prepared.tracking_changes.released_dependencies);
                if let Some(publication) = prepared.publication {
                    actions.publications.push(publication);
                }
                if prepared.validation_pending {
                    actions.pending_validations.insert(policy);
                }
            }

            let Some(candidate) = promotion_candidates.pop_first() else {
                break;
            };
            if self.policies.contains_key(&candidate)
                || !self.is_policy_candidate(&candidate)
                || !documents.contains_path(&candidate)
            {
                continue;
            }
            self.policies
                .insert(candidate.clone(), PolicyTracking::default());
            affected.insert(candidate);
        }
        actions.publications = coalesce_publications(actions.publications);
        actions
    }

    fn prepare_policy(
        &mut self,
        policy_path: &Path,
        documents: &DocumentStore,
    ) -> Option<PreparedPolicy> {
        let (policy_uri, policy) = documents.get_by_path(policy_path)?;
        let policy_uri = policy_uri.clone();
        let policy_version = policy.version();
        let policy_revision = policy.revision();
        let resolver = self
            .resolver
            .as_ref()
            .expect("policy diagnostics are configured during initialize");
        let discovery_root = resolver
            .discovery_root_for(policy_path)
            .map(Path::to_path_buf);
        let resolved = resolver.resolve_with_schema_candidates(
            policy_path,
            |path| documents.contains_path(path) || disk_path_is_present(path),
            documents.paths().map(Path::to_path_buf),
        );

        let paths = match resolved {
            Ok(paths) => paths,
            Err(failure) => {
                let generation = self.allocate_generation();
                let tracking_changes = self.replace_tracking(
                    policy_path,
                    &failure.dependencies,
                    None,
                    discovery_root,
                    generation,
                    None,
                );
                return Some(PreparedPolicy {
                    publication: Some(project_failure_publication(
                        &policy_uri,
                        policy_version,
                        failure,
                        documents,
                    )),
                    validation_pending: false,
                    tracking_changes,
                });
            }
        };
        let dependencies = paths.dependencies();
        let external_dependencies = resolver.external_dependency_paths(&paths);
        if !self.external_dependencies_watchable && !external_dependencies.is_empty() {
            let generation = self.allocate_generation();
            let tracking_changes = self.replace_tracking(
                policy_path,
                &dependencies,
                discovery_root
                    .as_ref()
                    .map(|_| paths.bundle_directory().to_path_buf()),
                discovery_root,
                generation,
                None,
            );
            return Some(PreparedPolicy {
                publication: Some(project_failure_publication(
                    &policy_uri,
                    policy_version,
                    ProjectFailure {
                        message: EXTERNAL_DEPENDENCY_WATCH_MESSAGE.to_owned(),
                        related_path: external_dependencies.into_iter().next(),
                        dependencies,
                    },
                    documents,
                )),
                validation_pending: false,
                tracking_changes,
            });
        }

        let identity = bundle_identity(
            policy_path,
            policy_version,
            policy_revision,
            &paths,
            documents,
        );
        let generation = self.allocate_generation();
        let tracking_changes = self.replace_tracking(
            policy_path,
            &dependencies,
            discovery_root
                .as_ref()
                .map(|_| paths.bundle_directory().to_path_buf()),
            discovery_root,
            generation,
            Some(identity.clone()),
        );
        let pending_validation = PendingPolicyValidation {
            paths,
            generation,
            version: policy_version,
            identity,
        };
        let tracking = self
            .policies
            .get_mut(policy_path)
            .expect("prepared policy should remain tracked");
        tracking.pending_validation = Some(pending_validation);
        tracking.validation_pending = true;
        Some(PreparedPolicy {
            publication: None,
            validation_pending: true,
            tracking_changes,
        })
    }

    fn replace_tracking(
        &mut self,
        policy: &Path,
        dependencies: &[(SourceKind, PathBuf)],
        bundle_directory: Option<PathBuf>,
        discovery_root: Option<PathBuf>,
        generation: u64,
        current_identity: Option<BundleIdentity>,
    ) -> TrackingChanges {
        let previous_dependencies = self
            .policies
            .get(policy)
            .map(|tracking| tracking.dependencies.clone())
            .unwrap_or_default();
        let dependency_paths: BTreeSet<_> =
            dependencies.iter().map(|(_, path)| path.clone()).collect();

        for dependency in previous_dependencies.difference(&dependency_paths) {
            if let Some(policies) = self.reverse_dependencies.get_mut(dependency) {
                policies.remove(policy);
                if policies.is_empty() {
                    self.reverse_dependencies.remove(dependency);
                    self.disk_sources.remove(dependency);
                }
            }
        }
        for dependency in dependency_paths.difference(&previous_dependencies) {
            self.reverse_dependencies
                .entry(dependency.clone())
                .or_default()
                .insert(policy.to_path_buf());
        }
        self.policies.insert(
            policy.to_path_buf(),
            PolicyTracking {
                dependencies: dependency_paths.clone(),
                bundle_directory,
                discovery_root,
                generation,
                current_identity,
                validation_pending: false,
                semantic_snapshot: None,
                pending_validation: None,
            },
        );

        TrackingChanges {
            blocked_policies: dependency_paths
                .iter()
                .filter(|dependency| dependency.as_path() != policy)
                .filter(|dependency| self.policies.contains_key(dependency.as_path()))
                .cloned()
                .collect(),
            released_dependencies: previous_dependencies
                .difference(&dependency_paths)
                .cloned()
                .collect(),
        }
    }

    fn remove_policy(&mut self, policy: &Path) -> BTreeSet<PathBuf> {
        let Some(tracking) = self.policies.remove(policy) else {
            return BTreeSet::new();
        };
        for dependency in &tracking.dependencies {
            if let Some(policies) = self.reverse_dependencies.get_mut(dependency) {
                policies.remove(policy);
                if policies.is_empty() {
                    self.reverse_dependencies.remove(dependency);
                    self.disk_sources.remove(dependency);
                }
            }
        }
        tracking.dependencies
    }

    fn allocate_generation(&mut self) -> u64 {
        self.next_generation = self
            .next_generation
            .checked_add(1)
            .expect("policy validation generation counter exhausted");
        self.next_generation
    }
}

pub(crate) fn run_policy_validation(work: PolicyValidationWork) -> PolicyValidationResult {
    let outcome = validate_bundle(&work.snapshot.frontend_input());
    let parser_backed = matches!(&outcome, FrontendOutcome::Report(_));
    let publication = project_frontend_outcome(work.version, work.snapshot.documents(), outcome);
    PolicyValidationResult {
        policy_path: work.policy_path,
        generation: work.generation,
        identity: work.identity,
        publication,
        snapshot: work.snapshot,
        parser_backed,
    }
}

fn disk_path_is_present(path: &Path) -> bool {
    match fs::symlink_metadata(path) {
        Ok(_) => true,
        Err(error) => error.kind() != std::io::ErrorKind::NotFound,
    }
}

fn coalesce_publications(
    publications: Vec<PublishDiagnosticsParams>,
) -> Vec<PublishDiagnosticsParams> {
    let mut indices = BTreeMap::new();
    let mut coalesced = Vec::with_capacity(publications.len());
    for publication in publications {
        let key = (publication.uri.as_str().to_owned(), publication.version);
        if let Some(index) = indices.get(&key).copied() {
            coalesced[index] = publication;
        } else {
            indices.insert(key, coalesced.len());
            coalesced.push(publication);
        }
    }
    coalesced
}

fn project_failure_publication(
    policy_uri: &Uri,
    version: i32,
    failure: ProjectFailure,
    documents: &DocumentStore,
) -> PublishDiagnosticsParams {
    let related = failure.related_path.as_deref().and_then(|path| {
        source_uri(path, documents).ok().map(|uri| {
            (
                uri,
                zero_range(),
                "Dogwood project input location".to_owned(),
            )
        })
    });
    PublishDiagnosticsParams::new(
        policy_uri.clone(),
        vec![server_error_diagnostic(
            PROJECT_DIAGNOSTIC_CODE,
            failure.message,
            related,
        )],
        Some(version),
    )
}

fn bundle_identity(
    policy_path: &Path,
    policy_version: i32,
    policy_revision: u64,
    paths: &ResolvedBundlePaths,
    documents: &DocumentStore,
) -> BundleIdentity {
    BundleIdentity {
        policy: SourceIdentity {
            path: policy_path.to_path_buf(),
            origin: SourceOrigin::Open {
                version: policy_version,
                revision: policy_revision,
            },
        },
        action_schema: source_identity(&paths.action_schema, documents),
        event_schema: paths
            .event_schema
            .as_deref()
            .map(|path| source_identity(path, documents)),
        providers: paths
            .providers
            .as_deref()
            .map(|path| source_identity(path, documents)),
        macros: paths
            .macros
            .as_deref()
            .map(|path| source_identity(path, documents)),
    }
}

fn source_identity(path: &Path, documents: &DocumentStore) -> SourceIdentity {
    let origin = documents
        .get_by_path(path)
        .map(|(_, document)| SourceOrigin::Open {
            version: document.version(),
            revision: document.revision(),
        })
        .unwrap_or_else(|| SourceOrigin::Disk {
            revision: documents.disk_revision(path),
        });
    SourceIdentity {
        path: path.to_path_buf(),
        origin,
    }
}

#[derive(Debug)]
struct LoadFailure {
    path: PathBuf,
    kind: SourceKind,
    message: String,
}

fn load_failure_publication(
    policy_uri: &Uri,
    version: i32,
    failure: LoadFailure,
    documents: &DocumentStore,
) -> PublishDiagnosticsParams {
    let related = source_uri(&failure.path, documents).ok().map(|uri| {
        (
            uri,
            zero_range(),
            format!("Dogwood {} input", failure.kind.as_str()),
        )
    });
    PublishDiagnosticsParams::new(
        policy_uri.clone(),
        vec![server_error_diagnostic(
            INPUT_DIAGNOSTIC_CODE,
            failure.message,
            related,
        )],
        Some(version),
    )
}

fn load_bundle(
    policy: SourceSnapshot,
    paths: &ResolvedBundlePaths,
    documents: &DocumentStore,
    disk_sources: &mut DiskSourceStore,
) -> Result<BundleSnapshot, LoadFailure> {
    Ok(BundleSnapshot {
        policy,
        action_schema: load_source(
            &paths.action_schema,
            SourceKind::ActionSchema,
            documents,
            disk_sources,
        )?,
        event_schema: paths
            .event_schema
            .as_deref()
            .map(|path| load_source(path, SourceKind::EventSchema, documents, disk_sources))
            .transpose()?,
        providers: paths
            .providers
            .as_deref()
            .map(|path| load_source(path, SourceKind::Providers, documents, disk_sources))
            .transpose()?,
        macros: paths
            .macros
            .as_deref()
            .map(|path| load_source(path, SourceKind::Macros, documents, disk_sources))
            .transpose()?,
    })
}

fn load_source(
    path: &Path,
    kind: SourceKind,
    documents: &DocumentStore,
    disk_sources: &mut DiskSourceStore,
) -> Result<SourceSnapshot, LoadFailure> {
    if let Some((uri, document)) = documents.get_by_path(path) {
        return Ok(SourceSnapshot {
            uri: uri.clone(),
            identity: SourceIdentity {
                path: path.to_path_buf(),
                origin: SourceOrigin::Open {
                    version: document.version(),
                    revision: document.revision(),
                },
            },
            text: document.text_snapshot(),
        });
    }

    let uri =
        path_to_file_uri(path).map_err(|_| load_failure(path, kind, "has an invalid path"))?;
    let revision = documents.disk_revision(path);
    if let Some(source) = disk_sources
        .sources
        .get(path)
        .filter(|source| source.revision == revision)
    {
        return Ok(SourceSnapshot {
            uri,
            identity: SourceIdentity {
                path: path.to_path_buf(),
                origin: SourceOrigin::Disk { revision },
            },
            text: Arc::clone(&source.text),
        });
    }

    let metadata = fs::metadata(path).map_err(|error| {
        let reason = if error.kind() == std::io::ErrorKind::NotFound {
            "does not exist"
        } else if error.kind() == std::io::ErrorKind::PermissionDenied {
            "is not readable"
        } else {
            "cannot be inspected"
        };
        load_failure(path, kind, reason)
    })?;
    if !metadata.is_file() {
        return Err(load_failure(path, kind, "is not a regular file"));
    }
    if metadata.len() > MAX_FRONTEND_SOURCE_BYTES as u64 {
        return Err(load_failure(
            path,
            kind,
            "exceeds the 1048576-byte source limit",
        ));
    }

    let file = File::open(path).map_err(|error| {
        let reason = if error.kind() == std::io::ErrorKind::PermissionDenied {
            "is not readable"
        } else {
            "cannot be opened"
        };
        load_failure(path, kind, reason)
    })?;
    let mut bytes = Vec::with_capacity(metadata.len() as usize);
    let mut limited = file.take(MAX_FRONTEND_SOURCE_BYTES as u64 + 1);
    read_bounded(&mut limited, &mut bytes)
        .map_err(|_| load_failure(path, kind, "cannot be read"))?;
    if bytes.len() > MAX_FRONTEND_SOURCE_BYTES {
        return Err(load_failure(
            path,
            kind,
            "exceeds the 1048576-byte source limit",
        ));
    }
    let text =
        String::from_utf8(bytes).map_err(|_| load_failure(path, kind, "is not valid UTF-8"))?;
    let text: Arc<str> = Arc::from(text);
    #[cfg(feature = "test-control")]
    {
        disk_sources.reads = disk_sources
            .reads
            .checked_add(1)
            .expect("disk source read counter exhausted");
    }
    disk_sources.sources.insert(
        path.to_path_buf(),
        CachedDiskSource {
            revision,
            text: Arc::clone(&text),
        },
    );
    Ok(SourceSnapshot {
        uri,
        identity: SourceIdentity {
            path: path.to_path_buf(),
            origin: SourceOrigin::Disk { revision },
        },
        text,
    })
}

fn read_bounded(reader: &mut Take<File>, bytes: &mut Vec<u8>) -> std::io::Result<()> {
    reader.read_to_end(bytes).map(|_| ())
}

fn load_failure(path: &Path, kind: SourceKind, reason: &str) -> LoadFailure {
    LoadFailure {
        path: path.to_path_buf(),
        kind,
        message: format!("Dogwood input load error: {} {reason}", kind.as_str()),
    }
}

fn source_uri(path: &Path, documents: &DocumentStore) -> Result<Uri, String> {
    documents
        .get_by_path(path)
        .map(|(uri, _)| uri.clone())
        .map(Ok)
        .unwrap_or_else(|| path_to_file_uri(path))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;
    use std::path::PathBuf;
    use std::str::FromStr;

    use lsp_types::{Diagnostic, PublishDiagnosticsParams, Range, Uri};

    use super::{PolicyDiagnostics, coalesce_publications};

    #[test]
    fn policy_candidate_role_allows_self_dependency_but_not_external_dependents() {
        let policy = PathBuf::from("/workspace/macros.dw");
        let other_policy = PathBuf::from("/workspace/policy.dw");
        let mut diagnostics = PolicyDiagnostics::default();

        assert!(diagnostics.is_policy_candidate(&policy));
        diagnostics
            .reverse_dependencies
            .insert(policy.clone(), BTreeSet::from([policy.clone()]));
        assert!(diagnostics.is_policy_candidate(&policy));

        diagnostics
            .reverse_dependencies
            .get_mut(&policy)
            .unwrap()
            .insert(other_policy);
        assert!(!diagnostics.is_policy_candidate(&policy));
        assert!(!diagnostics.is_policy_candidate(&PathBuf::from("/workspace/schema.txt")));
    }

    #[test]
    fn publication_coalescing_keeps_final_state_and_distinct_uri_order() {
        let first_uri = Uri::from_str("file:///workspace/a.dw").unwrap();
        let second_uri = Uri::from_str("file:///workspace/z.dw").unwrap();
        let diagnostic =
            |message: &str| Diagnostic::new_simple(Range::default(), message.to_owned());
        let publications = vec![
            PublishDiagnosticsParams::new(first_uri.clone(), vec![diagnostic("obsolete")], Some(3)),
            PublishDiagnosticsParams::new(second_uri.clone(), vec![diagnostic("second")], Some(4)),
            PublishDiagnosticsParams::new(first_uri.clone(), Vec::new(), Some(3)),
            PublishDiagnosticsParams::new(
                first_uri.clone(),
                vec![diagnostic("first"), diagnostic("second")],
                Some(5),
            ),
        ];

        let coalesced = coalesce_publications(publications);

        assert_eq!(coalesced.len(), 3);
        assert_eq!(coalesced[0].uri, first_uri);
        assert_eq!(coalesced[0].version, Some(3));
        assert!(coalesced[0].diagnostics.is_empty());
        assert_eq!(coalesced[1].uri, second_uri);
        assert_eq!(coalesced[1].version, Some(4));
        assert_eq!(coalesced[1].diagnostics[0].message, "second");
        assert_eq!(coalesced[2].uri, first_uri);
        assert_eq!(coalesced[2].version, Some(5));
        assert_eq!(coalesced[2].diagnostics.len(), 2);
    }
}
