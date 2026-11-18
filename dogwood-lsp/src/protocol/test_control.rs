use std::collections::VecDeque;
use std::path::PathBuf;

use lsp_server::{ErrorCode, Notification, Request, Response};
use lsp_types::{FileChangeType, Uri};
use serde_json::json;

use super::lifecycle::Lifecycle;
use super::scheduler::Checkpoint;
use super::snapshots::{BundleIdentity, SourceIdentity, SourceOrigin};
use super::{DispatchOutcome, INVALID_PARAMS, SERVER_SHUT_DOWN, Server, immediate_response};

pub(super) const TEST_BARRIER: &str = "dogwood/testBarrier";
pub(super) const TEST_CONTROL: &str = "dogwood-lsp/testControl";
const TEST_REACHED: &str = "dogwood-lsp/testReached";
const TEST_WATCH_OBSERVED: &str = "dogwood-lsp/testWatchObserved";
const MAX_WATCH_OBSERVATIONS: usize = 256;

#[derive(Debug, Default)]
pub(super) struct ServerTestObservations {
    watch_registration: Option<&'static str>,
    watch_notifications_enabled: bool,
    next_watch_sequence: u64,
    watch_events: VecDeque<WatchTestObservation>,
}

#[derive(Clone, Debug)]
pub(super) struct WatchTestObservation {
    sequence: u64,
    uri: Uri,
    path: PathBuf,
    kind: &'static str,
}

pub(super) fn reached_notification(task_id: u64, point: &str) -> Notification {
    Notification::new(
        TEST_REACHED.to_owned(),
        json!({"task": task_id, "point": point}),
    )
}

pub(super) fn watch_observed_notification(event: WatchTestObservation) -> Notification {
    Notification::new(
        TEST_WATCH_OBSERVED.to_owned(),
        json!({
            "sequence": event.sequence,
            "uri": event.uri.as_str(),
            "path": event.path.display().to_string(),
            "kind": event.kind,
        }),
    )
}

impl Server {
    pub(super) fn test_control(&mut self, request: Request) -> DispatchOutcome {
        let id = request.id;
        let Some(command) = request
            .params
            .get("command")
            .and_then(serde_json::Value::as_str)
        else {
            return immediate_response(Response::new_err(
                id,
                ErrorCode::InvalidParams as i32,
                INVALID_PARAMS.to_owned(),
            ));
        };
        if self.lifecycle == Lifecycle::Shutdown && command != "snapshotStats" {
            return immediate_response(Response::new_err(
                id,
                ErrorCode::InvalidRequest as i32,
                SERVER_SHUT_DOWN.to_owned(),
            ));
        }
        match command {
            "pauseNext" => {
                let Some(point) = request
                    .params
                    .get("point")
                    .and_then(serde_json::Value::as_str)
                    .and_then(Checkpoint::parse)
                else {
                    return immediate_response(Response::new_err(
                        id,
                        ErrorCode::InvalidParams as i32,
                        INVALID_PARAMS.to_owned(),
                    ));
                };
                self.scheduler.pause_next(point);
                immediate_response(Response::new_ok(id, ()))
            }
            "release" => {
                let Some(task_id) = request
                    .params
                    .get("task")
                    .and_then(serde_json::Value::as_u64)
                else {
                    return immediate_response(Response::new_err(
                        id,
                        ErrorCode::InvalidParams as i32,
                        INVALID_PARAMS.to_owned(),
                    ));
                };
                if self.scheduler.release(task_id) {
                    immediate_response(Response::new_ok(id, ()))
                } else {
                    immediate_response(Response::new_err(
                        id,
                        ErrorCode::InvalidParams as i32,
                        INVALID_PARAMS.to_owned(),
                    ))
                }
            }
            "enableWatchNotifications" => {
                self.test_observations.watch_notifications_enabled = true;
                immediate_response(Response::new_ok(id, ()))
            }
            "snapshotStats" => {
                let scheduler = self.scheduler.snapshot_stats();
                let policies = self.policy_diagnostics.snapshot_stats();
                let policy_observations = self.policy_diagnostics.test_observations();
                immediate_response(Response::new_ok(
                    id,
                    json!({
                        "retentionLimit": scheduler.retention_limit,
                        "queuedValidationSnapshots": scheduler.queued_validation_snapshots,
                        "activeValidationSnapshots": scheduler.active_validation_snapshots,
                        "queuedPolicyPaths": scheduler
                            .queued_policy_paths
                            .iter()
                            .map(|path| path.display().to_string())
                            .collect::<Vec<_>>(),
                        "dirtyPolicies": self.dirty_policy_diagnostics.len(),
                        "completedPolicySnapshots": policies.completed_policy_snapshots,
                        "sharedDiskSources": policies.shared_disk_sources,
                        "sharedDiskSourceBytes": policies.shared_disk_source_bytes,
                        "diskSourceReads": policies.disk_source_reads,
                        "watchRegistration": self.test_observations.watch_registration,
                        "watchEvents": self.test_observations.watch_events.iter().map(|event| {
                            json!({
                                "sequence": event.sequence,
                                "uri": event.uri.as_str(),
                                "path": event.path.display().to_string(),
                                "kind": event.kind,
                            })
                        }).collect::<Vec<_>>(),
                        "policies": policy_observations.iter().map(|policy| {
                            json!({
                                "path": policy.path.display().to_string(),
                                "generation": policy.generation,
                                "dependencies": policy.dependencies.iter()
                                    .map(|path| path.display().to_string())
                                    .collect::<Vec<_>>(),
                                "identity": policy.identity.as_ref().map(bundle_identity_json),
                                "validationPending": policy.validation_pending,
                                "parserBacked": policy.parser_backed,
                            })
                        }).collect::<Vec<_>>(),
                        "pendingSemanticRequests": scheduler.pending_semantic_requests.iter()
                            .map(|request| {
                                json!({
                                    "task": request.task_id,
                                    "uri": request.uri.as_str(),
                                    "revision": request.revision,
                                    "state": request.state,
                                })
                            }).collect::<Vec<_>>(),
                        "semanticTerminalOutcomes": scheduler.semantic_terminal_outcomes.iter()
                            .map(|request| {
                                json!({
                                    "task": request.task_id,
                                    "uri": request.uri.as_str(),
                                    "revision": request.revision,
                                    "outcome": request.outcome,
                                })
                            }).collect::<Vec<_>>(),
                    }),
                ))
            }
            _ => immediate_response(Response::new_err(
                id,
                ErrorCode::InvalidParams as i32,
                INVALID_PARAMS.to_owned(),
            )),
        }
    }

    pub(super) fn record_watch_registration(&mut self, state: &'static str) {
        if self.scheduler.test_control_enabled() {
            self.test_observations.watch_registration = Some(state);
        }
    }

    pub(super) fn record_watch_event(
        &mut self,
        uri: Uri,
        path: PathBuf,
        typ: FileChangeType,
    ) -> Option<WatchTestObservation> {
        if !self.scheduler.test_control_enabled() {
            return None;
        }
        self.test_observations.next_watch_sequence = self
            .test_observations
            .next_watch_sequence
            .checked_add(1)
            .expect("test watcher sequence exhausted");
        if self.test_observations.watch_events.len() == MAX_WATCH_OBSERVATIONS {
            self.test_observations.watch_events.pop_front();
        }
        let observation = WatchTestObservation {
            sequence: self.test_observations.next_watch_sequence,
            uri,
            path,
            kind: file_change_kind(typ),
        };
        self.test_observations
            .watch_events
            .push_back(observation.clone());
        Some(observation)
    }

    pub(super) fn watch_notifications_enabled(&self) -> bool {
        self.test_observations.watch_notifications_enabled
    }
}

fn file_change_kind(typ: FileChangeType) -> &'static str {
    if typ == FileChangeType::CREATED {
        "created"
    } else if typ == FileChangeType::CHANGED {
        "changed"
    } else if typ == FileChangeType::DELETED {
        "deleted"
    } else {
        "unknown"
    }
}

fn bundle_identity_json(identity: &BundleIdentity) -> serde_json::Value {
    json!({
        "policy": source_identity_json(&identity.policy),
        "actionSchema": source_identity_json(&identity.action_schema),
        "eventSchema": identity.event_schema.as_ref().map(source_identity_json),
        "providers": identity.providers.as_ref().map(source_identity_json),
        "macros": identity.macros.as_ref().map(source_identity_json),
    })
}

fn source_identity_json(identity: &SourceIdentity) -> serde_json::Value {
    let origin = match identity.origin {
        SourceOrigin::Open { version, revision } => {
            json!({"kind": "open", "version": version, "revision": revision})
        }
        SourceOrigin::Disk { revision } => {
            json!({"kind": "disk", "revision": revision})
        }
    };
    json!({
        "path": identity.path.display().to_string(),
        "origin": origin,
    })
}
