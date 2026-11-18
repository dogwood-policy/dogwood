mod capabilities;
mod documents;
mod encoding;
mod lifecycle;
mod policy_diagnostics;
mod scheduler;
mod snapshots;
#[cfg(feature = "test-control")]
mod test_control;
mod watchers;

use std::collections::BTreeSet;
use std::path::PathBuf;

use lsp_server::{ErrorCode, Message, Notification, Request, RequestId, Response};
use lsp_types::{
    CancelParams, DidChangeTextDocumentParams, DidChangeWatchedFilesParams,
    DidCloseTextDocumentParams, DidOpenTextDocumentParams, InitializeParams, InitializedParams,
    NumberOrString, PublishDiagnosticsParams, SemanticTokensParams, Uri,
};

use self::documents::{DocumentError, DocumentKind, DocumentStore, is_dw_uri};
use self::lifecycle::Lifecycle;
use self::policy_diagnostics::{
    DiagnosticActions, MaterializedPolicyValidation, PolicyDiagnostics, SemanticSnapshot,
};
use self::scheduler::{
    AsyncEvent, DiagnosticSchedule, Scheduler, SchemaDiagnosticWork, SemanticFailure,
    SemanticInput, SemanticWork, WorkOutput,
};
#[cfg(feature = "test-control")]
use self::test_control::{ServerTestObservations, TEST_BARRIER, TEST_CONTROL};

const INITIALIZE: &str = "initialize";
const INITIALIZED: &str = "initialized";
const SHUTDOWN: &str = "shutdown";
const EXIT: &str = "exit";
const DID_OPEN: &str = "textDocument/didOpen";
const DID_CHANGE: &str = "textDocument/didChange";
const DID_CLOSE: &str = "textDocument/didClose";
const DID_CHANGE_WATCHED_FILES: &str = "workspace/didChangeWatchedFiles";
const CANCEL_REQUEST: &str = "$/cancelRequest";
const PUBLISH_DIAGNOSTICS: &str = "textDocument/publishDiagnostics";
const SEMANTIC_TOKENS_FULL: &str = "textDocument/semanticTokens/full";
const WATCH_REGISTRATION_REQUEST_ID: &str = "dogwood-lsp/register-watched-files";

const SERVER_NOT_INITIALIZED: &str = "Server not initialized";
const SERVER_SHUT_DOWN: &str = "Server has shut down";
const DUPLICATE_INITIALIZE: &str = "Initialize request may only be sent once";
const INVALID_PARAMS: &str = "Invalid params";
const METHOD_NOT_FOUND: &str = "Method not found";
const DOCUMENT_NOT_OPEN: &str = "Document is not open";
const SEMANTIC_TOKEN_LIMIT_EXCEEDED: &str = "Semantic token limit exceeded";
const INTERNAL_ERROR: &str = "Internal error";
const REQUEST_CANCELLED: &str = "Request cancelled";
const CONTENT_MODIFIED: &str = "Content modified";
const SERVER_CANCELLED: &str = "Server cancelled";

#[derive(Debug, Default)]
pub(crate) struct Server {
    lifecycle: Lifecycle,
    documents: DocumentStore,
    policy_diagnostics: PolicyDiagnostics,
    scheduler: Scheduler,
    watched_files_dynamic_registration: bool,
    watched_files_relative_pattern_support: bool,
    pending_watch_registration: Option<RequestId>,
    pending_barriers: Vec<Response>,
    dirty_policy_diagnostics: BTreeSet<PathBuf>,
    dirty_schema_diagnostics: BTreeSet<Uri>,
    #[cfg(feature = "test-control")]
    test_observations: ServerTestObservations,
}

#[derive(Debug, Default)]
pub(crate) struct DispatchOutcome {
    pub(crate) requests: Vec<Request>,
    pub(crate) response: Option<Response>,
    pub(crate) responses: Vec<Response>,
    pub(crate) notifications: Vec<Notification>,
    pub(crate) exit_code: Option<u8>,
}

impl Server {
    pub(crate) fn async_events(&self) -> crossbeam_channel::Receiver<AsyncEvent> {
        self.scheduler.events()
    }

    pub(crate) fn handle_message(&mut self, message: Message) -> DispatchOutcome {
        let outcome = match message {
            Message::Request(request) => self.handle_request(request),
            Message::Notification(notification) => self.handle_notification(notification),
            Message::Response(response) => self.handle_client_response(response),
        };
        self.finish_dispatch(outcome)
    }

    pub(crate) fn handle_async_event(&mut self, event: AsyncEvent) -> DispatchOutcome {
        let outcome = match event {
            AsyncEvent::Completion(completion) => {
                let mut outcome = DispatchOutcome::default();
                if let Some(output) = self.scheduler.complete(*completion) {
                    self.handle_work_output(output, &mut outcome);
                }
                outcome
            }
            #[cfg(feature = "test-control")]
            AsyncEvent::TestReached { task_id, point } => DispatchOutcome {
                notifications: vec![test_control::reached_notification(task_id, point.name())],
                ..DispatchOutcome::default()
            },
        };
        self.finish_dispatch(outcome)
    }

    fn handle_request(&mut self, request: Request) -> DispatchOutcome {
        let response = match self.lifecycle {
            #[cfg(feature = "test-control")]
            Lifecycle::Shutdown
                if request.method == TEST_CONTROL && self.scheduler.test_control_enabled() =>
            {
                return self.test_control(request);
            }
            Lifecycle::Shutdown => {
                error_response(request, ErrorCode::InvalidRequest as i32, SERVER_SHUT_DOWN)
            }
            Lifecycle::PreInitialize if request.method == INITIALIZE => self.initialize(request),
            Lifecycle::PreInitialize => error_response(
                request,
                ErrorCode::ServerNotInitialized as i32,
                SERVER_NOT_INITIALIZED,
            ),
            Lifecycle::AwaitInitialized if request.method == INITIALIZE => error_response(
                request,
                ErrorCode::InvalidRequest as i32,
                DUPLICATE_INITIALIZE,
            ),
            Lifecycle::AwaitInitialized => error_response(
                request,
                ErrorCode::ServerNotInitialized as i32,
                SERVER_NOT_INITIALIZED,
            ),
            Lifecycle::Running if request.method == INITIALIZE => error_response(
                request,
                ErrorCode::InvalidRequest as i32,
                DUPLICATE_INITIALIZE,
            ),
            Lifecycle::Running => return self.handle_running_request(request),
        };
        DispatchOutcome {
            response: Some(response),
            ..DispatchOutcome::default()
        }
    }

    fn initialize(&mut self, request: Request) -> Response {
        let id = request.id;
        let params = match serde_json::from_value::<InitializeParams>(request.params) {
            Ok(params) => params,
            Err(_) => {
                return Response::new_err(
                    id,
                    ErrorCode::InvalidParams as i32,
                    INVALID_PARAMS.to_owned(),
                );
            }
        };

        self.policy_diagnostics.configure(&params);
        let watched_files_capability = params
            .capabilities
            .workspace
            .as_ref()
            .and_then(|workspace| workspace.did_change_watched_files.as_ref());
        self.watched_files_dynamic_registration = watched_files_capability
            .and_then(|capability| capability.dynamic_registration)
            == Some(true);
        self.watched_files_relative_pattern_support = watched_files_capability
            .and_then(|capability| capability.relative_pattern_support)
            == Some(true);
        self.policy_diagnostics
            .reset_external_dependencies_watchable();
        self.lifecycle.begin_initialization();
        Response::new_ok(id, capabilities::initialize_result())
    }

    fn handle_running_request(&mut self, request: Request) -> DispatchOutcome {
        match request.method.as_str() {
            SHUTDOWN => self.shutdown(request),
            SEMANTIC_TOKENS_FULL => self.semantic_tokens(request),
            #[cfg(feature = "test-control")]
            TEST_CONTROL if self.scheduler.test_control_enabled() => self.test_control(request),
            #[cfg(feature = "test-control")]
            TEST_BARRIER if self.scheduler.test_control_enabled() => {
                let response =
                    error_response(request, ErrorCode::MethodNotFound as i32, METHOD_NOT_FOUND);
                if self.analysis_idle() {
                    immediate_response(response)
                } else {
                    self.pending_barriers.push(response);
                    DispatchOutcome::default()
                }
            }
            _ => DispatchOutcome {
                response: Some(error_response(
                    request,
                    ErrorCode::MethodNotFound as i32,
                    METHOD_NOT_FOUND,
                )),
                ..DispatchOutcome::default()
            },
        }
    }

    fn shutdown(&mut self, request: Request) -> DispatchOutcome {
        let id = request.id;
        if serde_json::from_value::<()>(request.params).is_err() {
            return DispatchOutcome {
                response: Some(Response::new_err(
                    id,
                    ErrorCode::InvalidParams as i32,
                    INVALID_PARAMS.to_owned(),
                )),
                ..DispatchOutcome::default()
            };
        }

        self.lifecycle.shutdown();
        self.dirty_policy_diagnostics.clear();
        self.dirty_schema_diagnostics.clear();
        self.policy_diagnostics.release_snapshots();
        let mut responses: Vec<_> = self
            .scheduler
            .cancel_all()
            .into_iter()
            .map(|request_id| {
                Response::new_err(
                    request_id,
                    ErrorCode::RequestCanceled as i32,
                    REQUEST_CANCELLED.to_owned(),
                )
            })
            .collect();
        responses.append(&mut self.pending_barriers);
        DispatchOutcome {
            response: Some(Response::new_ok(id, ())),
            responses,
            ..DispatchOutcome::default()
        }
    }

    fn semantic_tokens(&mut self, request: Request) -> DispatchOutcome {
        let id = request.id;
        let params = match serde_json::from_value::<SemanticTokensParams>(request.params) {
            Ok(params) => params,
            Err(_) => {
                return immediate_response(Response::new_err(
                    id,
                    ErrorCode::InvalidParams as i32,
                    INVALID_PARAMS.to_owned(),
                ));
            }
        };
        let Some(document) = self.documents.get(&params.text_document.uri) else {
            return immediate_response(Response::new_err(
                id,
                ErrorCode::RequestFailed as i32,
                DOCUMENT_NOT_OPEN.to_owned(),
            ));
        };
        let uri = params.text_document.uri;
        let revision = document.revision();
        let (input, policy_path) = match document.kind() {
            DocumentKind::Dependency => {
                return immediate_response(Response::new_err(
                    id,
                    ErrorCode::RequestFailed as i32,
                    DOCUMENT_NOT_OPEN.to_owned(),
                ));
            }
            DocumentKind::EventSchema => (
                SemanticInput::EventSchema {
                    source: document.text_snapshot(),
                },
                None,
            ),
            DocumentKind::Policy => {
                let path = document.path().to_path_buf();
                let Some(snapshot) = self
                    .policy_diagnostics
                    .semantic_snapshot(&path, &self.documents)
                else {
                    return immediate_response(Response::new_err(
                        id,
                        ErrorCode::RequestFailed as i32,
                        DOCUMENT_NOT_OPEN.to_owned(),
                    ));
                };
                match snapshot {
                    SemanticSnapshot::Standalone { policy } => {
                        (SemanticInput::PolicyStandalone { policy }, None)
                    }
                    SemanticSnapshot::Project {
                        policy,
                        event_schema,
                        providers,
                        macros,
                    } => (
                        SemanticInput::PolicyProject {
                            policy,
                            event_schema,
                            providers,
                            macros,
                        },
                        Some(path),
                    ),
                    SemanticSnapshot::Pending {
                        generation,
                        identity,
                    } => (
                        SemanticInput::PolicyPending {
                            generation,
                            identity,
                        },
                        Some(path),
                    ),
                    SemanticSnapshot::Unavailable { policy } => {
                        (SemanticInput::PolicyLexical { policy }, Some(path))
                    }
                }
            }
        };

        match self.scheduler.schedule_semantic(SemanticWork {
            request_id: id.clone(),
            uri,
            revision,
            policy_path,
            input,
        }) {
            Ok(()) => DispatchOutcome::default(),
            Err(error) => {
                eprintln!("semantic analysis could not be scheduled: {error:?}");
                immediate_response(Response::new_err(
                    id,
                    ErrorCode::ServerCancelled as i32,
                    SERVER_CANCELLED.to_owned(),
                ))
            }
        }
    }

    fn handle_notification(&mut self, notification: Notification) -> DispatchOutcome {
        if notification.method == EXIT {
            if serde_json::from_value::<()>(notification.params).is_err() {
                eprintln!("ignoring exit notification with invalid params");
                return DispatchOutcome::default();
            }
            return DispatchOutcome {
                exit_code: Some(self.lifecycle.exit_code()),
                ..DispatchOutcome::default()
            };
        }

        if self.lifecycle == Lifecycle::AwaitInitialized && notification.method == INITIALIZED {
            let is_empty_object = notification
                .params
                .as_object()
                .is_some_and(serde_json::Map::is_empty);
            if !is_empty_object
                || serde_json::from_value::<InitializedParams>(notification.params).is_err()
            {
                eprintln!("ignoring initialized notification with invalid params");
                return DispatchOutcome::default();
            }
            self.lifecycle.initialized();
            let requests = self.watch_registration_request().into_iter().collect();
            return DispatchOutcome {
                requests,
                ..DispatchOutcome::default()
            };
        }

        if self.lifecycle != Lifecycle::Running {
            return DispatchOutcome::default();
        }

        match notification.method.as_str() {
            DID_OPEN => self.did_open(notification.params),
            DID_CHANGE => self.did_change(notification.params),
            DID_CLOSE => self.did_close(notification.params),
            DID_CHANGE_WATCHED_FILES => self.did_change_watched_files(notification.params),
            CANCEL_REQUEST => self.cancel_request(notification.params),
            _ => DispatchOutcome::default(),
        }
    }

    fn did_open(&mut self, params: serde_json::Value) -> DispatchOutcome {
        let params = match serde_json::from_value::<DidOpenTextDocumentParams>(params) {
            Ok(params) => params,
            Err(error) => {
                eprintln!("ignoring didOpen notification with invalid params: {error}");
                return DispatchOutcome::default();
            }
        };
        let uri = params.text_document.uri.clone();
        let version = params.text_document.version;
        let policy_diagnostics = &self.policy_diagnostics;
        if let Err(error) = self.documents.open(params.text_document, |path| {
            policy_diagnostics.is_explicit_dependency_path(path)
        }) {
            eprintln!("ignoring didOpen for {}: {error}", uri.as_str());
            return if error == DocumentError::UnsupportedDocument && is_dw_uri(&uri) {
                DispatchOutcome {
                    notifications: publish_diagnostics_notifications(vec![
                        self.policy_diagnostics.invalid_policy_opened(
                            uri,
                            version,
                            "policy URI is not an unambiguous absolute file URI".to_owned(),
                        ),
                    ]),
                    ..DispatchOutcome::default()
                }
            } else {
                DispatchOutcome::default()
            };
        }
        let document = self.documents.get(&uri).expect("document was just opened");
        let path = document.path().to_path_buf();
        let kind = document.kind();
        let schema = self.schema_work(&uri);
        let actions = self
            .policy_diagnostics
            .document_opened(&path, kind, &self.documents);
        let mut outcome = DispatchOutcome::default();
        if let Some(work) = schema {
            self.schedule_schema(work, &mut outcome);
        }
        self.apply_diagnostic_actions(actions, &mut outcome);
        outcome
    }

    fn did_change(&mut self, params: serde_json::Value) -> DispatchOutcome {
        let params = match serde_json::from_value::<DidChangeTextDocumentParams>(params) {
            Ok(params) => params,
            Err(error) => {
                eprintln!("ignoring didChange notification with invalid params: {error}");
                return DispatchOutcome::default();
            }
        };
        let uri = params.text_document.uri.clone();
        if let Err(error) = self
            .documents
            .change(params.text_document, params.content_changes)
        {
            eprintln!("ignoring didChange for {}: {error}", uri.as_str());
            return DispatchOutcome::default();
        }
        let path = self
            .documents
            .get(&uri)
            .expect("document was just changed")
            .path()
            .to_path_buf();
        let mut outcome = DispatchOutcome {
            responses: cancellation_responses(
                self.scheduler.invalidate_semantics(&uri),
                ErrorCode::ContentModified,
                CONTENT_MODIFIED,
            ),
            ..DispatchOutcome::default()
        };
        if let Some(work) = self.schema_work(&uri) {
            self.schedule_schema(work, &mut outcome);
        }
        let actions = self
            .policy_diagnostics
            .document_changed(&path, &self.documents);
        self.apply_diagnostic_actions(actions, &mut outcome);
        outcome
    }

    fn did_close(&mut self, params: serde_json::Value) -> DispatchOutcome {
        let params = match serde_json::from_value::<DidCloseTextDocumentParams>(params) {
            Ok(params) => params,
            Err(error) => {
                eprintln!("ignoring didClose notification with invalid params: {error}");
                return DispatchOutcome::default();
            }
        };
        let Some(document) = self.documents.get(&params.text_document.uri) else {
            if let Some(publication) = self
                .policy_diagnostics
                .invalid_policy_closed(&params.text_document.uri)
            {
                return DispatchOutcome {
                    notifications: publish_diagnostics_notifications(vec![publication]),
                    ..DispatchOutcome::default()
                };
            }
            eprintln!(
                "ignoring didClose for {}: document is not open",
                params.text_document.uri.as_str()
            );
            return DispatchOutcome::default();
        };
        let path = document.path().to_path_buf();
        let version = document.version();
        let kind = document.kind();
        let uri = params.text_document.uri.clone();
        if let Err(error) = self.documents.close(&params.text_document.uri) {
            eprintln!(
                "ignoring didClose for {}: {error}",
                params.text_document.uri.as_str()
            );
            return DispatchOutcome::default();
        }
        let mut outcome = DispatchOutcome {
            responses: cancellation_responses(
                self.scheduler.invalidate_semantics(&uri),
                ErrorCode::ContentModified,
                CONTENT_MODIFIED,
            ),
            ..DispatchOutcome::default()
        };
        self.dirty_schema_diagnostics.remove(&uri);
        self.scheduler.cancel_schema(&uri);
        let mut publications = Vec::new();
        if kind == DocumentKind::EventSchema {
            publications.push(PublishDiagnosticsParams::new(
                uri.clone(),
                Vec::new(),
                Some(version),
            ));
        }
        let actions = self
            .policy_diagnostics
            .document_closed(&path, uri, version, &self.documents);
        publications.extend(actions.publications.iter().cloned());
        outcome
            .notifications
            .extend(publish_diagnostics_notifications(publications));
        let actions = DiagnosticActions {
            publications: Vec::new(),
            ..actions
        };
        self.apply_diagnostic_actions(actions, &mut outcome);
        outcome
    }

    fn did_change_watched_files(&mut self, params: serde_json::Value) -> DispatchOutcome {
        let params = match serde_json::from_value::<DidChangeWatchedFilesParams>(params) {
            Ok(params) => params,
            Err(error) => {
                eprintln!("ignoring didChangeWatchedFiles with invalid params: {error}");
                return DispatchOutcome::default();
            }
        };
        #[cfg(feature = "test-control")]
        let mut observations = Vec::new();
        for event in &params.changes {
            if let Ok(path) = dogwood_lsp::project::file_uri_to_path(&event.uri) {
                #[cfg(feature = "test-control")]
                if let Some(observation) =
                    self.record_watch_event(event.uri.clone(), path.clone(), event.typ)
                {
                    observations.push(observation);
                }
                self.documents.note_disk_change(path);
            }
        }
        let actions = self
            .policy_diagnostics
            .watched_files(&params.changes, &self.documents);
        let mut outcome = DispatchOutcome::default();
        self.apply_diagnostic_actions(actions, &mut outcome);
        #[cfg(feature = "test-control")]
        if self.watch_notifications_enabled() {
            outcome.notifications.extend(
                observations
                    .into_iter()
                    .map(test_control::watch_observed_notification),
            );
        }
        outcome
    }

    fn watch_registration_request(&mut self) -> Option<Request> {
        if !self.watched_files_dynamic_registration {
            #[cfg(feature = "test-control")]
            self.record_watch_registration("unsupported");
            return None;
        }
        #[cfg(feature = "test-control")]
        self.record_watch_registration("pending");
        let (workspace_roots, explicit_dependencies) = self.policy_diagnostics.watch_targets();
        let request_id = RequestId::from(WATCH_REGISTRATION_REQUEST_ID.to_owned());
        self.pending_watch_registration = Some(request_id.clone());
        Some(watchers::registration_request(
            request_id,
            workspace_roots,
            explicit_dependencies,
            self.watched_files_relative_pattern_support,
        ))
    }

    fn schema_work(&self, uri: &Uri) -> Option<SchemaDiagnosticWork> {
        let document = self.documents.get(uri)?;
        (document.kind() == DocumentKind::EventSchema).then(|| SchemaDiagnosticWork {
            uri: uri.clone(),
            version: document.version(),
            revision: document.revision(),
            source: document.text_snapshot(),
        })
    }

    fn handle_client_response(&mut self, response: Response) -> DispatchOutcome {
        if self.pending_watch_registration.as_ref() != Some(&response.id) {
            eprintln!("ignoring unexpected client response: {}", response.id);
            return DispatchOutcome::default();
        }
        self.pending_watch_registration = None;
        let registration_rejected = match response.response_result {
            Ok(serde_json::Value::Null) => false,
            Ok(_) => {
                eprintln!("client/registerCapability returned an unexpected non-null result");
                true
            }
            Err(error) => {
                eprintln!(
                    "client/registerCapability failed with code {}: {}",
                    error.code, error.message
                );
                true
            }
        };
        let actions = if registration_rejected {
            #[cfg(feature = "test-control")]
            self.record_watch_registration("failed");
            self.policy_diagnostics
                .watch_registration_failed(&self.documents)
        } else if self.watched_files_relative_pattern_support {
            #[cfg(feature = "test-control")]
            self.record_watch_registration("succeeded");
            self.policy_diagnostics
                .watch_registration_succeeded(&self.documents)
        } else {
            #[cfg(feature = "test-control")]
            self.record_watch_registration("succeeded");
            DiagnosticActions::default()
        };
        let mut outcome = DispatchOutcome::default();
        self.apply_diagnostic_actions(actions, &mut outcome);
        outcome
    }

    fn cancel_request(&mut self, params: serde_json::Value) -> DispatchOutcome {
        let params = match serde_json::from_value::<CancelParams>(params) {
            Ok(params) => params,
            Err(error) => {
                eprintln!("ignoring $/cancelRequest with invalid params: {error}");
                return DispatchOutcome::default();
            }
        };
        let request_id = match params.id {
            NumberOrString::Number(id) => RequestId::from(id),
            NumberOrString::String(id) => RequestId::from(id),
        };
        if !self.scheduler.cancel_request(&request_id) {
            return DispatchOutcome::default();
        }
        DispatchOutcome {
            responses: vec![Response::new_err(
                request_id,
                ErrorCode::RequestCanceled as i32,
                REQUEST_CANCELLED.to_owned(),
            )],
            ..DispatchOutcome::default()
        }
    }

    fn schedule_schema(
        &mut self,
        work: SchemaDiagnosticWork,
        outcome: &mut DispatchOutcome,
    ) -> bool {
        let uri = work.uri.clone();
        let result = self.scheduler.schedule_schema(work);
        self.append_diagnostic_cancellations(&result, outcome);
        if result.scheduled {
            self.dirty_schema_diagnostics.remove(&uri);
        } else {
            self.dirty_schema_diagnostics.insert(uri);
        }
        result.scheduled
    }

    fn schedule_policy(
        &mut self,
        validation: policy_diagnostics::PolicyValidationWork,
        outcome: &mut DispatchOutcome,
    ) -> bool {
        let path = validation.policy_path.clone();
        let generation = validation.generation;
        let result = self.scheduler.schedule_policy(validation);
        self.append_diagnostic_cancellations(&result, outcome);
        if result.scheduled {
            self.dirty_policy_diagnostics.remove(&path);
            self.policy_diagnostics
                .validation_scheduled(&path, generation);
        } else {
            self.dirty_policy_diagnostics.insert(path);
        }
        result.scheduled
    }

    fn apply_diagnostic_actions(
        &mut self,
        actions: DiagnosticActions,
        outcome: &mut DispatchOutcome,
    ) {
        for policy in &actions.invalidated_policies {
            self.dirty_policy_diagnostics.remove(policy);
            self.scheduler.cancel_policy(policy);
        }
        outcome
            .notifications
            .extend(publish_diagnostics_notifications(actions.publications));
        for policy in &actions.invalidated_policies {
            outcome.responses.extend(cancellation_responses(
                self.scheduler.invalidate_policy_semantics(policy),
                ErrorCode::ContentModified,
                CONTENT_MODIFIED,
            ));
        }
        for policy in actions.pending_validations {
            self.dirty_policy_diagnostics.insert(policy);
        }
    }

    fn append_diagnostic_cancellations(
        &self,
        result: &DiagnosticSchedule,
        outcome: &mut DispatchOutcome,
    ) {
        outcome.responses.extend(cancellation_responses(
            result.cancelled_semantics.clone(),
            ErrorCode::ServerCancelled,
            SERVER_CANCELLED,
        ));
    }

    fn finish_dispatch(&mut self, mut outcome: DispatchOutcome) -> DispatchOutcome {
        if self.lifecycle != Lifecycle::Shutdown {
            self.retry_dirty_diagnostics(&mut outcome);
        }
        if self.analysis_idle() {
            outcome.responses.append(&mut self.pending_barriers);
        }
        outcome
    }

    fn retry_dirty_diagnostics(&mut self, outcome: &mut DispatchOutcome) {
        while let Some(uri) = self.dirty_schema_diagnostics.first().cloned() {
            let Some(work) = self.schema_work(&uri) else {
                self.dirty_schema_diagnostics.remove(&uri);
                continue;
            };
            if !self.schedule_schema(work, outcome) {
                return;
            }
        }

        while let Some(path) = self.dirty_policy_diagnostics.first().cloned() {
            if !self.scheduler.diagnostic_capacity_available() {
                return;
            }
            let Some(validation) = self
                .policy_diagnostics
                .materialize_validation(&path, &self.documents)
            else {
                self.dirty_policy_diagnostics.remove(&path);
                continue;
            };
            match validation {
                MaterializedPolicyValidation::Work(validation) => {
                    if !self.schedule_policy(validation, outcome) {
                        return;
                    }
                }
                MaterializedPolicyValidation::Failure(failure) => {
                    self.dirty_policy_diagnostics.remove(&path);
                    self.scheduler.resolve_failed_policy_semantics(&failure);
                    outcome
                        .notifications
                        .extend(publish_diagnostics_notifications(vec![failure.publication]));
                }
            }
        }
    }

    fn analysis_idle(&self) -> bool {
        self.scheduler.is_idle()
            && self.dirty_policy_diagnostics.is_empty()
            && self.dirty_schema_diagnostics.is_empty()
    }

    fn handle_work_output(&mut self, output: WorkOutput, outcome: &mut DispatchOutcome) {
        match output {
            WorkOutput::Policy(result) => {
                if let Some(publication) = self.policy_diagnostics.complete_validation(*result) {
                    outcome
                        .notifications
                        .extend(publish_diagnostics_notifications(vec![publication]));
                }
            }
            WorkOutput::Schema(result) => {
                let current = self.documents.get(&result.uri);
                if current.is_some_and(|document| {
                    document.kind() == DocumentKind::EventSchema
                        && document.revision() == result.revision
                }) {
                    outcome
                        .notifications
                        .extend(publish_diagnostics_notifications(vec![result.publication]));
                }
            }
            WorkOutput::Semantic(result) => {
                let current = self.documents.get(&result.uri);
                if current.is_none_or(|document| document.revision() != result.revision) {
                    outcome.responses.push(Response::new_err(
                        result.request_id,
                        ErrorCode::ContentModified as i32,
                        CONTENT_MODIFIED.to_owned(),
                    ));
                    return;
                }
                let response = match result.result {
                    Ok(tokens) => Response::new_ok(result.request_id, tokens),
                    Err(SemanticFailure::TokenLimit(error)) => {
                        eprintln!("semantic token analysis failed: {error}");
                        Response::new_err(
                            result.request_id,
                            ErrorCode::RequestFailed as i32,
                            SEMANTIC_TOKEN_LIMIT_EXCEEDED.to_owned(),
                        )
                    }
                    Err(SemanticFailure::Internal(error)) => {
                        eprintln!("semantic token analysis failed: {error}");
                        Response::new_err(
                            result.request_id,
                            ErrorCode::InternalError as i32,
                            INTERNAL_ERROR.to_owned(),
                        )
                    }
                };
                outcome.responses.push(response);
            }
        }
    }
}

fn publish_diagnostics_notifications(
    publications: Vec<PublishDiagnosticsParams>,
) -> Vec<Notification> {
    publications
        .into_iter()
        .map(|params| Notification::new(PUBLISH_DIAGNOSTICS.to_owned(), params))
        .collect()
}

fn immediate_response(response: Response) -> DispatchOutcome {
    DispatchOutcome {
        response: Some(response),
        ..DispatchOutcome::default()
    }
}

fn cancellation_responses(
    request_ids: Vec<RequestId>,
    code: ErrorCode,
    message: &str,
) -> Vec<Response> {
    request_ids
        .into_iter()
        .map(|id| Response::new_err(id, code as i32, message.to_owned()))
        .collect()
}

fn error_response(request: Request, code: i32, message: &str) -> Response {
    Response::new_err(request.id, code, message.to_owned())
}

// dogwood-lsp handles Unix paths and file URIs only, so its tests run on Unix.
#[cfg(all(test, unix))]
mod tests {
    use std::path::PathBuf;
    use std::str::FromStr;

    use lsp_server::{ErrorCode, Message, Notification, Request, Response};
    use lsp_types::Uri;
    use serde_json::{Value, json};

    use super::{
        DID_CHANGE, DID_CLOSE, DID_OPEN, DOCUMENT_NOT_OPEN, DUPLICATE_INITIALIZE, EXIT, INITIALIZE,
        INITIALIZED, INVALID_PARAMS, METHOD_NOT_FOUND, SEMANTIC_TOKENS_FULL,
        SERVER_NOT_INITIALIZED, SERVER_SHUT_DOWN, SHUTDOWN, Server, WATCH_REGISTRATION_REQUEST_ID,
    };
    use crate::protocol::lifecycle::Lifecycle;
    use crate::protocol::watchers::{REGISTER_CAPABILITY, watched_file_watchers};

    fn request(id: i32, method: &str, params: Value) -> Request {
        Request {
            id: id.into(),
            method: method.to_owned(),
            params,
        }
    }

    fn notification(method: &str, params: Value) -> Notification {
        Notification {
            method: method.to_owned(),
            params,
        }
    }

    fn initialize(server: &mut Server) -> Response {
        response(server.handle_message(Message::Request(request(
            1,
            INITIALIZE,
            json!({"capabilities": {}}),
        ))))
    }

    fn running_server() -> Server {
        let mut server = Server::default();
        initialize(&mut server);
        let outcome =
            server.handle_message(Message::Notification(notification(INITIALIZED, json!({}))));
        assert!(outcome.response.is_none());
        assert!(outcome.exit_code.is_none());
        assert_eq!(server.lifecycle, Lifecycle::Running);
        server
    }

    fn response(outcome: super::DispatchOutcome) -> Response {
        assert!(outcome.exit_code.is_none());
        outcome.response.expect("request should produce a response")
    }

    fn async_response(server: &mut Server, request: Request) -> Response {
        let outcome = server.handle_message(Message::Request(request));
        if let Some(response) = outcome.response {
            return response;
        }
        let events = server.async_events();
        loop {
            let event = events
                .recv_timeout(std::time::Duration::from_secs(5))
                .expect("asynchronous request should complete");
            let mut outcome = server.handle_async_event(event);
            if let Some(response) = outcome.response {
                return response;
            }
            if let Some(response) = outcome.responses.pop() {
                return response;
            }
        }
    }

    fn assert_error(response: Response, code: i32, message: &str) {
        let error = response
            .response_result
            .expect_err("expected error response");
        assert_eq!(error.code, code);
        assert_eq!(error.message, message);
        assert_eq!(error.data, None);
    }

    fn assert_ok(response: Response, expected: Value) {
        let result = response
            .response_result
            .expect("expected successful response");
        assert_eq!(result, expected);
    }

    fn uri(value: &str) -> Uri {
        Uri::from_str(value).expect("test URI should be valid")
    }

    fn open(server: &mut Server, document_uri: &Uri, version: i32, text: &str) {
        let outcome = server.handle_message(Message::Notification(notification(
            DID_OPEN,
            json!({
                "textDocument": {
                    "uri": document_uri,
                    "languageId": "dogwood",
                    "version": version,
                    "text": text
                }
            }),
        )));
        assert!(outcome.response.is_none());
        assert!(outcome.exit_code.is_none());
    }

    fn tokens_request(id: i32, document_uri: &Uri) -> Request {
        request(
            id,
            SEMANTIC_TOKENS_FULL,
            json!({"textDocument": {"uri": document_uri}}),
        )
    }

    #[test]
    fn initialize_waits_for_initialized_and_rejects_duplicates() {
        let mut server = Server::default();
        let initialize_response = initialize(&mut server);
        assert!(initialize_response.response_result.is_ok());
        assert_eq!(server.lifecycle, Lifecycle::AwaitInitialized);

        assert_error(
            response(server.handle_message(Message::Request(request(2, "unknown", Value::Null)))),
            ErrorCode::ServerNotInitialized as i32,
            SERVER_NOT_INITIALIZED,
        );
        assert_error(
            response(server.handle_message(Message::Request(request(
                3,
                INITIALIZE,
                json!({"capabilities": {}}),
            )))),
            ErrorCode::InvalidRequest as i32,
            DUPLICATE_INITIALIZE,
        );

        server.handle_message(Message::Notification(notification(INITIALIZED, json!({}))));
        assert_eq!(server.lifecycle, Lifecycle::Running);
        assert_error(
            response(server.handle_message(Message::Request(request(
                4,
                INITIALIZE,
                json!({"capabilities": {}}),
            )))),
            ErrorCode::InvalidRequest as i32,
            DUPLICATE_INITIALIZE,
        );
    }

    #[test]
    fn lifecycle_errors_take_precedence() {
        let document_uri = uri("file:///policy.dw");
        let mut server = Server::default();
        assert_error(
            response(server.handle_message(Message::Request(tokens_request(1, &document_uri)))),
            ErrorCode::ServerNotInitialized as i32,
            SERVER_NOT_INITIALIZED,
        );

        let mut server = running_server();
        let shutdown_response =
            response(server.handle_message(Message::Request(request(2, SHUTDOWN, Value::Null))));
        assert_ok(shutdown_response, Value::Null);
        assert_eq!(server.lifecycle, Lifecycle::Shutdown);

        assert_error(
            response(server.handle_message(Message::Request(request(
                3,
                "unknown",
                json!({"malformed": true}),
            )))),
            ErrorCode::InvalidRequest as i32,
            SERVER_SHUT_DOWN,
        );
    }

    #[test]
    fn malformed_initialize_does_not_advance_lifecycle() {
        let mut server = Server::default();
        assert_error(
            response(server.handle_message(Message::Request(request(
                1,
                INITIALIZE,
                json!({"missing": "capabilities"}),
            )))),
            ErrorCode::InvalidParams as i32,
            INVALID_PARAMS,
        );
        assert_eq!(server.lifecycle, Lifecycle::PreInitialize);
    }

    #[test]
    fn shutdown_accepts_omitted_and_null_params() {
        let omitted: Request = serde_json::from_value(json!({
            "id": 1,
            "method": SHUTDOWN
        }))
        .expect("request with omitted params should deserialize");
        assert!(omitted.params.is_null());

        for shutdown_request in [omitted, request(2, SHUTDOWN, Value::Null)] {
            let mut server = running_server();
            let shutdown_response =
                response(server.handle_message(Message::Request(shutdown_request)));
            assert_ok(shutdown_response, Value::Null);
            assert_eq!(server.lifecycle, Lifecycle::Shutdown);
        }
    }

    #[test]
    fn invalid_shutdown_params_do_not_change_state() {
        let mut server = running_server();
        assert_error(
            response(server.handle_message(Message::Request(request(1, SHUTDOWN, json!({}))))),
            ErrorCode::InvalidParams as i32,
            INVALID_PARAMS,
        );
        assert_eq!(server.lifecycle, Lifecycle::Running);
    }

    #[test]
    fn exit_status_depends_on_shutdown_and_invalid_params_are_ignored() {
        let mut pre_initialize = Server::default();
        let omitted: Notification = serde_json::from_value(json!({"method": EXIT}))
            .expect("notification with omitted params should deserialize");
        assert!(omitted.params.is_null());
        let outcome = pre_initialize.handle_message(Message::Notification(omitted));
        assert_eq!(outcome.exit_code, Some(1));

        let mut running = running_server();
        let invalid = running.handle_message(Message::Notification(notification(EXIT, json!({}))));
        assert!(invalid.response.is_none());
        assert_eq!(invalid.exit_code, None);
        assert_eq!(running.lifecycle, Lifecycle::Running);

        let running_exit =
            running.handle_message(Message::Notification(notification(EXIT, Value::Null)));
        assert!(running_exit.response.is_none());
        assert_eq!(running_exit.exit_code, Some(1));

        let mut shutdown = running_server();
        shutdown.handle_message(Message::Request(request(2, SHUTDOWN, Value::Null)));
        let shutdown_exit =
            shutdown.handle_message(Message::Notification(notification(EXIT, Value::Null)));
        assert!(shutdown_exit.response.is_none());
        assert_eq!(shutdown_exit.exit_code, Some(0));
    }

    #[test]
    fn initialized_notification_requires_the_awaiting_state_and_valid_params() {
        let mut server = Server::default();
        server.handle_message(Message::Notification(notification(INITIALIZED, json!({}))));
        assert_eq!(server.lifecycle, Lifecycle::PreInitialize);

        initialize(&mut server);
        server.handle_message(Message::Notification(notification(
            INITIALIZED,
            json!({"invalid": true}),
        )));
        assert_eq!(server.lifecycle, Lifecycle::AwaitInitialized);

        server.handle_message(Message::Notification(notification(INITIALIZED, json!({}))));
        assert_eq!(server.lifecycle, Lifecycle::Running);
    }

    #[test]
    fn running_requests_apply_method_params_then_document_checks() {
        let mut server = running_server();
        let document_uri = uri("file:///missing.dw");

        assert_error(
            response(server.handle_message(Message::Request(request(
                1,
                "unknown",
                json!({"anything": true}),
            )))),
            ErrorCode::MethodNotFound as i32,
            METHOD_NOT_FOUND,
        );
        assert_error(
            response(server.handle_message(Message::Request(request(
                2,
                SEMANTIC_TOKENS_FULL,
                json!({"notTextDocument": true}),
            )))),
            ErrorCode::InvalidParams as i32,
            INVALID_PARAMS,
        );
        assert_error(
            response(server.handle_message(Message::Request(tokens_request(3, &document_uri)))),
            ErrorCode::RequestFailed as i32,
            DOCUMENT_NOT_OPEN,
        );
    }

    #[test]
    fn document_notifications_drive_empty_token_results_for_blank_source() {
        let mut server = running_server();
        let document_uri = uri("file:///policy.dw");
        open(&mut server, &document_uri, 1, " \n\t");

        let first = async_response(&mut server, tokens_request(1, &document_uri));
        assert_ok(first, json!({"data": []}));

        server.handle_message(Message::Notification(notification(
            DID_CHANGE,
            json!({
                "textDocument": {"uri": document_uri, "version": 2},
                "contentChanges": [{"text": ""}]
            }),
        )));
        let second = async_response(&mut server, tokens_request(2, &document_uri));
        assert_ok(second, json!({"data": []}));

        server.handle_message(Message::Notification(notification(
            DID_CLOSE,
            json!({"textDocument": {"uri": document_uri}}),
        )));
        assert_error(
            response(server.handle_message(Message::Request(tokens_request(3, &document_uri)))),
            ErrorCode::RequestFailed as i32,
            DOCUMENT_NOT_OPEN,
        );
    }

    #[test]
    fn unsupported_open_does_not_create_a_document() {
        let mut server = running_server();
        let document_uri = uri("file:///policy.txt");
        open(&mut server, &document_uri, 1, "permit();");

        assert_error(
            response(server.handle_message(Message::Request(tokens_request(1, &document_uri)))),
            ErrorCode::RequestFailed as i32,
            DOCUMENT_NOT_OPEN,
        );
    }

    #[test]
    fn dependency_documents_do_not_expand_the_semantic_token_contract() {
        let mut server = running_server();
        let schema_uri = uri("file:///actions.cedarschema");
        open(&mut server, &schema_uri, 1, "namespace App {}");

        assert_error(
            response(server.handle_message(Message::Request(tokens_request(1, &schema_uri)))),
            ErrorCode::RequestFailed as i32,
            DOCUMENT_NOT_OPEN,
        );
    }

    #[test]
    fn watcher_patterns_escape_paths_and_deduplicate_nested_coverage() {
        let root = PathBuf::from("/workspace/[root]");
        let watchers = watched_file_watchers(
            vec![root.clone(), root.join("nested"), root.clone()],
            vec![
                PathBuf::from("/outside/schema?.txt"),
                PathBuf::from("/outside/schema?.txt"),
                root.join("events.dwschema"),
            ],
            true,
        );

        assert_eq!(
            serde_json::to_value(watchers).unwrap(),
            json!([
                {"globPattern": "/workspace/[[]root[]]/**/*.cedarschema", "kind": 7},
                {"globPattern": "/workspace/[[]root[]]/**/events.dwschema", "kind": 7},
                {"globPattern": "/workspace/[[]root[]]/**/macros.dw", "kind": 7},
                {"globPattern": "/workspace/[[]root[]]/**/providers.json", "kind": 7},
                {
                    "globPattern": {
                        "baseUri": "file:///outside",
                        "pattern": "schema[?].txt"
                    },
                    "kind": 7
                }
            ])
        );

        let without_relative_patterns = watched_file_watchers(
            vec![root],
            vec![PathBuf::from("/outside/schema?.txt")],
            false,
        );
        assert!(
            serde_json::to_value(without_relative_patterns)
                .unwrap()
                .as_array()
                .unwrap()
                .iter()
                .all(|watcher| watcher["globPattern"].is_string())
        );
    }

    #[test]
    fn dynamic_watcher_registration_is_sent_once_after_initialized_and_consumed() {
        let mut server = Server::default();
        let initialize = server.handle_message(Message::Request(request(
            1,
            INITIALIZE,
            json!({
                "capabilities": {
                    "workspace": {
                        "didChangeWatchedFiles": {
                            "dynamicRegistration": true,
                            "relativePatternSupport": true
                        }
                    }
                },
                "rootUri": "file:///workspace"
            }),
        )));
        assert!(initialize.requests.is_empty());
        assert!(initialize.response.unwrap().response_result.is_ok());

        let initialized =
            server.handle_message(Message::Notification(notification(INITIALIZED, json!({}))));
        assert_eq!(initialized.requests.len(), 1);
        assert_eq!(initialized.requests[0].method, REGISTER_CAPABILITY);
        assert_eq!(
            initialized.requests[0].id,
            WATCH_REGISTRATION_REQUEST_ID.to_owned().into()
        );
        assert_eq!(server.lifecycle, Lifecycle::Running);

        let duplicate =
            server.handle_message(Message::Notification(notification(INITIALIZED, json!({}))));
        assert!(duplicate.requests.is_empty());

        let response = server.handle_message(Message::Response(Response::new_ok(
            WATCH_REGISTRATION_REQUEST_ID.to_owned().into(),
            (),
        )));
        assert!(response.requests.is_empty());
        assert!(server.pending_watch_registration.is_none());
        assert_eq!(server.lifecycle, Lifecycle::Running);
    }
}
