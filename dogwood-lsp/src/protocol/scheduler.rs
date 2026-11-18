#[cfg(feature = "test-control")]
use std::collections::BTreeMap;
use std::collections::VecDeque;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
#[cfg(feature = "test-control")]
use std::sync::{Condvar, Mutex};
use std::thread::{self, JoinHandle};

use crossbeam_channel::{Receiver, Sender, TrySendError, bounded, unbounded};
use dogwood_lsp::{
    analysis,
    diagnostics::{SourceDocument, project_event_schema_outcome},
    frontend::parse_event_schema,
};
use lsp_server::RequestId;
use lsp_types::{PublishDiagnosticsParams, SemanticTokens, Uri};

use super::encoding::{EncodingError, encode_tokens};
use super::policy_diagnostics::{
    PolicyValidationFailure, PolicyValidationResult, PolicyValidationWork, run_policy_validation,
};
use super::snapshots::{BundleIdentity, BundleSnapshot};

#[cfg(not(feature = "test-control"))]
const MAX_QUEUED_WORK: usize = 1024;
#[cfg(feature = "test-control")]
const TEST_MAX_QUEUED_WORK: usize = 4;
const WORKER_NAME: &str = "dogwood-lsp-analysis";
#[cfg(feature = "test-control")]
pub(crate) const TEST_CONTROL_ENV: &str = "DOGWOOD_LSP_TEST_CONTROL";

#[cfg(feature = "test-control")]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum Checkpoint {
    Validation,
    Semantic,
}

#[cfg(feature = "test-control")]
impl Checkpoint {
    pub(crate) fn parse(value: &str) -> Option<Self> {
        match value {
            "validation" => Some(Self::Validation),
            "semantic" => Some(Self::Semantic),
            _ => None,
        }
    }

    pub(crate) const fn name(self) -> &'static str {
        match self {
            Self::Validation => "validation",
            Self::Semantic => "semantic",
        }
    }
}

#[derive(Debug)]
pub(crate) enum AsyncEvent {
    Completion(Box<WorkCompletion>),
    #[cfg(feature = "test-control")]
    TestReached {
        task_id: u64,
        point: Checkpoint,
    },
}

#[derive(Debug)]
pub(crate) struct WorkCompletion {
    task_id: u64,
    output: Option<WorkOutput>,
}

#[derive(Debug)]
pub(crate) enum WorkOutput {
    Policy(Box<PolicyValidationResult>),
    Schema(SchemaDiagnosticResult),
    Semantic(SemanticResult),
}

#[derive(Debug)]
pub(crate) struct SchemaDiagnosticWork {
    pub(crate) uri: Uri,
    pub(crate) version: i32,
    pub(crate) revision: u64,
    pub(crate) source: Arc<str>,
}

#[derive(Debug)]
pub(crate) struct SchemaDiagnosticResult {
    pub(crate) uri: Uri,
    pub(crate) revision: u64,
    pub(crate) publication: PublishDiagnosticsParams,
}

#[derive(Debug)]
pub(crate) enum SemanticInput {
    PolicyStandalone {
        policy: Arc<str>,
    },
    PolicyProject {
        policy: Arc<str>,
        event_schema: Option<Arc<str>>,
        providers: Option<Arc<str>>,
        macros: Option<Arc<str>>,
    },
    PolicyPending {
        generation: u64,
        identity: BundleIdentity,
    },
    PolicyLexical {
        policy: Arc<str>,
    },
    EventSchema {
        source: Arc<str>,
    },
}

#[derive(Debug)]
pub(crate) struct SemanticWork {
    pub(crate) request_id: RequestId,
    pub(crate) uri: Uri,
    pub(crate) revision: u64,
    pub(crate) policy_path: Option<PathBuf>,
    pub(crate) input: SemanticInput,
}

#[derive(Debug)]
pub(crate) struct SemanticResult {
    pub(crate) request_id: RequestId,
    pub(crate) uri: Uri,
    pub(crate) revision: u64,
    pub(crate) result: Result<SemanticTokens, SemanticFailure>,
}

#[derive(Debug)]
pub(crate) enum SemanticFailure {
    TokenLimit(String),
    Internal(String),
}

#[derive(Debug)]
pub(crate) enum ScheduleError {
    QueueFull,
}

#[derive(Debug)]
pub(crate) struct DiagnosticSchedule {
    pub(crate) scheduled: bool,
    pub(crate) cancelled_semantics: Vec<RequestId>,
}

#[cfg(feature = "test-control")]
#[derive(Debug)]
pub(crate) struct SchedulerSnapshotStats {
    pub(crate) retention_limit: usize,
    pub(crate) queued_validation_snapshots: usize,
    pub(crate) active_validation_snapshots: usize,
    pub(crate) queued_policy_paths: Vec<PathBuf>,
    pub(crate) pending_semantic_requests: Vec<SemanticTestObservation>,
    pub(crate) semantic_terminal_outcomes: Vec<SemanticTerminalObservation>,
}

#[cfg(feature = "test-control")]
#[derive(Clone, Debug)]
pub(crate) struct SemanticTestObservation {
    pub(crate) task_id: u64,
    pub(crate) uri: Uri,
    pub(crate) revision: u64,
    pub(crate) state: &'static str,
}

#[cfg(feature = "test-control")]
#[derive(Clone, Debug)]
pub(crate) struct SemanticTerminalObservation {
    pub(crate) task_id: u64,
    pub(crate) uri: Uri,
    pub(crate) revision: u64,
    pub(crate) outcome: &'static str,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum WorkKey {
    Policy(PathBuf),
    Schema(Uri),
    Semantic(RequestId),
}

#[derive(Debug)]
enum Work {
    Policy(PolicyValidationWork),
    Schema(SchemaDiagnosticWork),
    Semantic(SemanticWork),
}

impl Work {
    fn key(&self) -> WorkKey {
        match self {
            Self::Policy(work) => WorkKey::Policy(work.policy_path.clone()),
            Self::Schema(work) => WorkKey::Schema(work.uri.clone()),
            Self::Semantic(work) => WorkKey::Semantic(work.request_id.clone()),
        }
    }

    fn semantic_uri(&self) -> Option<&Uri> {
        match self {
            Self::Semantic(work) => Some(&work.uri),
            Self::Policy(_) | Self::Schema(_) => None,
        }
    }

    fn semantic_policy_path(&self) -> Option<&Path> {
        match self {
            Self::Semantic(work) => work.policy_path.as_deref(),
            Self::Policy(_) | Self::Schema(_) => None,
        }
    }

    #[cfg(feature = "test-control")]
    fn semantic_revision(&self) -> Option<u64> {
        match self {
            Self::Semantic(work) => Some(work.revision),
            Self::Policy(_) | Self::Schema(_) => None,
        }
    }
}

#[derive(Debug)]
struct ScheduledWork {
    task_id: u64,
    cancel: Arc<AtomicBool>,
    work: Work,
}

#[derive(Debug)]
enum WorkerCommand {
    Run(Box<ScheduledWork>),
    Shutdown,
}

#[derive(Debug)]
struct RunningWork {
    task_id: u64,
    key: WorkKey,
    semantic_uri: Option<Uri>,
    #[cfg(feature = "test-control")]
    semantic_revision: Option<u64>,
    semantic_policy_path: Option<PathBuf>,
    cancel: Arc<AtomicBool>,
}

#[derive(Debug)]
pub(crate) struct Scheduler {
    commands: Sender<WorkerCommand>,
    events: Receiver<AsyncEvent>,
    queue: VecDeque<ScheduledWork>,
    running: Option<RunningWork>,
    next_task_id: u64,
    max_queued_work: usize,
    #[cfg(feature = "test-control")]
    test_control: TestControl,
    #[cfg(feature = "test-control")]
    semantic_terminal_outcomes: VecDeque<SemanticTerminalObservation>,
    worker: Option<JoinHandle<()>>,
}

impl Default for Scheduler {
    fn default() -> Self {
        let (commands, command_receiver) = bounded(1);
        let (event_sender, events) = unbounded();
        #[cfg(feature = "test-control")]
        let test_control = TestControl::from_environment();
        #[cfg(feature = "test-control")]
        let worker_control = test_control.clone();
        let worker_events = event_sender.clone();
        let worker = thread::Builder::new()
            .name(WORKER_NAME.to_owned())
            .spawn(move || {
                worker_loop(
                    command_receiver,
                    worker_events,
                    #[cfg(feature = "test-control")]
                    worker_control,
                )
            })
            .expect("analysis worker thread should start");
        Self {
            commands,
            events,
            queue: VecDeque::new(),
            running: None,
            next_task_id: 0,
            max_queued_work: configured_max_queued_work(),
            #[cfg(feature = "test-control")]
            test_control,
            #[cfg(feature = "test-control")]
            semantic_terminal_outcomes: VecDeque::new(),
            worker: Some(worker),
        }
    }
}

#[cfg(feature = "test-control")]
const fn configured_max_queued_work() -> usize {
    TEST_MAX_QUEUED_WORK
}

#[cfg(not(feature = "test-control"))]
const fn configured_max_queued_work() -> usize {
    MAX_QUEUED_WORK
}

impl Scheduler {
    pub(crate) fn events(&self) -> Receiver<AsyncEvent> {
        self.events.clone()
    }

    pub(crate) fn schedule_policy(&mut self, work: PolicyValidationWork) -> DiagnosticSchedule {
        self.cancel_key(&WorkKey::Policy(work.policy_path.clone()));
        self.schedule_diagnostic(Work::Policy(work))
    }

    pub(crate) fn schedule_schema(&mut self, work: SchemaDiagnosticWork) -> DiagnosticSchedule {
        self.cancel_key(&WorkKey::Schema(work.uri.clone()));
        self.schedule_diagnostic(Work::Schema(work))
    }

    pub(crate) fn schedule_semantic(&mut self, work: SemanticWork) -> Result<(), ScheduleError> {
        self.schedule(Work::Semantic(work)).map(|_| ())
    }

    pub(crate) fn cancel_policy(&mut self, path: &Path) {
        self.cancel_key(&WorkKey::Policy(path.to_path_buf()));
    }

    pub(crate) fn cancel_schema(&mut self, uri: &Uri) {
        self.cancel_key(&WorkKey::Schema(uri.clone()));
    }

    pub(crate) fn cancel_request(&mut self, request_id: &RequestId) -> bool {
        self.cancel_key(&WorkKey::Semantic(request_id.clone()))
    }

    pub(crate) fn invalidate_semantics(&mut self, uri: &Uri) -> Vec<RequestId> {
        let mut cancelled = Vec::new();
        #[cfg(feature = "test-control")]
        let mut terminal = Vec::new();
        self.queue.retain(|scheduled| {
            if scheduled.work.semantic_uri() == Some(uri) {
                scheduled.cancel.store(true, Ordering::Release);
                if let WorkKey::Semantic(request_id) = scheduled.work.key() {
                    cancelled.push(request_id);
                    #[cfg(feature = "test-control")]
                    if let Some(observation) = semantic_observation(scheduled, "cancelled") {
                        terminal.push(observation);
                    }
                }
                false
            } else {
                true
            }
        });
        if let Some(running) = &self.running
            && running.semantic_uri.as_ref() == Some(uri)
            && !running.cancel.swap(true, Ordering::AcqRel)
        {
            if let WorkKey::Semantic(request_id) = &running.key {
                cancelled.push(request_id.clone());
            }
            #[cfg(feature = "test-control")]
            {
                self.test_control.wake();
                terminal.extend(running_semantic_observation(running, "cancelled"));
            }
        }
        #[cfg(feature = "test-control")]
        self.record_semantic_terminals(terminal);
        cancelled
    }

    pub(crate) fn invalidate_policy_semantics(&mut self, path: &Path) -> Vec<RequestId> {
        let mut cancelled = Vec::new();
        #[cfg(feature = "test-control")]
        let mut terminal = Vec::new();
        self.queue.retain(|scheduled| {
            if scheduled.work.semantic_policy_path() == Some(path) {
                scheduled.cancel.store(true, Ordering::Release);
                if let WorkKey::Semantic(request_id) = scheduled.work.key() {
                    cancelled.push(request_id);
                    #[cfg(feature = "test-control")]
                    if let Some(observation) = semantic_observation(scheduled, "cancelled") {
                        terminal.push(observation);
                    }
                }
                false
            } else {
                true
            }
        });
        if let Some(running) = &self.running
            && running.semantic_policy_path.as_deref() == Some(path)
            && !running.cancel.swap(true, Ordering::AcqRel)
        {
            if let WorkKey::Semantic(request_id) = &running.key {
                cancelled.push(request_id.clone());
            }
            #[cfg(feature = "test-control")]
            {
                self.test_control.wake();
                terminal.extend(running_semantic_observation(running, "cancelled"));
            }
        }
        #[cfg(feature = "test-control")]
        self.record_semantic_terminals(terminal);
        cancelled
    }

    pub(crate) fn cancel_all(&mut self) -> Vec<RequestId> {
        let mut semantic = Vec::new();
        #[cfg(feature = "test-control")]
        let mut terminal = Vec::new();
        for scheduled in self.queue.drain(..) {
            scheduled.cancel.store(true, Ordering::Release);
            if let WorkKey::Semantic(request_id) = scheduled.work.key() {
                semantic.push(request_id);
                #[cfg(feature = "test-control")]
                if let Some(observation) = semantic_observation(&scheduled, "cancelled") {
                    terminal.push(observation);
                }
            }
        }
        if let Some(running) = &self.running
            && !running.cancel.swap(true, Ordering::AcqRel)
        {
            if let WorkKey::Semantic(request_id) = &running.key {
                semantic.push(request_id.clone());
            }
            #[cfg(feature = "test-control")]
            {
                self.test_control.wake();
                terminal.extend(running_semantic_observation(running, "cancelled"));
            }
        }
        #[cfg(feature = "test-control")]
        self.record_semantic_terminals(terminal);
        semantic
    }

    pub(crate) fn complete(&mut self, completion: WorkCompletion) -> Option<WorkOutput> {
        let running = self.running.take()?;
        if running.task_id != completion.task_id {
            self.running = Some(running);
            return None;
        }
        let cancelled = running.cancel.load(Ordering::Acquire);
        #[cfg(feature = "test-control")]
        if !cancelled {
            let outcome = match completion.output.as_ref() {
                Some(WorkOutput::Semantic(result)) if result.result.is_err() => "failed",
                Some(WorkOutput::Semantic(_)) => "completed",
                _ => "",
            };
            if !outcome.is_empty()
                && let Some(observation) = running_semantic_observation(&running, outcome)
            {
                self.record_semantic_terminal(observation);
            }
        }
        if !cancelled && let Some(WorkOutput::Policy(result)) = completion.output.as_ref() {
            self.resolve_policy_semantics(result);
        }
        self.dispatch();
        (!cancelled).then_some(completion.output).flatten()
    }

    pub(crate) fn is_idle(&self) -> bool {
        self.running.is_none() && self.queue.is_empty()
    }

    #[cfg(feature = "test-control")]
    pub(crate) fn test_control_enabled(&self) -> bool {
        self.test_control.enabled()
    }

    pub(crate) fn diagnostic_capacity_available(&self) -> bool {
        self.queue.len() < self.max_queued_work
            || self
                .queue
                .iter()
                .any(|scheduled| matches!(scheduled.work, Work::Semantic(_)))
    }

    #[cfg(feature = "test-control")]
    pub(crate) fn snapshot_stats(&self) -> SchedulerSnapshotStats {
        let mut pending_semantic_requests = self
            .queue
            .iter()
            .filter_map(|scheduled| semantic_observation(scheduled, "queued"))
            .map(|observation| SemanticTestObservation {
                task_id: observation.task_id,
                uri: observation.uri,
                revision: observation.revision,
                state: "queued",
            })
            .collect::<Vec<_>>();
        if let Some(running) = &self.running
            && let Some(observation) = running_semantic_observation(running, "running")
        {
            pending_semantic_requests.push(SemanticTestObservation {
                task_id: observation.task_id,
                uri: observation.uri,
                revision: observation.revision,
                state: "running",
            });
        }
        pending_semantic_requests.sort_by_key(|request| request.task_id);
        SchedulerSnapshotStats {
            retention_limit: self.max_queued_work,
            queued_validation_snapshots: self
                .queue
                .iter()
                .filter(|scheduled| matches!(scheduled.work, Work::Policy(_)))
                .count(),
            active_validation_snapshots: usize::from(
                self.running
                    .as_ref()
                    .is_some_and(|running| matches!(running.key, WorkKey::Policy(_))),
            ),
            queued_policy_paths: self
                .queue
                .iter()
                .filter_map(|scheduled| match &scheduled.work {
                    Work::Policy(work) => Some(work.policy_path.clone()),
                    Work::Schema(_) | Work::Semantic(_) => None,
                })
                .collect(),
            pending_semantic_requests,
            semantic_terminal_outcomes: self.semantic_terminal_outcomes.iter().cloned().collect(),
        }
    }

    #[cfg(feature = "test-control")]
    pub(crate) fn pause_next(&self, point: Checkpoint) {
        self.test_control.pause_next(point);
    }

    #[cfg(feature = "test-control")]
    pub(crate) fn release(&self, task_id: u64) -> bool {
        self.test_control.release(task_id)
    }

    fn schedule(&mut self, work: Work) -> Result<u64, ScheduleError> {
        if self.queue.len() >= self.max_queued_work {
            return Err(ScheduleError::QueueFull);
        }
        let scheduled = self.new_scheduled_work(work);
        let task_id = scheduled.task_id;
        self.queue.push_back(scheduled);
        self.dispatch();
        Ok(task_id)
    }

    fn schedule_diagnostic(&mut self, work: Work) -> DiagnosticSchedule {
        let mut cancelled_semantics = Vec::new();
        if self.queue.len() >= self.max_queued_work
            && let Some(index) = self
                .queue
                .iter()
                .position(|scheduled| matches!(scheduled.work, Work::Semantic(_)))
        {
            let evicted = self
                .queue
                .remove(index)
                .expect("semantic queue index should remain valid");
            evicted.cancel.store(true, Ordering::Release);
            if let Work::Semantic(semantic) = evicted.work {
                #[cfg(feature = "test-control")]
                {
                    self.record_semantic_terminal(SemanticTerminalObservation {
                        task_id: evicted.task_id,
                        uri: semantic.uri.clone(),
                        revision: semantic.revision,
                        outcome: "cancelled",
                    });
                }
                cancelled_semantics.push(semantic.request_id);
            }
        }
        if self.queue.len() >= self.max_queued_work {
            return DiagnosticSchedule {
                scheduled: false,
                cancelled_semantics,
            };
        }

        let scheduled = self.new_scheduled_work(work);
        let index = self
            .queue
            .iter()
            .position(|queued| matches!(queued.work, Work::Semantic(_)))
            .unwrap_or(self.queue.len());
        self.queue.insert(index, scheduled);
        self.dispatch();
        DiagnosticSchedule {
            scheduled: true,
            cancelled_semantics,
        }
    }

    fn new_scheduled_work(&mut self, work: Work) -> ScheduledWork {
        self.next_task_id = self
            .next_task_id
            .checked_add(1)
            .expect("analysis task counter exhausted");
        let task_id = self.next_task_id;
        ScheduledWork {
            task_id,
            cancel: Arc::new(AtomicBool::new(false)),
            work,
        }
    }

    fn cancel_key(&mut self, key: &WorkKey) -> bool {
        let mut cancelled = false;
        #[cfg(feature = "test-control")]
        let mut terminal = Vec::new();
        self.queue.retain(|scheduled| {
            if scheduled.work.key() == *key {
                scheduled.cancel.store(true, Ordering::Release);
                cancelled = true;
                #[cfg(feature = "test-control")]
                if let Some(observation) = semantic_observation(scheduled, "cancelled") {
                    terminal.push(observation);
                }
                false
            } else {
                true
            }
        });
        if let Some(running) = &self.running
            && running.key == *key
            && !running.cancel.swap(true, Ordering::AcqRel)
        {
            cancelled = true;
            #[cfg(feature = "test-control")]
            {
                self.test_control.wake();
                terminal.extend(running_semantic_observation(running, "cancelled"));
            }
        }
        #[cfg(feature = "test-control")]
        self.record_semantic_terminals(terminal);
        cancelled
    }

    fn dispatch(&mut self) {
        if self.running.is_some() {
            return;
        }
        let Some(scheduled) = self.queue.pop_front() else {
            return;
        };
        let running = RunningWork {
            task_id: scheduled.task_id,
            key: scheduled.work.key(),
            semantic_uri: scheduled.work.semantic_uri().cloned(),
            #[cfg(feature = "test-control")]
            semantic_revision: scheduled.work.semantic_revision(),
            semantic_policy_path: scheduled.work.semantic_policy_path().map(Path::to_path_buf),
            cancel: Arc::clone(&scheduled.cancel),
        };
        match self
            .commands
            .try_send(WorkerCommand::Run(Box::new(scheduled)))
        {
            Ok(()) => self.running = Some(running),
            Err(TrySendError::Full(WorkerCommand::Run(scheduled))) => {
                self.queue.push_front(*scheduled);
            }
            Err(TrySendError::Disconnected(_)) => {
                eprintln!("analysis worker stopped before accepting queued work");
            }
            Err(TrySendError::Full(WorkerCommand::Shutdown)) => {
                unreachable!("dispatch only sends run commands")
            }
        }
    }

    fn resolve_policy_semantics(&mut self, result: &PolicyValidationResult) {
        for scheduled in &mut self.queue {
            let Work::Semantic(work) = &mut scheduled.work else {
                continue;
            };
            let matches_validation = matches!(
                &work.input,
                SemanticInput::PolicyPending {
                    generation,
                    identity,
                    ..
                } if work.policy_path.as_deref() == Some(result.policy_path.as_path())
                    && *generation == result.generation
                    && identity == &result.identity
            );
            if matches_validation {
                work.input = resolved_policy_input(&result.snapshot, result.parser_backed);
            }
        }
    }

    pub(crate) fn resolve_failed_policy_semantics(&mut self, failure: &PolicyValidationFailure) {
        for scheduled in &mut self.queue {
            let Work::Semantic(work) = &mut scheduled.work else {
                continue;
            };
            let matches_validation = matches!(
                &work.input,
                SemanticInput::PolicyPending {
                    generation,
                    identity,
                } if work.policy_path.as_deref() == Some(failure.policy_path.as_path())
                    && *generation == failure.generation
                    && identity == &failure.identity
            );
            if matches_validation {
                work.input = SemanticInput::PolicyLexical {
                    policy: Arc::clone(&failure.policy),
                };
            }
        }
    }

    #[cfg(feature = "test-control")]
    fn record_semantic_terminals(
        &mut self,
        observations: impl IntoIterator<Item = SemanticTerminalObservation>,
    ) {
        for observation in observations {
            self.record_semantic_terminal(observation);
        }
    }

    #[cfg(feature = "test-control")]
    fn record_semantic_terminal(&mut self, observation: SemanticTerminalObservation) {
        if !self.test_control.enabled() {
            return;
        }
        const MAX_TERMINAL_OBSERVATIONS: usize = 256;
        if self.semantic_terminal_outcomes.len() == MAX_TERMINAL_OBSERVATIONS {
            self.semantic_terminal_outcomes.pop_front();
        }
        self.semantic_terminal_outcomes.push_back(observation);
    }
}

#[cfg(feature = "test-control")]
fn semantic_observation(
    scheduled: &ScheduledWork,
    outcome: &'static str,
) -> Option<SemanticTerminalObservation> {
    let Work::Semantic(work) = &scheduled.work else {
        return None;
    };
    Some(SemanticTerminalObservation {
        task_id: scheduled.task_id,
        uri: work.uri.clone(),
        revision: work.revision,
        outcome,
    })
}

#[cfg(feature = "test-control")]
fn running_semantic_observation(
    running: &RunningWork,
    outcome: &'static str,
) -> Option<SemanticTerminalObservation> {
    Some(SemanticTerminalObservation {
        task_id: running.task_id,
        uri: running.semantic_uri.clone()?,
        revision: running.semantic_revision?,
        outcome,
    })
}

impl Drop for Scheduler {
    fn drop(&mut self) {
        self.cancel_all();
        if self.commands.send(WorkerCommand::Shutdown).is_err() {
            eprintln!("analysis worker stopped before shutdown");
        }
        if self
            .worker
            .take()
            .is_some_and(|worker| worker.join().is_err())
        {
            eprintln!("analysis worker panicked");
        }
    }
}

fn worker_loop(
    commands: Receiver<WorkerCommand>,
    events: Sender<AsyncEvent>,
    #[cfg(feature = "test-control")] test_control: TestControl,
) {
    while let Ok(command) = commands.recv() {
        let WorkerCommand::Run(scheduled) = command else {
            return;
        };
        let task_id = scheduled.task_id;
        let output = run_work(
            *scheduled,
            #[cfg(feature = "test-control")]
            &events,
            #[cfg(feature = "test-control")]
            &test_control,
        );
        if events
            .send(AsyncEvent::Completion(Box::new(WorkCompletion {
                task_id,
                output,
            })))
            .is_err()
        {
            return;
        }
    }
}

fn run_work(
    scheduled: ScheduledWork,
    #[cfg(feature = "test-control")] events: &Sender<AsyncEvent>,
    #[cfg(feature = "test-control")] test_control: &TestControl,
) -> Option<WorkOutput> {
    if scheduled.cancel.load(Ordering::Acquire) {
        return None;
    }
    #[cfg(feature = "test-control")]
    {
        let point = match &scheduled.work {
            Work::Policy(_) => Some(Checkpoint::Validation),
            Work::Semantic(_) => Some(Checkpoint::Semantic),
            Work::Schema(_) => None,
        };
        if let Some(point) = point {
            test_control.checkpoint(scheduled.task_id, point, &scheduled.cancel, events);
        }
    }
    if scheduled.cancel.load(Ordering::Acquire) {
        return None;
    }
    let ScheduledWork { cancel, work, .. } = scheduled;
    let output = match work {
        Work::Policy(work) => WorkOutput::Policy(Box::new(run_policy_validation(work))),
        Work::Schema(work) => WorkOutput::Schema(run_schema_diagnostics(&work)),
        Work::Semantic(work) => WorkOutput::Semantic(run_semantic(&work)),
    };
    (!cancel.load(Ordering::Acquire)).then_some(output)
}

fn resolved_policy_input(snapshot: &BundleSnapshot, parser_backed: bool) -> SemanticInput {
    if !parser_backed {
        return SemanticInput::PolicyLexical {
            policy: Arc::clone(&snapshot.policy.text),
        };
    }
    SemanticInput::PolicyProject {
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
    }
}

fn run_schema_diagnostics(work: &SchemaDiagnosticWork) -> SchemaDiagnosticResult {
    SchemaDiagnosticResult {
        uri: work.uri.clone(),
        revision: work.revision,
        publication: project_event_schema_outcome(
            work.version,
            SourceDocument {
                uri: &work.uri,
                text: &work.source,
            },
            parse_event_schema(&work.source),
        ),
    }
}

fn run_semantic(work: &SemanticWork) -> SemanticResult {
    let (source, analyzed) = match &work.input {
        SemanticInput::PolicyStandalone { policy } => {
            (Arc::clone(policy), analysis::analyze(policy))
        }
        SemanticInput::PolicyProject {
            policy,
            event_schema,
            providers,
            macros,
        } => (
            Arc::clone(policy),
            analysis::analyze_with_input(&analysis::SemanticInput {
                policy,
                event_schema: event_schema.as_deref(),
                providers: providers.as_deref(),
                macros: macros.as_deref(),
            }),
        ),
        SemanticInput::PolicyPending { .. } => {
            unreachable!("pending semantic work must be resolved by matching validation")
        }
        SemanticInput::PolicyLexical { policy } => {
            (Arc::clone(policy), analysis::analyze_lexical(policy))
        }
        SemanticInput::EventSchema { source } => {
            (Arc::clone(source), analysis::analyze_event_schema(source))
        }
    };
    let result = analyzed
        .map_err(semantic_analysis_failure)
        .and_then(|tokens| encode_tokens(&source, tokens).map_err(semantic_encoding_failure))
        .map(|data| SemanticTokens {
            result_id: None,
            data,
        });
    SemanticResult {
        request_id: work.request_id.clone(),
        uri: work.uri.clone(),
        revision: work.revision,
        result,
    }
}

fn semantic_analysis_failure(error: analysis::ValidationError) -> SemanticFailure {
    if matches!(
        error,
        analysis::ValidationError::SemanticTokenLimitExceeded { .. }
    ) {
        SemanticFailure::TokenLimit(error.to_string())
    } else {
        SemanticFailure::Internal(error.to_string())
    }
}

fn semantic_encoding_failure(error: EncodingError) -> SemanticFailure {
    if matches!(
        error,
        EncodingError::InvalidTokens(analysis::ValidationError::SemanticTokenLimitExceeded { .. })
    ) {
        SemanticFailure::TokenLimit(error.to_string())
    } else {
        SemanticFailure::Internal(error.to_string())
    }
}

#[cfg(feature = "test-control")]
#[derive(Clone, Debug)]
struct TestControl {
    shared: Option<Arc<TestControlShared>>,
}

#[cfg(feature = "test-control")]
#[derive(Debug)]
struct TestControlShared {
    state: Mutex<TestControlState>,
    changed: Condvar,
    #[cfg(test)]
    interleaving: Option<TestControlInterleaving>,
}

#[cfg(feature = "test-control")]
#[derive(Debug, Default)]
struct TestControlState {
    pause_next: BTreeMap<Checkpoint, usize>,
    paused: BTreeMap<u64, Checkpoint>,
}

#[cfg(all(test, feature = "test-control"))]
#[derive(Debug)]
struct TestControlInterleaving {
    predicate_evaluated: Sender<()>,
    wake_started: Receiver<()>,
    announce_wake: Sender<()>,
    wake_acquired: Receiver<()>,
    announce_wake_acquired: Sender<()>,
}

#[cfg(feature = "test-control")]
impl TestControl {
    fn from_environment() -> Self {
        let enabled = std::env::var(TEST_CONTROL_ENV).as_deref() == Ok("1");
        Self {
            shared: enabled.then(|| {
                Arc::new(TestControlShared {
                    state: Mutex::new(TestControlState::default()),
                    changed: Condvar::new(),
                    #[cfg(test)]
                    interleaving: None,
                })
            }),
        }
    }

    fn enabled(&self) -> bool {
        self.shared.is_some()
    }

    fn pause_next(&self, point: Checkpoint) {
        let Some(shared) = &self.shared else {
            return;
        };
        let mut state = shared.state.lock().expect("test control lock poisoned");
        *state.pause_next.entry(point).or_default() += 1;
    }

    fn checkpoint(
        &self,
        task_id: u64,
        point: Checkpoint,
        cancel: &AtomicBool,
        events: &Sender<AsyncEvent>,
    ) {
        let Some(shared) = &self.shared else {
            return;
        };
        let mut state = shared.state.lock().expect("test control lock poisoned");
        let Some(remaining) = state.pause_next.get_mut(&point) else {
            return;
        };
        if *remaining == 0 {
            return;
        }
        *remaining -= 1;
        state.paused.insert(task_id, point);
        drop(state);
        if events
            .send(AsyncEvent::TestReached { task_id, point })
            .is_err()
        {
            return;
        }

        let mut state = shared.state.lock().expect("test control lock poisoned");
        while state.paused.contains_key(&task_id) && !cancel.load(Ordering::Acquire) {
            #[cfg(test)]
            if let Some(interleaving) = &shared.interleaving {
                interleaving
                    .predicate_evaluated
                    .send(())
                    .expect("lost-wakeup test receiver should remain available");
                interleaving
                    .wake_started
                    .recv()
                    .expect("lost-wakeup test notifier should begin");
                assert!(
                    matches!(
                        interleaving.wake_acquired.try_recv(),
                        Err(crossbeam_channel::TryRecvError::Empty)
                    ),
                    "notifier must block on the state mutex until the worker waits"
                );
            }
            state = shared
                .changed
                .wait(state)
                .expect("test control lock poisoned while waiting");
            #[cfg(test)]
            if let Some(interleaving) = &shared.interleaving {
                interleaving
                    .wake_acquired
                    .try_recv()
                    .expect("notifier should acquire the state mutex before waking the worker");
            }
        }
        state.paused.remove(&task_id);
    }

    fn release(&self, task_id: u64) -> bool {
        let Some(shared) = &self.shared else {
            return false;
        };
        let removed = shared
            .state
            .lock()
            .expect("test control lock poisoned")
            .paused
            .remove(&task_id)
            .is_some();
        shared.changed.notify_all();
        removed
    }

    fn wake(&self) {
        if let Some(shared) = &self.shared {
            #[cfg(test)]
            if let Some(interleaving) = &shared.interleaving {
                interleaving
                    .announce_wake
                    .send(())
                    .expect("lost-wakeup test worker should remain available");
            }
            let state = shared.state.lock().expect("test control lock poisoned");
            #[cfg(test)]
            if let Some(interleaving) = &shared.interleaving {
                interleaving
                    .announce_wake_acquired
                    .send(())
                    .expect("lost-wakeup test worker should observe mutex acquisition");
            }
            shared.changed.notify_all();
            drop(state);
        }
    }
}

#[cfg(all(test, feature = "test-control"))]
mod tests {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::{Arc, Condvar, Mutex};
    use std::thread;
    use std::time::Duration;

    use crossbeam_channel::{RecvTimeoutError, bounded, unbounded};

    use super::{
        AsyncEvent, Checkpoint, TestControl, TestControlInterleaving, TestControlShared,
        TestControlState,
    };

    #[test]
    fn cancellation_wake_cannot_be_lost_between_predicate_and_wait() {
        const TASK_ID: u64 = 41;
        const DEADLINE: Duration = Duration::from_secs(2);

        let (predicate_evaluated, predicate_observed) = bounded(1);
        let (announce_wake, wake_started) = bounded(1);
        let (announce_wake_acquired, wake_acquired) = bounded(1);
        let control = TestControl {
            shared: Some(Arc::new(TestControlShared {
                state: Mutex::new(TestControlState::default()),
                changed: Condvar::new(),
                interleaving: Some(TestControlInterleaving {
                    predicate_evaluated,
                    wake_started,
                    announce_wake,
                    wake_acquired,
                    announce_wake_acquired,
                }),
            })),
        };
        control.pause_next(Checkpoint::Semantic);

        let cancel = Arc::new(AtomicBool::new(false));
        let (events, reached) = unbounded();
        let (worker_finished, worker_observed) = bounded(1);
        let worker_control = control.clone();
        let worker_cancel = Arc::clone(&cancel);
        let worker = thread::spawn(move || {
            worker_control.checkpoint(
                TASK_ID,
                Checkpoint::Semantic,
                worker_cancel.as_ref(),
                &events,
            );
            worker_finished
                .send(())
                .expect("test should observe worker completion");
        });

        assert!(matches!(
            reached.recv_timeout(DEADLINE),
            Ok(AsyncEvent::TestReached {
                task_id: TASK_ID,
                point: Checkpoint::Semantic
            })
        ));

        let notifier_control = control.clone();
        let notifier_cancel = Arc::clone(&cancel);
        let notifier = thread::spawn(move || {
            predicate_observed
                .recv_timeout(DEADLINE)
                .expect("worker should evaluate the wait predicate");
            notifier_cancel.store(true, Ordering::Release);
            notifier_control.wake();
        });

        match worker_observed.recv_timeout(DEADLINE) {
            Ok(()) => {}
            Err(error @ (RecvTimeoutError::Timeout | RecvTimeoutError::Disconnected)) => {
                control.release(TASK_ID);
                worker
                    .join()
                    .expect("worker should stop during test cleanup");
                notifier
                    .join()
                    .expect("notifier should stop during test cleanup");
                panic!("cancelled checkpoint remained stranded after wake: {error}");
            }
        }
        worker
            .join()
            .expect("worker should exit after cancellation");
        notifier.join().expect("notifier should complete");

        assert!(
            !control.release(TASK_ID),
            "cancelled worker must remove its paused task without explicit release"
        );
        let shared = control
            .shared
            .as_ref()
            .expect("test control should remain enabled");
        assert!(
            shared
                .state
                .lock()
                .expect("test control lock should remain available")
                .paused
                .is_empty(),
            "no paused worker may remain after cancellation"
        );
    }
}

#[cfg(all(test, not(feature = "test-control")))]
mod production_tests {
    use super::{Scheduler, configured_max_queued_work};

    #[test]
    fn production_capacity_is_fixed_at_1024() {
        assert_eq!(configured_max_queued_work(), 1024);
        assert_eq!(Scheduler::default().max_queued_work, 1024);
    }
}
