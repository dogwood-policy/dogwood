//! The Lean runtime, as seen from Rust: process initialization, per-thread
//! registration, and one safe call primitive over the C shim (`shim.c`).
//!
//! ## Initialization
//!
//! The first call from any thread initializes the runtime once for the process
//! (`dogwood_lean_init`: `lean_initialize_runtime_module`, the module
//! initializers of `Dogwood.Frontend.Library` and of everything it imports,
//! `lean_io_mark_end_initialization`). The C function is idempotent and
//! thread-safe; its result is also kept in a [`OnceLock`]. A failure is
//! remembered and returned by every later call; Lean cannot be re-initialized.
//! A dependent crate that links Lean modules of its own calls the same C
//! function first, and initializes its own modules after (see the `frontend`
//! module's documentation, "Linking Lean code of your own").
//!
//! The runtime's initialization installs a process-wide `SIGSEGV`/`SIGBUS`
//! handler (Lean's stack-overflow detector). The shim saves the host's handlers
//! before and restores them after, so the Rust process keeps its own
//! stack-overflow reporting: a stack overflow inside Lean code is reported by
//! Rust's handler (`thread '…' has overflowed its stack`) and aborts the
//! process, as one in Rust code does.
//!
//! ## Threads and stacks
//!
//! Lean requires every thread it did not create to be registered
//! (`lean_initialize_thread`) before it runs Lean code, and finalized
//! (`lean_finalize_thread`) when it is done. The shim counts the registrations
//! of each thread (`dogwood_lean_thread_enter`, `dogwood_lean_thread_exit`), so
//! that a thread a dependent registered is registered once. Each call runs on a
//! fresh thread with a [`STACK_SIZE`] stack (the frontend recurses over the
//! policy's syntax trees and its JSON), registered for that one call. So any
//! thread may call in, concurrently, and no Lean object outlives a call or
//! crosses threads: the input string is created, consumed and freed, and the
//! result copied out and released, all on the call's thread.

use std::sync::OnceLock;

/// The stack of the thread each call runs on.
pub(super) const STACK_SIZE: usize = 256 * 1024 * 1024;

/// The opaque Lean object handle the shim returns. Rust never dereferences it.
#[repr(C)]
struct LeanObject {
    _private: [u8; 0],
}

unsafe extern "C" {
    fn dogwood_lean_init() -> i32;
    fn dogwood_lean_thread_enter();
    fn dogwood_lean_thread_exit();
    fn dogwood_lean_shim_call(
        entry: u32,
        input: *const u8,
        input_len: usize,
        out: *mut *const u8,
        out_len: *mut usize,
        status: *mut i32,
    ) -> *mut LeanObject;
    fn dogwood_lean_shim_release(handle: *mut LeanObject);
}

/// The Lean entry points, by the id the shim dispatches on (`shim.c`'s
/// `DOGWOOD_LEAN_*`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Entry {
    /// Returns its input unchanged (for the tests).
    #[cfg_attr(not(test), allow(dead_code))]
    Ping = 0,
    /// Lower one policy set, and validate it (`Ffi.lower`).
    Lower = 1,
    /// Lower several policy sets into one, and validate it (`Ffi.lowerMany`).
    LowerMany = 2,
    /// Test hook: panics in Lean on input `"panic"`.
    #[cfg_attr(not(test), allow(dead_code))]
    PanicProbe = 3,
    /// Parse, expand and assign the stable ids of one policy set (`Ffi.parse`).
    Parse = 4,
}

/// Why a call into Lean failed before Lean could produce an answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RuntimeError {
    /// The process-wide initialization failed (its diagnostic went to stderr).
    InitFailed,
    /// The Lean entry point raised an IO error it did not catch (a bug in
    /// `Ffi.lean`, whose entry points catch everything), or the call could not be
    /// made or answered: the call's thread could not be started, the shim does not
    /// know the entry point, or the reply is not UTF-8.
    Uncaught(String),
}

impl std::fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RuntimeError::InitFailed => f.write_str("the Lean runtime failed to initialize"),
            RuntimeError::Uncaught(m) => f.write_str(m),
        }
    }
}

static INIT: OnceLock<Result<(), RuntimeError>> = OnceLock::new();

/// Initialize the runtime, once per process.
pub(crate) fn ensure_initialized() -> Result<(), RuntimeError> {
    INIT.get_or_init(|| {
        // SAFETY: idempotent and thread-safe; called before any other shim call.
        if unsafe { dogwood_lean_init() } == 0 {
            Ok(())
        } else {
            Err(RuntimeError::InitFailed)
        }
    })
    .clone()
}

/// Registers the current thread with the Lean runtime until dropped (one counted
/// enter and exit of the shim's registration).
pub(crate) struct ThreadRegistration {
    _not_send: std::marker::PhantomData<*const ()>,
}

impl ThreadRegistration {
    /// Register the current thread. The process runtime must be initialized.
    pub(crate) fn new() -> Self {
        // SAFETY: the process runtime is initialized (checked by the caller).
        unsafe { dogwood_lean_thread_enter() };
        ThreadRegistration {
            _not_send: std::marker::PhantomData,
        }
    }
}

impl Drop for ThreadRegistration {
    fn drop(&mut self) {
        // SAFETY: this thread entered in `new` (on this thread: the guard is not
        // `Send`) and runs no more Lean code under this registration.
        unsafe { dogwood_lean_thread_exit() };
    }
}

/// A thread registered with the Lean runtime, on which [`with_lean`] runs its
/// closure. Not `Send`: Lean calls are made on the registered thread only.
pub(crate) struct LeanThread {
    _not_send: std::marker::PhantomData<*const ()>,
}

impl LeanThread {
    /// Call a Lean entry point with `input`; returns its result string.
    pub(crate) fn call(&self, entry: Entry, input: &str) -> Result<String, RuntimeError> {
        call_registered(entry, input)
    }
}

/// Run `f` on a fresh thread with a [`STACK_SIZE`] stack, registered with the
/// Lean runtime (initialized first if need be). The caller does its JSON work in
/// `f` too, so that a deeply nested policy is encoded and decoded on the big stack.
pub(crate) fn with_lean<T: Send>(
    f: impl FnOnce(&LeanThread) -> T + Send,
) -> Result<T, RuntimeError> {
    ensure_initialized()?;
    std::thread::scope(|scope| {
        let worker = std::thread::Builder::new()
            .name("dogwood-lean".to_owned())
            .stack_size(STACK_SIZE)
            .spawn_scoped(scope, || {
                let _registration = ThreadRegistration::new();
                f(&LeanThread {
                    _not_send: std::marker::PhantomData,
                })
            })
            .map_err(|e| {
                RuntimeError::Uncaught(format!("cannot start the Lean call's thread: {e}"))
            })?;
        worker
            .join()
            .map_err(|_| RuntimeError::Uncaught("the Lean call's thread panicked".to_owned()))
    })
}

/// Call a Lean entry point with `input` on a thread of its own (see [`with_lean`]).
#[cfg(test)]
pub(crate) fn call(entry: Entry, input: &str) -> Result<String, RuntimeError> {
    with_lean(|lean| lean.call(entry, input))?
}

/// The C initialization itself, called again (tests only: it is idempotent).
#[cfg(test)]
pub(crate) fn init_again() -> i32 {
    // SAFETY: idempotent and thread-safe.
    unsafe { dogwood_lean_init() }
}

/// [`call`] on the calling thread, which the caller registered (tests only).
#[cfg(test)]
pub(crate) fn call_here(entry: Entry, input: &str) -> Result<String, RuntimeError> {
    call_registered(entry, input)
}

/// [`call`] on a registered thread.
fn call_registered(entry: Entry, input: &str) -> Result<String, RuntimeError> {
    let mut out: *const u8 = std::ptr::null();
    let mut out_len: usize = 0;
    let mut status: i32 = 0;
    // SAFETY: the runtime is initialized and this thread registered; `input` is
    // valid UTF-8 for the duration of the call (the shim copies it).
    let handle = unsafe {
        dogwood_lean_shim_call(
            entry as u32,
            input.as_ptr(),
            input.len(),
            &mut out,
            &mut out_len,
            &mut status,
        )
    };
    // NULL only for an entry id the shim does not know (none of `Entry`'s), in
    // which case `out` was not written.
    if handle.is_null() {
        return Err(RuntimeError::Uncaught(format!(
            "the shim does not know the entry point {entry:?}"
        )));
    }
    // SAFETY: for a non-NULL handle, `out` points to the result string's `out_len`
    // bytes, valid until the handle is released below.
    let bytes = unsafe { std::slice::from_raw_parts(out, out_len) }.to_vec();
    // SAFETY: released once, on the thread that received it.
    unsafe { dogwood_lean_shim_release(handle) };
    // Lean strings are UTF-8; checked rather than assumed, so that a reply that is
    // not (a defect in the shim or the Lean side) is an error, not undefined
    // behavior.
    let result = String::from_utf8(bytes)
        .map_err(|_| RuntimeError::Uncaught("the Lean frontend's reply is not UTF-8".to_owned()))?;
    if status == 0 {
        Ok(result)
    } else {
        Err(RuntimeError::Uncaught(result))
    }
}
