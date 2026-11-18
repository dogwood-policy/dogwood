//! A test of the `dogwood-language` crate's Lean frontend as a dependency
//! (feature `lean`): this crate compiles a Lean module of its own
//! (`lean/DependentProbe.lean`) against the Lean library the language crate's
//! build publishes (`DEP_DOGWOOD_LEAN_*`, see `build.rs`), and links it with the
//! language crate's archive, which holds that library and the process's one Lean
//! runtime. [`probe`] calls the module, which lowers a policy set with the
//! library's pipeline; the tests compare it with the language crate's own Lean
//! frontend, in one process, from several threads.
//!
//! Without the feature the crate is empty, so that no build of the workspace
//! turns the Lean frontend on.

#[cfg(feature = "lean")]
mod lean {
    use std::ffi::c_void;

    unsafe extern "C" {
        fn dependent_init() -> i32;
        fn dependent_enter();
        fn dependent_exit();
        fn dependent_probe(
            input: *const u8,
            input_len: usize,
            out: *mut *const u8,
            out_len: *mut usize,
        ) -> *mut c_void;
        fn dependent_lower(
            bare: i32,
            input: *const u8,
            input_len: usize,
            out: *mut *const u8,
            out_len: *mut usize,
        ) -> *mut c_void;
        fn dependent_release(handle: *mut c_void);
    }

    /// The calling thread registered with the Lean runtime until dropped.
    struct Registered;

    impl Registered {
        fn new() -> Registered {
            // SAFETY: the runtime is initialized (`dependent_init` returned 0).
            unsafe { dependent_enter() };
            Registered
        }
    }

    impl Drop for Registered {
        fn drop(&mut self) {
            // SAFETY: entered in `new`, on this thread.
            unsafe { dependent_exit() };
        }
    }

    /// Lower the policy set `inputs` describes (the language crate's
    /// `frontend_export::inputs`) with this crate's own Lean module: its JSON
    /// reply, `{"ok": {"cedar", "effects"}}` or `{"error": message}`.
    pub fn probe(inputs: &str) -> Result<String, String> {
        call(inputs, |i, n, out, out_len| {
            // SAFETY: the thread is registered; the shim copies the input.
            unsafe { dependent_probe(i, n, out, out_len) }
        })
    }

    /// Lower the policy set, or the sets, `inputs` describes (the language
    /// crate's `frontend_export::inputs` or `inputs_many`) with the library's
    /// pipeline, from this crate's own Lean module: the outcome as the library
    /// encodes it, or, with `bare`, the lowered set alone, which the language
    /// crate's `frontend::lowered_from_lean` decodes.
    pub fn lower(inputs: &str, bare: bool) -> Result<String, String> {
        call(inputs, |i, n, out, out_len| {
            // SAFETY: the thread is registered; the shim copies the input.
            unsafe { dependent_lower(i32::from(bare), i, n, out, out_len) }
        })
    }

    /// Call an entry point of the shim on `inputs`, on this thread, registered.
    fn call(
        inputs: &str,
        f: impl FnOnce(*const u8, usize, *mut *const u8, *mut usize) -> *mut c_void,
    ) -> Result<String, String> {
        // SAFETY: idempotent and thread-safe.
        if unsafe { dependent_init() } != 0 {
            return Err("the Lean runtime or a module failed to initialize".into());
        }
        let _registered = Registered::new();
        let mut out: *const u8 = std::ptr::null();
        let mut out_len = 0usize;
        let handle = f(inputs.as_ptr(), inputs.len(), &mut out, &mut out_len);
        // SAFETY: `out` views the reply's `out_len` bytes until the handle is released.
        let bytes = unsafe { std::slice::from_raw_parts(out, out_len) }.to_vec();
        // SAFETY: released once, on the thread that received it.
        unsafe { dependent_release(handle) };
        String::from_utf8(bytes).map_err(|_| "the reply is not UTF-8".into())
    }
}

#[cfg(feature = "lean")]
pub use lean::{lower, probe};

/// The digest of the Lean sources of the language crate this crate's Lean code
/// was compiled against (`DEP_DOGWOOD_LEAN_SOURCE_SHA256`).
#[cfg(feature = "lean")]
pub const COMPILED_AGAINST: &str = env!("DOGWOOD_LEAN_COMPILED_AGAINST");
