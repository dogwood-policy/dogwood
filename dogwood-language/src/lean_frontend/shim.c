/*
 * The C side of the Rust <-> Lean boundary of the Lean frontend (feature
 * `lean-frontend`), and the Lean runtime's initialization, which a dependent
 * crate that links Lean modules of its own shares.
 *
 * Rust never touches a `lean_object`: most of `lean.h` is `static inline`, so
 * this file (compiled against the toolchain's `lean.h` by `build.rs`) owns
 * every Lean object and hands Rust plain bytes.
 *
 * The runtime (the contract a dependent's own C code relies on too; the
 * crate's documentation of the `frontend` module states it):
 *   - `dogwood_lean_init` initializes the Lean runtime and every module of the
 *     frontend's library, once per process, and ends Lean's initialization. It
 *     is idempotent and thread-safe, and returns 0 on success (every later call
 *     returns the first call's result). Nothing else may initialize the
 *     runtime;
 *   - `dogwood_lean_thread_enter` registers the calling thread with Lean on its
 *     first enter and counts nested enters; `dogwood_lean_thread_exit`
 *     finalizes the thread on its last exit. Lean code runs only on a thread
 *     between the two, after `dogwood_lean_init` returned 0.
 *
 * Contract, per call of an entry point (see `runtime.rs`):
 *   - the calling thread is registered;
 *   - `in`/`in_len` is UTF-8 that Rust still owns; the shim copies it into a
 *     fresh Lean string, which the Lean entry point CONSUMES (Lean 4.34's code
 *     generator treats exported parameters as owned, `@&` or not);
 *   - the result is an owned Lean string, returned as an opaque handle plus a
 *     pointer/length view of its bytes; the caller copies the bytes and then
 *     releases the handle with `dogwood_lean_shim_release` ON THE SAME THREAD.
 */
#include <lean/lean.h>
#include <pthread.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>

/* Defined in libleanrt, not declared in lean.h. */
extern void lean_initialize_runtime_module(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);

/*
 * Since Lean 4.34, the initializer of every module that imports a `Lean.*`
 * module calls `lean_initialize()` (4.29 called it only from a program's
 * `main`). Lean's own definition, in libleancpp, initializes the root `Lean`
 * module, which references every module of libLean, so linking it would put
 * all of Lean's elaborator and compiler into the archive and run their
 * initializers at startup. The frontend needs only the runtime, which
 * `dogwood_lean_init` initializes anyway, so the archive defines the function
 * itself; this file is linked whole before libleancpp, so Lean's definition is
 * never pulled in. Lean code that needs the elaborator at run time cannot be
 * linked with this archive.
 */
void lean_initialize(void) { lean_initialize_runtime_module(); }

/* The root module initializer Lake generates for package `DogwoodSpec`,
 * module `Dogwood.Frontend.Library` (the library's root, which imports the C
 * entry points and every module a dependent builds on). Lean 4.34
 * initializers take no world token. */
extern lean_object *initialize_DogwoodSpec_Dogwood_Frontend_Library(uint8_t builtin);

/* The `@[export]` entry points of `Dogwood/Frontend/Ffi.lean`. Each takes an
 * owned `String` and returns an owned IO result whose value is a `String`. */
extern lean_object *dogwood_frontend_ping(lean_object *input);
extern lean_object *dogwood_frontend_lower(lean_object *input);
extern lean_object *dogwood_frontend_lower_many(lean_object *input);
extern lean_object *dogwood_frontend_panic_probe(lean_object *input);
extern lean_object *dogwood_frontend_parse(lean_object *input);

/* Entry-point ids; must match `Entry` in `runtime.rs`. */
enum {
    DOGWOOD_LEAN_PING = 0,
    DOGWOOD_LEAN_LOWER = 1,
    DOGWOOD_LEAN_LOWER_MANY = 2,
    DOGWOOD_LEAN_PANIC_PROBE = 3,
    DOGWOOD_LEAN_PARSE = 4,
};

/* The process state Lean's runtime initialization changes and the host keeps:
 * the SIGSEGV and SIGBUS handlers (Lean's stack-overflow detector), the
 * SIGPIPE disposition (Lean ignores it), and the calling thread's alternate
 * signal stack (Lean installs one for its handler). Restoring them leaves
 * stack-overflow reporting to the host (Rust's handler, which aborts with
 * "thread '...' has overflowed its stack"). */
static const int HOST_SIGNALS[] = {SIGSEGV, SIGBUS, SIGPIPE};
#define N_HOST_SIGNALS (sizeof HOST_SIGNALS / sizeof HOST_SIGNALS[0])

static pthread_once_t init_once = PTHREAD_ONCE_INIT;
static int init_status = 1;

/* The initialization proper, run once (`pthread_once`):
 *   1. the runtime (`lean_initialize_runtime_module`);
 *   2. the host's signal handlers and alternate stack, restored;
 *   3. the library's root module, with `builtin = 1`, which runs the
 *      initializers of every module it imports;
 *   4. the end of Lean's initialization (`lean_io_mark_end_initialization`). */
static void initialize_once(void) {
    struct sigaction saved[N_HOST_SIGNALS];
    stack_t saved_stack;
    int have_stack = sigaltstack(NULL, &saved_stack) == 0;
    for (size_t i = 0; i < N_HOST_SIGNALS; i++) {
        sigaction(HOST_SIGNALS[i], NULL, &saved[i]);
    }
    lean_initialize_runtime_module();
    for (size_t i = 0; i < N_HOST_SIGNALS; i++) {
        sigaction(HOST_SIGNALS[i], &saved[i], NULL);
    }
    if (have_stack) {
        if (saved_stack.ss_flags & SS_DISABLE) {
            stack_t off = {.ss_sp = NULL, .ss_flags = SS_DISABLE, .ss_size = 0};
            sigaltstack(&off, NULL);
        } else {
            saved_stack.ss_flags = 0;
            sigaltstack(&saved_stack, NULL);
        }
    }
    lean_object *res = initialize_DogwoodSpec_Dogwood_Frontend_Library(1 /* builtin */);
    int ok = lean_io_result_is_ok(res);
    if (!ok) {
        lean_io_result_show_error(res);
    }
    lean_dec(res);
    if (!ok) {
        return;
    }
    lean_io_mark_end_initialization();
    init_status = 0;
}

/* Returns 0 on success. Idempotent and thread-safe: the first call, from any
 * thread, initializes; every call returns its result. */
int dogwood_lean_init(void) {
    pthread_once(&init_once, initialize_once);
    return init_status;
}

/* How many times the calling thread entered and has not exited. */
static _Thread_local unsigned long thread_depth = 0;

/* Registers the calling thread with Lean on its first enter (after a
 * successful `dogwood_lean_init`); counts nested enters. */
void dogwood_lean_thread_enter(void) {
    if (thread_depth++ == 0) {
        lean_initialize_thread();
    }
}

/* Finalizes the calling thread on its last exit; an exit without an enter
 * does nothing. */
void dogwood_lean_thread_exit(void) {
    if (thread_depth == 0) {
        return;
    }
    if (--thread_depth == 0) {
        lean_finalize_thread();
    }
}

/* Returns the result handle (never NULL for a known entry id), or NULL for an
 * unknown id. `*out`/`*out_len` view the result string's UTF-8 bytes (no NUL
 * terminator counted) and stay valid until `dogwood_lean_shim_release(handle)`.
 * `*status` is 0 when Lean returned normally, 1 when the IO action itself
 * failed (the Lean side catches everything, so 1 means a bug there; the bytes
 * are then a fixed diagnostic). */
lean_object *dogwood_lean_shim_call(uint32_t entry, const uint8_t *in, size_t in_len,
                                    const uint8_t **out, size_t *out_len, int *status) {
    lean_object *arg = lean_mk_string_from_bytes_unchecked((const char *)in, in_len);
    lean_object *res;
    switch (entry) {
    case DOGWOOD_LEAN_PING:        res = dogwood_frontend_ping(arg); break;
    case DOGWOOD_LEAN_LOWER:       res = dogwood_frontend_lower(arg); break;
    case DOGWOOD_LEAN_LOWER_MANY:  res = dogwood_frontend_lower_many(arg); break;
    case DOGWOOD_LEAN_PANIC_PROBE: res = dogwood_frontend_panic_probe(arg); break;
    case DOGWOOD_LEAN_PARSE:       res = dogwood_frontend_parse(arg); break;
    default:
        lean_dec(arg);
        return NULL;
    }
    if (lean_io_result_is_ok(res)) {
        lean_object *s = lean_io_result_take_value(res);
        *out = (const uint8_t *)lean_string_cstr(s);
        *out_len = lean_string_size(s) - 1; /* m_size counts the NUL */
        *status = 0;
        return s;
    }
    lean_dec(res);
    static const char msg[] = "the Lean entry point raised an uncaught IO error";
    lean_object *s = lean_mk_string_from_bytes_unchecked(msg, sizeof msg - 1);
    *out = (const uint8_t *)lean_string_cstr(s);
    *out_len = lean_string_size(s) - 1;
    *status = 1;
    return s;
}

void dogwood_lean_shim_release(lean_object *handle) { lean_dec(handle); }
