/*
 * The dependent's C side: its own Lean module's initialization and entry point,
 * over the Lean runtime the `dogwood-language` crate's archive holds and
 * initializes (`dogwood_lean_init`, `dogwood_lean_thread_enter`,
 * `dogwood_lean_thread_exit`, which this file only declares).
 *
 * The contract it follows (the `frontend` module's documentation of the
 * language crate): the language crate initializes the runtime and its own
 * modules, once, and ends Lean's initialization; the dependent initializes its
 * own root module afterwards, once, on a registered thread; every thread that
 * runs Lean code is registered, with counted enters and exits.
 */
#include <lean/lean.h>
#include <pthread.h>
#include <stddef.h>
#include <stdint.h>

extern int dogwood_lean_init(void);
extern void dogwood_lean_thread_enter(void);
extern void dogwood_lean_thread_exit(void);

/* The root module initializer of package `DogwoodLeanDependent`, module
 * `DependentProbe`, and its `@[export]` entry points. */
extern lean_object *initialize_DogwoodLeanDependent_DependentProbe(uint8_t builtin);
extern lean_object *dogwood_dependent_probe(lean_object *input);
extern lean_object *dogwood_dependent_lower(lean_object *input);
extern lean_object *dogwood_dependent_lower_bare(lean_object *input);

static pthread_once_t once = PTHREAD_ONCE_INIT;
static int status = 1;

static void initialize(void) {
    if (dogwood_lean_init() != 0) {
        return;
    }
    dogwood_lean_thread_enter();
    lean_object *res = initialize_DogwoodLeanDependent_DependentProbe(1 /* builtin */);
    int ok = lean_io_result_is_ok(res);
    if (!ok) {
        lean_io_result_show_error(res);
    }
    lean_dec(res);
    dogwood_lean_thread_exit();
    status = ok ? 0 : 1;
}

/* The language crate's runtime and modules, then this crate's: once; 0 on success. */
int dependent_init(void) {
    pthread_once(&once, initialize);
    return status;
}

void dependent_enter(void) { dogwood_lean_thread_enter(); }
void dependent_exit(void) { dogwood_lean_thread_exit(); }

/* An entry point `f` of this crate's module on a copy of `in`; the reply's bytes
 * stay valid until `dependent_release(handle)`, on the same thread. */
static lean_object *call(lean_object *(*f)(lean_object *), const uint8_t *in, size_t in_len,
                         const uint8_t **out, size_t *out_len) {
    lean_object *arg = lean_mk_string_from_bytes_unchecked((const char *)in, in_len);
    lean_object *res = f(arg);
    lean_object *s;
    if (lean_io_result_is_ok(res)) {
        s = lean_io_result_take_value(res);
    } else {
        lean_dec(res);
        static const char msg[] = "{\"error\":\"the probe raised an IO error\"}";
        s = lean_mk_string_from_bytes_unchecked(msg, sizeof msg - 1);
    }
    *out = (const uint8_t *)lean_string_cstr(s);
    *out_len = lean_string_size(s) - 1;
    return s;
}

/* `DependentProbe.probe`. */
lean_object *dependent_probe(const uint8_t *in, size_t in_len, const uint8_t **out,
                             size_t *out_len) {
    return call(dogwood_dependent_probe, in, in_len, out, out_len);
}

/* `DependentProbe.lower`, its outcome or (`bare`) the lowered set alone. */
lean_object *dependent_lower(int bare, const uint8_t *in, size_t in_len, const uint8_t **out,
                             size_t *out_len) {
    return call(bare ? dogwood_dependent_lower_bare : dogwood_dependent_lower, in, in_len, out,
                out_len);
}

void dependent_release(lean_object *handle) { lean_dec(handle); }
