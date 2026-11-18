//! Size and nesting limits on untrusted input.
//!
//! Every recursive walk in the bindings and in the crates below them — a
//! host-value deserializer, [`to_value`](crate::live::to_value), Cedar's
//! evaluator, the MCP manifest parser — uses one stack frame per level of
//! input nesting. Under WebAssembly a few KB of `{"k":{"k":…}}` exhausts the
//! stack, and the trap leaves the module's shadow stack pointer unrestored and
//! the instance's borrow flag set, so **every** later call into the module
//! fails. Natively the stack is larger, but an overflow aborts the whole host
//! process. Either way one hostile tool argument would be a denial of service.
//!
//! The checks here run **before** any recursive code sees the input, and are
//! themselves iterative (an explicit work stack, no recursion), so oversized
//! input becomes an ordinary `DogwoodError`. This module holds the limits and
//! the accounting helpers; each binding walks its own host values (JS objects,
//! Python objects) with them, since only it knows how to enumerate them.
//!
//! The value-depth limit is the one `dogwood-language`'s `.log` parser already
//! enforces (`MAX_VALUE_DEPTH` in `interpreter/log_parse.rs`), so a value that
//! `replay` accepts is accepted live, and vice versa.

/// Maximum nesting depth of one event value. Counted as `dogwood-language`'s
/// `.log` parser counts it, whose limit of the same name this matches: a
/// `context` / `logged` group (`context.input`) is the depth-0 record, so its
/// fields start at depth 1; an entity attribute starts at depth 0. Each array
/// or object level adds one.
pub const MAX_VALUE_DEPTH: usize = 128;

/// How deep event values sit inside the event object itself:
/// `event.entities[i].attrs.<name>` is the deepest, at 4 levels.
pub const EVENT_FRAMING_DEPTH: usize = 4;

/// Maximum number of values (scalars, arrays and objects, at any depth) in one
/// event. Far beyond any real tool call; bounds the work one event can cause.
pub const MAX_EVENT_VALUES: usize = 100_000;

/// Maximum total length of all strings in one event, object keys included, in
/// the host's own string-length unit (UTF-16 code units in JS, code points in
/// Python). 16 Mi leaves room for
/// large tool arguments such as file contents.
pub const MAX_EVENT_STRING_LENGTH: usize = 16 * 1024 * 1024;

/// Maximum size of an MCP `tools/list` manifest, in UTF-8 bytes.
pub const MAX_MANIFEST_BYTES: usize = 4 * 1024 * 1024;

/// Maximum nesting depth of an MCP manifest's JSON (arrays and objects).
pub const MAX_MANIFEST_DEPTH: usize = 128;

/// Add one string's length to the running total, failing past the limit.
pub fn add_string(len: usize, total: &mut usize) -> Result<(), String> {
    *total = total.saturating_add(len);
    if *total > MAX_EVENT_STRING_LENGTH {
        return Err(format!(
            "event strings total more than the limit of {MAX_EVENT_STRING_LENGTH} characters"
        ));
    }
    Ok(())
}

pub fn too_deep() -> String {
    format!("event value nested deeper than the limit of {MAX_VALUE_DEPTH}")
}

/// Admit a container's `children` at `child_depth`, before any of them is
/// pushed onto the work stack. Fails when they would sit past `max_depth`, or
/// would take the event past the value-count limit. An empty container admits
/// nothing, so there is nothing to check.
pub fn admit(
    children: usize,
    child_depth: usize,
    max_depth: usize,
    values: &mut usize,
) -> Result<(), String> {
    if children == 0 {
        return Ok(());
    }
    if child_depth > max_depth {
        // Past the framing allowance the event is either too deep or cyclic;
        // this walk cannot tell which, so say both.
        return Err(format!("{} (or is cyclic)", too_deep()));
    }
    *values = values.saturating_add(children);
    if *values > MAX_EVENT_VALUES {
        return Err(format!(
            "event has more than the limit of {MAX_EVENT_VALUES} values"
        ));
    }
    Ok(())
}

/// The per-value depth check `to_value` applies while converting.
pub fn check_value_depth(depth: usize) -> Result<(), String> {
    if depth > MAX_VALUE_DEPTH {
        Err(too_deep())
    } else {
        Ok(())
    }
}

/// Check JSON text against a byte-size and nesting-depth limit without parsing
/// it: one linear scan tracking `[`/`{` depth outside string literals. Used for
/// inputs whose parser lives in a dependency and recurses without a cap.
pub fn check_json_text(
    what: &str,
    text: &str,
    max_bytes: usize,
    max_depth: usize,
) -> Result<(), String> {
    if text.len() > max_bytes {
        return Err(format!(
            "{what} is {} bytes, over the limit of {max_bytes}",
            text.len()
        ));
    }
    let (mut depth, mut in_string, mut escaped) = (0usize, false, false);
    for byte in text.bytes() {
        if in_string {
            match byte {
                _ if escaped => escaped = false,
                b'\\' => escaped = true,
                b'"' => in_string = false,
                _ => {}
            }
            continue;
        }
        match byte {
            b'"' => in_string = true,
            b'[' | b'{' => {
                depth += 1;
                if depth > max_depth {
                    return Err(format!(
                        "{what} is nested deeper than the limit of {max_depth}"
                    ));
                }
            }
            b']' | b'}' => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nested(n: usize) -> String {
        format!("{}{}", "[".repeat(n), "]".repeat(n))
    }

    #[test]
    fn json_text_at_the_depth_limit_passes() {
        assert!(check_json_text("m", &nested(128), 1 << 20, 128).is_ok());
    }

    #[test]
    fn json_text_past_the_depth_limit_fails() {
        let err = check_json_text("m", &nested(129), 1 << 20, 128).unwrap_err();
        assert!(err.contains("nested deeper than the limit of 128"), "{err}");
    }

    #[test]
    fn brackets_inside_strings_do_not_count() {
        let text = format!(r#"{{"a": "{}", "b": "\"[[["}}"#, "[".repeat(1000));
        assert!(check_json_text("m", &text, 1 << 20, 4).is_ok());
    }

    #[test]
    fn oversized_json_text_fails() {
        let err = check_json_text("m", &"x".repeat(11), 10, 128).unwrap_err();
        assert!(err.contains("over the limit of 10"), "{err}");
    }

    #[test]
    fn value_depth_matches_the_log_parser() {
        assert!(check_value_depth(128).is_ok());
        assert!(check_value_depth(129).is_err());
    }
}
