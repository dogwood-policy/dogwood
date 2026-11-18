//! Field paths as text: the one place a path becomes a string and back.
//!
//! A field path is a non-empty list of segments: `["input", "user"]` names the
//! `user` member of the `input` group. The crate keeps most paths as that list.
//! A few places keep a path as one string instead: the name of a predicate
//! argument ([`NamedArg::name`](crate::extension::temporal::ast::NamedArg)), the
//! keys of the evaluator's request environment, and the paths that diagnostics
//! and explanations print. Each of them writes the string with [`join`] and
//! reads it with [`split`].
//!
//! The text escapes each segment and joins the segments with `.`. Inside a
//! segment, `\` is written `\\` and `.` is written `\.`. So a segment that holds
//! a `.` stays one segment: Cedar allows any string as an attribute name (as in
//! `context.input["user.id"]`), and the path `["input", "user.id"]` is written
//! `input.user\.id`, while `["input", "user", "id"]` is written
//! `input.user.id`. [`split`] cuts a text at its unescaped dots and drops the
//! escapes, so `split(&join(path)) == path` for every non-empty path, and two
//! different non-empty paths never have the same text.
//!
//! A path whose segments hold neither `.` nor `\` is written exactly as before
//! the escape existed: its segments joined by `.` (`["input", "user"]` is
//! `input.user`). The policy grammar and the event-schema grammar can spell
//! only identifiers, which hold neither character, so the text of every
//! authored or schema-declared path is unchanged.
//!
//! Any other implementation that keys a request by field path must read and
//! write this same text.

/// The text of a field path: each segment escaped (`\` as `\\`, `.` as `\.`),
/// and the segments joined by `.`.
///
/// `join(&["input", "user"])` is `input.user`; `join(&["input", "user.id"])`
/// is `input.user\.id`. [`split`] reads the text back.
pub fn join<S: AsRef<str>>(segments: &[S]) -> String {
    let mut out = String::new();
    for (i, segment) in segments.iter().enumerate() {
        if i > 0 {
            out.push('.');
        }
        escape_into(&mut out, segment.as_ref());
    }
    out
}

/// The field path a text written by [`join`] names: the text cut at every `.`
/// that no `\` escapes, with each escape `\c` read as `c`. A lone `\` at the end
/// of the text reads as itself.
///
/// `split("input.user")` is `["input", "user"]`; `split("input.user\\.id")` is
/// `["input", "user.id"]`. A text with no `.` is a single-segment path.
pub fn split(text: &str) -> Vec<String> {
    let mut segments = Vec::new();
    let mut current = String::new();
    let mut chars = text.chars();
    while let Some(c) = chars.next() {
        match c {
            '\\' => current.push(chars.next().unwrap_or('\\')),
            '.' => segments.push(std::mem::take(&mut current)),
            other => current.push(other),
        }
    }
    segments.push(current);
    segments
}

/// The text of the path `root` followed by `path`, where `root` is a segment
/// that holds neither `.` nor `\` (`context`, `@principal`): `root` as it is,
/// then each segment of `path` escaped, all joined by `.`. For such a root this
/// is `join` of the whole path.
pub(crate) fn join_under(root: &str, path: &[String]) -> String {
    debug_assert!(!root.contains(['.', '\\']), "root `{root}` needs no escape");
    let mut out = root.to_string();
    for segment in path {
        push_segment(&mut out, segment);
    }
    out
}

/// Extend the text of a path by one segment: a `.`, then the segment escaped.
pub(crate) fn push_segment(text: &mut String, segment: &str) {
    text.push('.');
    escape_into(text, segment);
}

fn escape_into(out: &mut String, segment: &str) {
    for c in segment.chars() {
        if c == '\\' || c == '.' {
            out.push('\\');
        }
        out.push(c);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    fn owned(path: &[&str]) -> Vec<String> {
        path.iter().map(|s| s.to_string()).collect()
    }

    /// Every string over `alphabet` of length at most `max_len`.
    fn strings(alphabet: &[char], max_len: usize) -> Vec<String> {
        let mut all = vec![String::new()];
        let mut last = vec![String::new()];
        for _ in 0..max_len {
            let next: Vec<String> = last
                .iter()
                .flat_map(|s| {
                    alphabet.iter().map(move |c| {
                        let mut t = s.clone();
                        t.push(*c);
                        t
                    })
                })
                .collect();
            all.extend(next.iter().cloned());
            last = next;
        }
        all
    }

    /// Every path of 1 to `max_segments` segments drawn from `segments`.
    fn paths(segments: &[String], max_segments: usize) -> Vec<Vec<String>> {
        let mut all = Vec::new();
        let mut last: Vec<Vec<String>> = vec![Vec::new()];
        for _ in 0..max_segments {
            let next: Vec<Vec<String>> = last
                .iter()
                .flat_map(|p| {
                    segments.iter().map(move |s| {
                        let mut q = p.clone();
                        q.push(s.clone());
                        q
                    })
                })
                .collect();
            all.extend(next.iter().cloned());
            last = next;
        }
        all
    }

    /// Fixed examples of the text: any implementation that reads and writes
    /// this format must produce and accept exactly these strings.
    #[test]
    fn matches_the_format_examples() {
        assert_eq!(join(&["context", "input", "user"]), "context.input.user");
        assert_eq!(join(&["context", "a.b"]), "context.a\\.b");
        assert_eq!(join(&["context", "a\\b"]), "context.a\\\\b");
        assert_eq!(
            split("context.input.user"),
            owned(&["context", "input", "user"])
        );
        assert_eq!(
            split(&join(&["context", "a.b"])),
            owned(&["context", "a.b"])
        );
        assert_eq!(
            split(&join(&["context", "a", "b"])),
            owned(&["context", "a", "b"])
        );
        let odd = ["scope", "principal", "x\\.y", "", "z\\"];
        assert_eq!(split(&join(&odd)), owned(&odd));
        assert_ne!(join(&["context", "a.b"]), join(&["context", "a", "b"]));
    }

    #[test]
    fn a_lone_trailing_backslash_reads_as_itself() {
        assert_eq!(split("a\\"), owned(&["a\\"]));
        // An escape of any other character reads as that character.
        assert_eq!(split("a\\bc"), owned(&["abc"]));
        assert_eq!(split(""), owned(&[""]));
        assert_eq!(split("."), owned(&["", ""]));
    }

    /// Round trip, exhaustively over a small alphabet that holds both special
    /// characters: every path of up to three segments of up to three
    /// characters reads back as itself.
    #[test]
    fn split_inverts_join_exhaustively() {
        let segments = strings(&['a', '.', '\\'], 3);
        for path in paths(&segments, 3) {
            assert_eq!(split(&join(&path)), path, "text {:?}", join(&path));
        }
    }

    /// Injectivity, exhaustively over the same domain: no two different paths
    /// have the same text.
    #[test]
    fn join_is_injective_exhaustively() {
        let segments = strings(&['a', '.', '\\'], 3);
        let mut seen: HashMap<String, Vec<String>> = HashMap::new();
        for path in paths(&segments, 3) {
            let text = join(&path);
            if let Some(other) = seen.insert(text.clone(), path.clone()) {
                panic!("{other:?} and {path:?} both have the text {text:?}");
            }
        }
    }

    /// Round trip and injectivity on pseudo-random paths over a wider
    /// alphabet (multi-byte characters included) and longer segments.
    #[test]
    fn split_inverts_join_on_random_paths() {
        let alphabet = ['a', 'Z', '0', '_', '.', '\\', ' ', '"', 'é', '中', '\u{1f}'];
        let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut next = move |bound: usize| {
            // xorshift64*
            state ^= state >> 12;
            state ^= state << 25;
            state ^= state >> 27;
            (state.wrapping_mul(0x2545_f491_4f6c_dd1d) >> 33) as usize % bound
        };
        let mut seen: HashMap<String, Vec<String>> = HashMap::new();
        for _ in 0..20_000 {
            let mut path = Vec::new();
            for _ in 0..1 + next(5) {
                let mut segment = String::new();
                for _ in 0..next(9) {
                    segment.push(alphabet[next(alphabet.len())]);
                }
                path.push(segment);
            }
            let text = join(&path);
            assert_eq!(split(&text), path, "text {text:?}");
            if let Some(other) = seen.insert(text.clone(), path.clone()) {
                assert_eq!(other, path, "two paths share the text {text:?}");
            }
        }
    }

    /// A path whose segments hold neither `.` nor `\` is written exactly as
    /// the segments joined by `.`, and a text with no `\` reads as the text cut
    /// at every `.`: the names the grammars can spell are unchanged.
    #[test]
    fn plain_paths_keep_their_dotted_text() {
        let segments = strings(&['a', 'b', '_', '1', 'é'], 2);
        for path in paths(&segments, 3) {
            assert_eq!(join(&path), path.join("."));
            assert_eq!(split(&path.join(".")), path);
        }
        for text in [
            "callerPrincipal",
            "input.user",
            "__drupe.session_id",
            "a.b.c",
        ] {
            let plain: Vec<String> = text.split('.').map(str::to_string).collect();
            assert_eq!(split(text), plain);
            assert_eq!(join(&plain), text);
        }
    }

    #[test]
    fn join_under_and_push_segment_agree_with_join() {
        let segments = strings(&['a', '.', '\\'], 2);
        for path in paths(&segments, 2) {
            let mut whole = vec!["context".to_string()];
            whole.extend(path.iter().cloned());
            assert_eq!(join_under("context", &path), join(&whole));
            let mut text = join(&path[..1]);
            for s in &path[1..] {
                push_segment(&mut text, s);
            }
            assert_eq!(text, join(&path));
        }
    }
}
