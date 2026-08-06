//! Parser for the `.log` trace wire format.
//!
//! Each timepoint is one line:
//! `@<ts> <Name>(<field>: <value>, …)`
//!
//! Values follow Cedar surface forms: entity refs `Ns::Type::"id"`,
//! double-quoted strings, integers, decimals (`1.50`), `true`/`false`,
//! arrays `[…]`, and objects `{…}`. This is the trace format the corpus is
//! written in, so the existing corpus parses verbatim.

use std::collections::BTreeMap;

use super::value::{EntityRecord, Event, EventData, Scope, Trace, Value};

/// Parse a `.log` trace into a [`Trace`].
///
/// Blank lines are skipped; every other line is a timepoint. There is no
/// comment syntax — a `//` is an ordinary part of a value (e.g. a URL like
/// `http://…`), not a line comment.
pub fn parse_trace(log: &str) -> Result<Trace, String> {
    let log = log.strip_prefix('\u{FEFF}').unwrap_or(log);
    let mut points = Vec::new();
    for (lineno, raw) in log.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() {
            continue;
        }
        let tp = parse_line(line).map_err(|e| format!("line {}: {e}", lineno + 1))?;
        points.push(tp);
    }
    Ok(Trace { points })
}

fn parse_line(line: &str) -> Result<Event, String> {
    // `@<ts> <rest>`
    let rest = line
        .strip_prefix('@')
        .ok_or("timepoint must start with `@`")?;
    let (ts_str, after) = rest
        .split_once(char::is_whitespace)
        .ok_or("expected whitespace after timestamp")?;
    let ts: i64 = ts_str
        .trim()
        .parse()
        .map_err(|_| format!("bad timestamp `{ts_str}`"))?;

    let mut after = after.trim();

    // Optional leading `scope(principal: …, resource: …)` envelope. The scope
    // args are uids (no nested parens/braces), so a naive `find(')')` is safe
    // here.
    let mut scope = Scope::default();
    if let Some(rest) = after.strip_prefix("scope(") {
        let sclose = rest.find(')').ok_or("scope missing `)`")?;
        let scope_fields = parse_args(&rest[..sclose])?;
        scope.principal = scope_fields.get("principal").cloned();
        scope.resource = scope_fields.get("resource").cloned();
        after = rest[sclose + 1..].trim();
    }

    // Optional `entities(<uid>: { <attrs> }, …)` envelope, after `scope(...)`.
    // Its attribute values contain nested `{}`/`[]`/quoted strings, so the
    // closing `)` must be found with depth/in-string tracking, NOT `find(')')`.
    let mut entities = BTreeMap::new();
    if let Some(rest) = after.strip_prefix("entities(") {
        let eclose = matching_paren(rest).ok_or("entities missing `)`")?;
        entities = parse_entities(&rest[..eclose])?;
        after = rest[eclose + 1..].trim();
    }

    // Optional `request_context(<group>: { … }, …)` envelope, after
    // `entities(...)`. This is the request-only context (`input`, `system`, …)
    // the Cedar request is built from — distinct from the logged record below.
    // Same depth/in-string-aware scan as `entities(...)` (values nest).
    let mut request_context = BTreeMap::new();
    if let Some(rest) = after.strip_prefix("request_context(") {
        let rclose = matching_paren(rest).ok_or("request_context missing `)`")?;
        request_context = parse_args(&rest[..rclose])?;
        after = rest[rclose + 1..].trim();
    }

    // `<qualified-name>::<kind>(<fields>)`, where the qualified name is
    // `Ns::Sub::"Id"` and the kind is a trailing `::ident`. The trailing group
    // is the **logged** record (temporal-history fields).
    let open = after.find('(').ok_or("event missing `(`")?;
    let head = after[..open].trim();
    let close = after.rfind(')').ok_or("event missing `)`")?;
    // The closing `)` must come after the opening `(`. On a malformed line
    // whose last `)` precedes its first `(` (e.g. `@0 )(`), `open > close` and
    // the slice below would panic on a reversed byte range. Guard it into a
    // clean parse error — this parser consumes untrusted `.log` input.
    if open >= close {
        return Err("event group `(` and `)` are out of order".to_string());
    }
    let args_src = &after[open + 1..close];

    let (namespace, action, kind) = parse_event_head(head)?;
    let logged = parse_args(args_src)?;
    Ok(Event {
        ts,
        scope,
        event: EventData {
            namespace,
            action,
            kind,
            logged,
            request_context,
            entities,
        },
    })
}

/// Parse the body of an `entities(...)` envelope. Each top-level-comma-separated
/// entry is:
///
/// ```text
/// <uid>: { <attrs> } [ in [ <parent-uid>, … ] ]
/// ```
///
/// — a uid, its attribute record, and an OPTIONAL trailing `in [ … ]` clause of
/// direct parents (`memberOf` edges). Produces a `uid -> EntityRecord` map.
///
/// The map is keyed by the **canonical** (escaped) uid literal, decoded from the
/// author's spelling and re-rendered with [`super::value::entity_uid_string`], so
/// a trace may write an id containing a quote either way (`"o'brien"` or
/// `"o\'brien"`) and both resolve to the same entity.
///
/// The uid itself contains `::`, so the entry cannot be split on its first `:`;
/// the split point is the top-level `:` immediately preceding the record's `{`.
/// The record spans to its matching `}`; anything after it must be the `in [ … ]`
/// parents clause. An entry with no `in` clause parses exactly as before (empty
/// `parents`), so existing traces are unaffected.
fn parse_entities(src: &str) -> Result<BTreeMap<String, EntityRecord>, String> {
    let mut out = BTreeMap::new();
    for entry in split_top_level(src, ',') {
        let entry = entry.trim();
        if entry.is_empty() {
            continue;
        }
        // Find the top-level `{` that opens the attribute record.
        let brace = top_level_char(entry, '{').ok_or_else(|| {
            format!("entities entry `{entry}` missing an attribute record `{{ ... }}`")
        })?;
        let uid = entry[..brace].trim_end();
        // The uid ends at the `:` just before the `{`.
        let uid = uid
            .strip_suffix(':')
            .ok_or_else(|| format!("entities entry `{entry}` missing `:` before `{{`"))?
            .trim();

        // The record spans `{` to its matching `}`; the rest (if any) is the
        // optional `in [ … ]` parents clause.
        let rec_src = &entry[brace..];
        let rclose = matching_brace(rec_src)
            .ok_or_else(|| format!("entities entry `{entry}` has an unterminated `{{ ... }}`"))?;
        let attrs = match parse_value(rec_src[..=rclose].trim())? {
            Value::Object(attrs) => attrs,
            _ => {
                return Err(format!(
                    "entities entry `{uid}` value is not a `{{ ... }}` record"
                ));
            }
        };
        let parents = parse_entity_parents(rec_src[rclose + 1..].trim(), uid)?;

        // The store is keyed by the CANONICAL (escaped) uid literal — the form
        // `value::entity_uid_string` produces — because every lookup rebuilds its
        // key from a decoded `(ty, id)` (`EventData::resolve_entity_attr`,
        // `eval::seed_supplied_entity_attrs`). Keying by the author's spelling
        // breaks that for any id Cedar escapes (`'`, `"`, `\`, control chars).
        //
        // So decode to `(ty, id)` and re-render, exactly once: `unescape` is the
        // exact inverse of the escaper, so an already-canonical key round-trips
        // unchanged rather than double-escaping.
        let key = match parse_value(uid)? {
            v @ Value::Entity { .. } => super::value::value_uid_string(&v)
                .expect("a Value::Entity always renders to a uid string"),
            _ => {
                return Err(format!(
                    "entities entry `{uid}` key is not an entity ref `Ns::Type::\"id\"`"
                ));
            }
        };

        // A duplicate uid is an authoring error, not a silent last-wins: which
        // binding survived is invisible in the decision, so reject it.
        if out.insert(key, EntityRecord { attrs, parents }).is_some() {
            return Err(format!("entities envelope has a duplicate uid `{uid}`"));
        }
    }
    Ok(out)
}

/// Parse the optional trailing parents clause of an entities entry. `rest` is
/// the text after the attribute record's `}`; it is either empty (no parents) or
/// `in [ <parent-uid>, … ]`. Each parent is an entity-ref value (`Ns::Type::"id"`).
fn parse_entity_parents(rest: &str, uid: &str) -> Result<Vec<Value>, String> {
    if rest.is_empty() {
        return Ok(Vec::new());
    }
    let list = rest.strip_prefix("in").map(str::trim_start).ok_or_else(|| {
        format!("entities entry `{uid}` has trailing text after its record; expected `in [ ... ]`, found `{rest}`")
    })?;
    let inner = list
        .strip_prefix('[')
        .and_then(|s| s.strip_suffix(']'))
        .ok_or_else(|| {
            format!(
                "entities entry `{uid}` parents must be a bracketed list `in [ ... ]`, found `{list}`"
            )
        })?;
    let mut parents = Vec::new();
    for item in split_top_level(inner, ',') {
        let item = item.trim();
        if item.is_empty() {
            continue;
        }
        match parse_value(item)? {
            v @ Value::Entity { .. } => parents.push(v),
            _ => {
                return Err(format!(
                    "entities entry `{uid}` parent `{item}` is not an entity ref `Ns::Type::\"id\"`"
                ));
            }
        }
    }
    Ok(parents)
}

/// Parse a structured event head `Ns::Sub::"Id"::kind` into its namespace
/// path, quoted action id, and event-kind segment.
fn parse_event_head(head: &str) -> Result<(Vec<String>, String, String), String> {
    // The id is the only quoted segment; the kind is the bare `::ident`
    // after the closing quote, and the namespace is everything before the
    // opening quote.
    let q_open = head
        .find("::\"")
        .ok_or_else(|| format!("event head `{head}` is missing a quoted action id"))?;
    let id_start = q_open + 3;
    // Find the unescaped closing quote (handles `\"` inside the action id).
    let id_end = find_unescaped_quote(&head[id_start..])
        .map(|n| id_start + n)
        .ok_or_else(|| format!("event head `{head}` has an unterminated action id"))?;
    let namespace: Vec<String> = head[..q_open].split("::").map(|s| s.to_string()).collect();
    let action = unescape(&head[id_start..id_end]);
    let after_id = head[id_end + 1..].trim();
    let kind = after_id
        .strip_prefix("::")
        .map(|k| k.trim().to_string())
        .filter(|k| !k.is_empty())
        .ok_or_else(|| format!("event head `{head}` is missing a `::kind` segment"))?;
    Ok((namespace, action, kind))
}

/// Parse `field: value, field: value, …` honoring nested `()[]{}` and
/// quoted strings when splitting on commas. Shared by the `scope(...)`,
/// `request_context(...)`, and trailing (logged) field groups; a duplicate key
/// in any of them is a parse error (last-wins would silently drop a binding —
/// see [`parse_value`]'s object branch for the same rule on nested records).
fn parse_args(src: &str) -> Result<BTreeMap<String, Value>, String> {
    let mut fields = BTreeMap::new();
    for part in split_top_level(src, ',') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        let (key, val) = split_top_level_once(part, ':')
            .ok_or_else(|| format!("argument `{part}` missing `:`"))?;
        let key = key.trim().to_string();
        if fields
            .insert(key.clone(), parse_value(val.trim())?)
            .is_some()
        {
            return Err(format!("duplicate field `{key}`"));
        }
    }
    Ok(fields)
}

/// The maximum nesting depth of a logged value (array/object). A `.log` line
/// is untrusted input, and `parse_value` recurses once per level; without a cap
/// a line like `[[[[…]]]]` (a few KB) overflows the stack and aborts the whole
/// process (an uncatchable panic). 128 is far deeper than any real event value
/// yet shallow enough to stay well within the stack; beyond it we return a
/// clean `Err` instead of crashing.
const MAX_VALUE_DEPTH: usize = 128;

fn parse_value(s: &str) -> Result<Value, String> {
    parse_value_depth(s, 0)
}

fn parse_value_depth(s: &str, depth: usize) -> Result<Value, String> {
    if depth > MAX_VALUE_DEPTH {
        return Err(format!(
            "logged value nested deeper than the limit of {MAX_VALUE_DEPTH}"
        ));
    }
    let s = s.trim();
    if s == "null" {
        return Ok(Value::Null);
    }
    if s == "true" {
        return Ok(Value::Bool(true));
    }
    if s == "false" {
        return Ok(Value::Bool(false));
    }
    // Array
    if let Some(inner) = s.strip_prefix('[').and_then(|x| x.strip_suffix(']')) {
        let mut items = Vec::new();
        for part in split_top_level(inner, ',') {
            let part = part.trim();
            if !part.is_empty() {
                items.push(parse_value_depth(part, depth + 1)?);
            }
        }
        return Ok(Value::Array(items));
    }
    // Object
    if let Some(inner) = s.strip_prefix('{').and_then(|x| x.strip_suffix('}')) {
        let mut obj = BTreeMap::new();
        for part in split_top_level(inner, ',') {
            let part = part.trim();
            if part.is_empty() {
                continue;
            }
            let (k, v) = split_top_level_once(part, ':')
                .ok_or_else(|| format!("object field `{part}` missing `:`"))?;
            let k = unquote(k.trim());
            // A duplicate key within one record silently drops a binding under
            // last-wins; reject it, matching `parse_args` / `parse_entities`.
            if obj
                .insert(k.clone(), parse_value_depth(v.trim(), depth + 1)?)
                .is_some()
            {
                return Err(format!("record has a duplicate field `{k}`"));
            }
        }
        return Ok(Value::Object(obj));
    }
    // Entity ref: `Ns::Type::"id"` — has `::` and ends with a quoted id.
    // The id may contain escaped quotes (`\"`), so find the opening `::"` and
    // then scan forward for the unescaped closing `"`.
    if s.contains("::")
        && s.ends_with('"')
        && let Some(q) = find_entity_quote_open(s)
    {
        let ty = s[..q].to_string();
        let id_with_quotes = &s[q + 2..]; // includes opening and closing quotes
        let id = unquote(id_with_quotes);
        return Ok(Value::Entity { ty, id });
    }
    // Quoted string.
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        return Ok(Value::String(unquote(s)));
    }
    // Integer.
    if let Ok(n) = s.parse::<i64>() {
        return Ok(Value::Int(n));
    }
    // Decimal (contains a dot and parses as f64) -> keep as text.
    if s.contains('.') && s.parse::<f64>().is_ok() {
        return Ok(Value::Decimal(s.to_string()));
    }
    // Fallthrough: bare token as string.
    Ok(Value::String(s.to_string()))
}

fn unquote(s: &str) -> String {
    let s = s.trim().trim_matches('"');
    unescape(s)
}

/// Decode Cedar's canonical string escapes — the exact inverse of the
/// [`str::escape_debug`] form that [`super::value::entity_uid_string`] and the
/// quoted-value writers produce, and the form Cedar itself emits. Handles the
/// simple escapes `\" \\ \' \n \t \r \0`, the Unicode escape `\u{HH..}`, and the
/// legacy byte escape `\xHH`; an unrecognized `\<c>` is passed through verbatim
/// (`\` then `c`) so malformed input degrades rather than dropping characters.
///
/// This MUST stay the exact inverse of `entity_uid_string`'s escaping: the event
/// entity store is keyed by the escaped uid literal, and lookups reconstruct
/// that key from a decoded `(ty, id)`, so `unescape(escape(id)) == id` for all
/// ids (see the round-trip tests in `tests/entity_store.rs`).
pub(crate) fn unescape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('"') => out.push('"'),
            Some('\\') => out.push('\\'),
            Some('\'') => out.push('\''),
            Some('n') => out.push('\n'),
            Some('t') => out.push('\t'),
            Some('r') => out.push('\r'),
            Some('0') => out.push('\0'),
            // `\u{HH..}` — hex code point in braces.
            Some('u') if chars.peek() == Some(&'{') => {
                chars.next(); // consume `{`
                let mut hex = String::new();
                while let Some(&h) = chars.peek() {
                    if h == '}' {
                        break;
                    }
                    hex.push(h);
                    chars.next();
                }
                let closed = chars.peek() == Some(&'}');
                if closed {
                    chars.next(); // consume `}`
                }
                match (
                    closed,
                    u32::from_str_radix(&hex, 16).ok().and_then(char::from_u32),
                ) {
                    (true, Some(ch)) => out.push(ch),
                    // Malformed `\u{…}` — emit verbatim so nothing is silently lost.
                    _ => {
                        out.push_str("\\u{");
                        out.push_str(&hex);
                        if closed {
                            out.push('}');
                        }
                    }
                }
            }
            // `\xHH` — two-hex-digit byte escape.
            Some('x') => {
                let h1 = chars.peek().copied().filter(|c| c.is_ascii_hexdigit());
                let mut hex = String::new();
                if let Some(h) = h1 {
                    hex.push(h);
                    chars.next();
                    if let Some(&h2) = chars.peek() {
                        if h2.is_ascii_hexdigit() {
                            hex.push(h2);
                            chars.next();
                        }
                    }
                }
                match u32::from_str_radix(&hex, 16).ok().and_then(char::from_u32) {
                    Some(ch) => out.push(ch),
                    None => {
                        out.push_str("\\x");
                        out.push_str(&hex);
                    }
                }
            }
            // Unknown escape: keep the backslash and the char verbatim.
            Some(other) => {
                out.push('\\');
                out.push(other);
            }
            None => out.push('\\'),
        }
    }
    out
}

/// Find the position of the `::` that introduces the entity id's opening
/// quote in a string like `Ns::Type::"id"` where `id` may contain `\"`.
/// We scan for `::"` occurrences and check whether the closing `"` (after
/// skipping escapes) lands at the end of the string.
fn find_entity_quote_open(s: &str) -> Option<usize> {
    // Search for every `::` that is followed by `"`, then check if the
    // quoted span (respecting `\"`) reaches the final `"`.
    let mut search_from = 0;
    while let Some(pos) = s[search_from..].find("::\"") {
        let abs_pos = search_from + pos;
        let quote_start = abs_pos + 3; // byte after the opening `"`
        // Scan forward for the unescaped closing `"`.
        if let Some(close) = find_unescaped_quote(&s[quote_start..]) {
            let close_abs = quote_start + close;
            // The closing quote must be the last character of the string.
            if close_abs == s.len() - 1 {
                return Some(abs_pos);
            }
        }
        search_from = abs_pos + 3;
    }
    None
}

/// Find the byte offset of the first unescaped `"` in `s`.
fn find_unescaped_quote(s: &str) -> Option<usize> {
    let mut i = 0;
    let bytes = s.as_bytes();
    while i < bytes.len() {
        if bytes[i] == b'\\' {
            i += 2; // skip escaped char
        } else if bytes[i] == b'"' {
            return Some(i);
        } else {
            i += 1;
        }
    }
    None
}

/// Split `s` on top-level occurrences of `delim`, ignoring delimiters
/// inside `()`, `[]`, `{}`, or double quotes. Backslash-escaped quotes
/// (`\"`) inside a quoted string do not toggle the in-string state.
fn split_top_level(s: &str, delim: char) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut in_str = false;
    let mut cur = String::new();
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\\' if in_str => {
                cur.push(c);
                if let Some(&next) = chars.peek() {
                    cur.push(next);
                    chars.next();
                }
            }
            '"' => {
                in_str = !in_str;
                cur.push(c);
            }
            '(' | '[' | '{' if !in_str => {
                depth += 1;
                cur.push(c);
            }
            ')' | ']' | '}' if !in_str => {
                depth -= 1;
                cur.push(c);
            }
            _ if c == delim && depth == 0 && !in_str => {
                out.push(std::mem::take(&mut cur));
            }
            _ => cur.push(c),
        }
    }
    out.push(cur);
    out
}

/// Byte index of the closing `)` that matches an already-consumed opening
/// `(` at depth 0 — i.e. the first `)` seen while the bracket depth is back to
/// zero — honoring nested `()[]{}` and quoted strings. Used to delimit the
/// `entities(...)` envelope, whose attribute values contain nested brackets
/// and quoted strings that a naive `find(')')` would stop at prematurely.
/// Returns `None` if no matching `)` is found (unbalanced).
fn matching_paren(s: &str) -> Option<usize> {
    let mut depth = 0i32;
    let mut in_str = false;
    let mut chars = s.char_indices().peekable();
    while let Some((i, c)) = chars.next() {
        match c {
            '\\' if in_str => {
                chars.next(); // skip the escaped char
            }
            '"' => in_str = !in_str,
            '(' | '[' | '{' if !in_str => depth += 1,
            ')' | ']' | '}' if !in_str => {
                if depth == 0 && c == ')' {
                    return Some(i);
                }
                depth -= 1;
            }
            _ => {}
        }
    }
    None
}

/// Byte index of the `}` that matches the leading `{` of `s` (which must start
/// with `{`), honoring nesting and quoted strings. `None` if unbalanced or `s`
/// does not begin with `{`.
fn matching_brace(s: &str) -> Option<usize> {
    let mut depth = 0i32;
    let mut in_str = false;
    let mut chars = s.char_indices().peekable();
    while let Some((i, c)) = chars.next() {
        match c {
            '\\' if in_str => {
                chars.next(); // skip the escaped char
            }
            '"' => in_str = !in_str,
            '{' if !in_str => depth += 1,
            '}' if !in_str => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Byte index of the first top-level occurrence of `target` (depth 0, outside
/// a quoted string), or `None`. Honors nested `()[]{}` and quotes.
fn top_level_char(s: &str, target: char) -> Option<usize> {
    let mut depth = 0i32;
    let mut in_str = false;
    let mut chars = s.char_indices().peekable();
    while let Some((i, c)) = chars.next() {
        match c {
            '\\' if in_str => {
                chars.next();
            }
            '"' => in_str = !in_str,
            _ if c == target && depth == 0 && !in_str => return Some(i),
            '(' | '[' | '{' if !in_str => depth += 1,
            ')' | ']' | '}' if !in_str => depth -= 1,
            _ => {}
        }
    }
    None
}

/// Split on the FIRST top-level `delim` into `(left, right)`.
/// Backslash-escaped quotes (`\"`) inside a quoted string do not toggle
/// the in-string state.
fn split_top_level_once(s: &str, delim: char) -> Option<(&str, &str)> {
    let mut depth = 0i32;
    let mut in_str = false;
    let mut i = 0;
    let bytes = s.as_bytes();
    while i < bytes.len() {
        let c = bytes[i] as char;
        match c {
            '\\' if in_str => {
                // Skip the escaped character.
                i += 1;
                if i < bytes.len() {
                    i += 1;
                }
            }
            '"' => {
                in_str = !in_str;
                i += 1;
            }
            '(' | '[' | '{' if !in_str => {
                depth += 1;
                i += 1;
            }
            ')' | ']' | '}' if !in_str => {
                depth -= 1;
                i += 1;
            }
            _ if c == delim && depth == 0 && !in_str => {
                return Some((&s[..i], &s[i + c.len_utf8()..]));
            }
            _ => {
                i += 1;
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `unescape` is the exact inverse of the `escape_debug` escaping in
    /// `entity_uid_string` — the invariant the string-keyed entity store relies
    /// on. Round-trip every escape-worthy shape, including the control /
    /// whitespace ids the Cedar fuzz corpus uses (which the old `"`/`\`-only
    /// escaping mangled).
    #[test]
    fn unescape_inverts_entity_uid_escaping() {
        for id in [
            "alice",
            "a\"b",            // quote
            "a\\b",            // backslash
            "a'b",             // apostrophe (escape_debug emits \')
            "wDebian ",        // trailing space
            "  x",             // leading spaces
            "tab\there",       // tab
            "nl\nhere",        // newline
            "\u{0}\u{0}\u{4}", // NULs + control
            "=\u{e}",          // control mid-string (a real corpus shape)
            "café",            // non-ASCII letters (passed through)
            "emoji😀",
        ] {
            // The body between the quotes of `Ty::"…"`.
            let body: String = id.escape_debug().collect();
            assert_eq!(
                unescape(&body),
                id,
                "round-trip failed for {id:?} (escaped body {body:?})"
            );
        }
    }

    #[test]
    fn parse_entity_id_with_escaped_quote() {
        let log = r#"@0 scope(principal: Drupe::OAuthUser::"a\"b", resource: Drupe::Gateway::"gw1") Drupe::Action::"Transfer"::request(input: { user: "alice", amount: 10 }, callerPrincipal: Drupe::OAuthUser::"a\"b", callerResource: Drupe::Gateway::"gw1", requestId: "u1")"#;
        let trace = parse_trace(log);
        eprintln!("result: {trace:#?}");
        let trace = trace.expect("should parse");
        let e = &trace.points[0];
        // Scope principal should have the unescaped entity id.
        match &e.scope.principal {
            Some(Value::Entity { ty, id }) => {
                assert_eq!(ty, "Drupe::OAuthUser");
                assert_eq!(id, "a\"b");
            }
            other => panic!("expected entity, got {other:?}"),
        }
        // The callerPrincipal field should also parse correctly.
        match e.event.logged.get("callerPrincipal") {
            Some(Value::Entity { ty, id }) => {
                assert_eq!(ty, "Drupe::OAuthUser");
                assert_eq!(id, "a\"b");
            }
            other => panic!("expected entity field, got {other:?}"),
        }
    }

    #[test]
    fn parse_string_field_with_escaped_quote() {
        let log = r#"@0 scope(principal: Drupe::OAuthUser::"alice", resource: Drupe::Gateway::"gw1") Drupe::Action::"Transfer"::request(input: { user: "o\"brien" }, callerPrincipal: Drupe::OAuthUser::"alice", callerResource: Drupe::Gateway::"gw1", requestId: "u1")"#;
        let trace = parse_trace(log).expect("should parse");
        let e = &trace.points[0];
        let input = e.event.logged.get("input").expect("input field");
        match input {
            Value::Object(map) => {
                assert_eq!(
                    map.get("user"),
                    Some(&Value::String("o\"brien".to_string()))
                );
            }
            other => panic!("expected object, got {other:?}"),
        }
    }

    // ─── entities(...) envelope (stage 3) ────────────────────────────

    /// A line with no `entities(...)` still parses, with an empty store.
    #[test]
    fn no_entities_envelope_yields_empty_store() {
        let log = r#"@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") Svc::Action::"Read"::request(input: { doc: "x" })"#;
        let e = &parse_trace(log).expect("parses").points[0];
        assert!(e.event.entities.is_empty());
    }

    /// A single entity with attributes; the uid (which contains `::`) keys the
    /// store and the `{ … }` body becomes its attribute map.
    #[test]
    fn single_entity_with_attributes() {
        let log = r#"@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") entities(Svc::User::"alice": { dept: "eng", level: 5 }) Svc::Action::"Read"::request(input: { doc: "x" })"#;
        let e = &parse_trace(log).expect("parses").points[0];
        let rec = e
            .event
            .entities
            .get("Svc::User::\"alice\"")
            .expect("alice's record");
        assert_eq!(
            rec.attrs.get("dept"),
            Some(&Value::String("eng".to_string()))
        );
        assert_eq!(rec.attrs.get("level"), Some(&Value::Int(5)));
        assert!(rec.parents.is_empty(), "no `in` clause ⇒ no parents");
    }

    /// Multiple entities on one line, including an empty-attrs entity (present
    /// without attributes — e.g. a group for `in`).
    #[test]
    fn multiple_entities_including_empty_attrs() {
        let log = r#"@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") entities(Svc::User::"alice": { dept: "eng" }, Svc::Group::"admins": {}) Svc::Action::"Read"::request(input: { doc: "x" })"#;
        let store = &parse_trace(log).expect("parses").points[0].event.entities;
        assert_eq!(store.len(), 2);
        assert_eq!(
            store
                .get("Svc::User::\"alice\"")
                .and_then(|r| r.attrs.get("dept")),
            Some(&Value::String("eng".to_string()))
        );
        assert!(
            store
                .get("Svc::Group::\"admins\"")
                .expect("group present")
                .attrs
                .is_empty(),
            "empty-attrs entity is present with no attributes"
        );
    }
    /// An entity id containing a single quote is keyed by its CANONICAL (escaped)
    /// literal, whichever way the trace spells it — Cedar's canonical form escapes
    /// `'` as `\'`.
    #[test]
    fn quoted_id_is_keyed_canonically_from_either_spelling() {
        // Cedar's canonical key for the id `o'brien`.
        let canonical = "Svc::User::\"o\\'brien\"";

        for spelling in [r#"Svc::User::"o'brien""#, r#"Svc::User::"o\'brien""#] {
            let log = format!(
                r#"@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") entities({spelling}: {{ dept: "eng" }}) Svc::Action::"Read"::request(input: {{ doc: "x" }})"#
            );
            let store = &parse_trace(&log).expect("parses").points[0].event.entities;
            assert_eq!(
                store.keys().collect::<Vec<_>>(),
                vec![canonical],
                "`{spelling}` must be keyed by its canonical literal"
            );
            assert_eq!(
                store.get(canonical).and_then(|r| r.attrs.get("dept")),
                Some(&Value::String("eng".to_string())),
                "attrs reachable under the canonical key for `{spelling}`"
            );
        }
    }

    /// The canonical key is exactly what a lookup reconstructs from a decoded
    /// `(ty, id)` — the invariant `entity_uid_string` documents. This ties the two
    /// halves together: if either side changed, this breaks.
    #[test]
    fn quoted_id_key_matches_what_lookups_reconstruct() {
        let log = r#"@0 scope(principal: Svc::User::"o'brien", resource: Svc::Gateway::"gw1") entities(Svc::User::"o'brien": { dept: "eng" }) Svc::Action::"Read"::request(input: { doc: "x" })"#;
        let event = &parse_trace(log).expect("parses").points[0].event;
        assert_eq!(
            event.entities.keys().collect::<Vec<_>>(),
            vec![&super::super::value::entity_uid_string(
                "Svc::User",
                "o'brien"
            )],
            "store key must equal the key a lookup builds from (ty, id)"
        );
        // And the lookup path itself resolves through it.
        assert_eq!(
            event.resolve_entity_attr("Svc::User", "o'brien", &["dept".to_string()]),
            Some(Value::String("eng".to_string())),
            "resolve_entity_attr must find the quoted-id entity"
        );
    }

    /// An entities key that is not an entity ref is rejected at trace-parse time
    /// rather than deferred to Cedar.
    #[test]
    fn non_entity_ref_entities_key_is_rejected() {
        let log = r#"@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") entities(notAUid: { dept: "eng" }) Svc::Action::"Read"::request(input: { doc: "x" })"#;
        let err = parse_trace(log).expect_err("non-entity-ref key must be rejected");
        assert!(
            format!("{err}").contains("not an entity ref"),
            "expected a `not an entity ref` error, got: {err}"
        );
    }

    /// An entity with a trailing `in [ … ]` clause: its attrs parse as usual and
    /// its direct parents populate `EntityRecord.parents` as entity refs.
    #[test]
    fn entity_with_parents_clause() {
        let log = r#"@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") entities(Svc::Group::"admins": {}, Svc::Group::"eng": {}, Svc::User::"alice": { dept: "eng" } in [Svc::Group::"admins", Svc::Group::"eng"]) Svc::Action::"Read"::request(input: { doc: "x" })"#;
        let store = &parse_trace(log).expect("parses").points[0].event.entities;
        let alice = store.get("Svc::User::\"alice\"").expect("alice present");
        assert_eq!(
            alice.attrs.get("dept"),
            Some(&Value::String("eng".to_string()))
        );
        assert_eq!(
            alice.parents,
            vec![
                Value::Entity {
                    ty: "Svc::Group".to_string(),
                    id: "admins".to_string()
                },
                Value::Entity {
                    ty: "Svc::Group".to_string(),
                    id: "eng".to_string()
                },
            ],
            "direct parents parse as entity refs in order"
        );
    }

    /// An empty-attrs entity may still carry parents: `{} in [ … ]`.
    #[test]
    fn empty_attrs_entity_with_parents() {
        let log = r#"@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") entities(Svc::Group::"root": {}, Svc::Group::"admins": {} in [Svc::Group::"root"]) Svc::Action::"Read"::request(input: { doc: "x" })"#;
        let store = &parse_trace(log).expect("parses").points[0].event.entities;
        let admins = store.get("Svc::Group::\"admins\"").expect("admins present");
        assert!(admins.attrs.is_empty());
        assert_eq!(
            admins.parents,
            vec![Value::Entity {
                ty: "Svc::Group".to_string(),
                id: "root".to_string()
            }]
        );
    }

    /// Non-entity-ref parent is rejected (a parent must be `Ns::Type::"id"`).
    #[test]
    fn non_entity_parent_is_rejected() {
        let log = r#"@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") entities(Svc::User::"alice": {} in ["not-an-entity"]) Svc::Action::"Read"::request(input: { doc: "x" })"#;
        assert!(parse_trace(log).is_err(), "string parent must be rejected");
    }

    /// An attribute whose value is itself an entity ref, and a nested record —
    /// the closing `)` scan and the `{`-split must not trip on the inner `::`,
    /// `{}`, or the entity-ref value.
    #[test]
    fn entity_attribute_values_nested_and_entity_ref() {
        let log = r#"@0 scope(principal: Svc::User::"alice", resource: Svc::Doc::"d1") entities(Svc::Doc::"d1": { owner: Svc::User::"bob", meta: { tag: "x" } }) Svc::Action::"Read"::request(input: { doc: "x" })"#;
        let attrs = parse_trace(log).expect("parses").points[0]
            .event
            .entities
            .get("Svc::Doc::\"d1\"")
            .expect("doc attrs")
            .attrs
            .clone();
        assert_eq!(
            attrs.get("owner"),
            Some(&Value::Entity {
                ty: "Svc::User".to_string(),
                id: "bob".to_string()
            })
        );
        match attrs.get("meta") {
            Some(Value::Object(m)) => {
                assert_eq!(m.get("tag"), Some(&Value::String("x".to_string())))
            }
            other => panic!("expected nested record, got {other:?}"),
        }
    }

    /// An `entities(...)` with a string attribute containing `)` and `{` — the
    /// depth/in-string aware scan must not close the envelope early.
    #[test]
    fn entity_attribute_string_with_brackets_and_paren() {
        let log = r#"@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") entities(Svc::User::"alice": { note: "a) { weird" }) Svc::Action::"Read"::request(input: { doc: "x" })"#;
        let attrs = parse_trace(log).expect("parses").points[0]
            .event
            .entities
            .get("Svc::User::\"alice\"")
            .expect("alice attrs")
            .attrs
            .clone();
        assert_eq!(
            attrs.get("note"),
            Some(&Value::String("a) { weird".to_string()))
        );
    }

    /// A missing `)` on the envelope is a parse error, not a silent truncation.
    #[test]
    fn unterminated_entities_envelope_errors() {
        let log = r#"@0 entities(Svc::User::"alice": { dept: "eng" } Svc::Action::"Read"::request(input: { doc: "x" })"#;
        assert!(
            parse_trace(log).is_err(),
            "unbalanced entities(...) must error"
        );
    }

    // ─── request_context(...) envelope ───────────────────────────────

    /// A line with no `request_context(...)` still parses, with an empty
    /// request-context bag (distinct from the trailing logged group).
    #[test]
    fn no_request_context_envelope_yields_empty_bag() {
        let log = r#"@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") Svc::Action::"Read"::request(input: { doc: "x" })"#;
        let e = &parse_trace(log).expect("parses").points[0];
        assert!(
            e.event.request_context.is_empty(),
            "no request_context(...) → empty request-context bag"
        );
        // The trailing group still populates `logged`.
        assert!(e.event.logged.contains_key("input"));
    }

    /// `request_context(...)` groups populate the request-context bag by group
    /// name, with nested records descending (the value nests, so the closing
    /// `)` needs the depth/in-string scan — a naive `find(')')` on
    /// `{ now: "...)..." }` would close early).
    #[test]
    fn request_context_groups_parse_into_the_bag() {
        let log = r#"@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") request_context(input: { doc: "x" }, system: { hour: 10 }) Svc::Action::"Read"::request(input: { doc: "x" })"#;
        let e = &parse_trace(log).expect("parses").points[0];
        // `input` group present in request_context.
        match e.event.request_context.get("input") {
            Some(Value::Object(m)) => {
                assert_eq!(m.get("doc"), Some(&Value::String("x".to_string())))
            }
            other => panic!("expected input record, got {other:?}"),
        }
        // A non-`input` group is carried too.
        match e.event.request_context.get("system") {
            Some(Value::Object(m)) => assert_eq!(m.get("hour"), Some(&Value::Int(10))),
            other => panic!("expected system record, got {other:?}"),
        }
    }

    /// A `request_context` value string containing `)` and `{` must not close
    /// the envelope early — same depth/in-string-aware scan as `entities(...)`.
    #[test]
    fn request_context_string_with_brackets_and_paren() {
        let log = r#"@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") request_context(system: { note: "a) { weird" }) Svc::Action::"Read"::request(input: { doc: "x" })"#;
        let e = &parse_trace(log).expect("parses").points[0];
        match e.event.request_context.get("system") {
            Some(Value::Object(m)) => {
                assert_eq!(
                    m.get("note"),
                    Some(&Value::String("a) { weird".to_string()))
                )
            }
            other => panic!("expected system record, got {other:?}"),
        }
    }

    /// `request_context(...)` sits *after* `entities(...)`; both envelopes on
    /// one line parse into their respective bags without interfering.
    #[test]
    fn request_context_after_entities_envelope() {
        let log = r#"@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") entities(Svc::User::"alice": { dept: "eng" }) request_context(input: { doc: "x" }) Svc::Action::"Read"::request(input: { doc: "x" })"#;
        let e = &parse_trace(log).expect("parses").points[0];
        assert_eq!(
            e.event
                .entities
                .get("Svc::User::\"alice\"")
                .and_then(|r| r.attrs.get("dept")),
            Some(&Value::String("eng".to_string())),
            "entities envelope parsed"
        );
        assert!(
            e.event.request_context.contains_key("input"),
            "request_context envelope parsed after entities"
        );
    }

    /// A missing `)` on the `request_context(...)` envelope is a parse error,
    /// not a silent truncation.
    #[test]
    fn unterminated_request_context_envelope_errors() {
        let log = r#"@0 request_context(input: { doc: "x" } Svc::Action::"Read"::request(input: { doc: "x" })"#;
        assert!(
            parse_trace(log).is_err(),
            "unbalanced request_context(...) must error"
        );
    }

    // ─── duplicate-key rejection (parse-strict) ──────────────────────
    //
    // A duplicate key would silently drop a binding under last-wins, and the
    // decision alone cannot tell the author which survived — so every group
    // map (`entities(...)`, `scope(...)`, `request_context(...)`, the trailing
    // logged group, and nested records) rejects a duplicate, matching the
    // unbalanced-envelope strictness.

    #[test]
    fn duplicate_uid_in_entities_envelope_errors() {
        let log = r#"@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") entities(Svc::User::"alice": { dept: "eng" }, Svc::User::"alice": { dept: "sales" }) Svc::Action::"Read"::request(input: { doc: "x" })"#;
        let e = parse_trace(log);
        assert!(e.is_err(), "duplicate uid must error, not last-wins");
        assert!(
            e.unwrap_err().contains("duplicate uid"),
            "error should name the duplicate uid"
        );
    }

    #[test]
    fn duplicate_key_in_scope_envelope_errors() {
        // The `scope(...)` envelope also goes through `parse_args`; a duplicate
        // `principal:` (or `resource:`) must error on the duplicate-field guard
        // rather than silently keeping the last binding.
        let log = r#"@0 scope(principal: Svc::User::"alice", principal: Svc::User::"bob", resource: Svc::Gateway::"gw1") Svc::Action::"Read"::request(input: { doc: "x" })"#;
        let err = parse_trace(log).expect_err("duplicate scope key must error");
        assert!(
            err.contains("duplicate field `principal`"),
            "want the parse_args duplicate-field guard, got: {err}"
        );
    }

    #[test]
    fn duplicate_field_in_request_context_errors() {
        // The `request_context(...)` group goes through `parse_args`; a
        // duplicate group name must error on the duplicate-field guard (asserted
        // on the message so it can't pass for an unrelated parse failure).
        let log = r#"@0 scope(principal: Svc::User::"alice", resource: Svc::Gateway::"gw1") request_context(input: { doc: "x" }, input: { doc: "y" }) Svc::Action::"Read"::request(input: { doc: "x" })"#;
        let err = parse_trace(log).expect_err("duplicate request_context group must error");
        assert!(
            err.contains("duplicate field `input`"),
            "want the parse_args duplicate-field guard, got: {err}"
        );
    }

    #[test]
    fn duplicate_field_in_logged_group_errors() {
        // The trailing logged group also goes through `parse_args`.
        let log = r#"@0 Svc::Action::"Read"::request(input: { doc: "x" }, input: { doc: "y" })"#;
        let err = parse_trace(log).expect_err("duplicate top-level logged field must error");
        assert!(
            err.contains("duplicate field `input`"),
            "want the parse_args duplicate-field guard, got: {err}"
        );
    }

    #[test]
    fn duplicate_key_in_nested_record_errors() {
        // A duplicate key *within* a record goes through `parse_value`'s object
        // branch, which emits its own distinct message.
        let log = r#"@0 Svc::Action::"Read"::request(input: { doc: "x", doc: "y" })"#;
        let err = parse_trace(log).expect_err("duplicate key within a record must error");
        assert!(
            err.contains("record has a duplicate field `doc`"),
            "want the parse_value record duplicate-field guard, got: {err}"
        );
    }
}
