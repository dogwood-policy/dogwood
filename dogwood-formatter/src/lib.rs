//! Source-preserving formatting for Dogwood (`.dw`) policy files.
//!
//! Formatting uses Dogwood's shared concrete-syntax grammar and lossless token
//! stream rather than the semantic AST. The semantic AST is macro-expanded and
//! does not retain comments or authored operator spelling, while a formatter
//! must preserve all of those.
//!
//! The layout follows the policy-oriented shape used by Dogwood's policy
//! tooling:
//!
//! - top-level declarations and policies are separated by a blank line;
//! - annotations and `when` / `unless` clauses start on their own lines;
//! - groups that exceed 80 columns break first at top-level commas, then at
//!   top-level `&&` / `||`;
//! - continuation lines use two spaces per nesting level.
//!
//! If the source does not parse, cannot be tokenized losslessly, or contains a
//! comment embedded in a statement, it is returned unchanged.

use dogwood_syntax::{Document, Item, Token};

const LINE_WIDTH: usize = 80;
const INDENT: &str = "  ";

/// Pretty-print a Dogwood policy set, preserving every non-whitespace token.
///
/// The returned string has no forced trailing newline. The `dogwood format`
/// command adds one when writing non-empty output to a terminal or pipeline.
///
/// Inputs that cannot be laid out safely are returned unchanged. This makes
/// formatting suitable for editor/save hooks: incomplete source is never
/// rewritten into a different token stream.
pub fn format_policies(source: &str) -> String {
    let (bom, source) = dogwood_syntax::split_bom(source);
    let Ok(tokens) = dogwood_syntax::tokenize(source) else {
        return format!("{bom}{source}");
    };
    let Ok(document) = dogwood_syntax::parse_document(source) else {
        return format!("{bom}{source}");
    };
    let Some(items) = top_level_items(source, &tokens, &document) else {
        return format!("{bom}{source}");
    };
    if items.is_empty() {
        return format!("{bom}{source}");
    }

    let mut output = String::from(bom);
    let mut previous = None;
    for item in items {
        let kind = item.kind();
        if let Some(previous) = previous {
            match (previous, kind) {
                (ItemKind::Comment, ItemKind::Comment) => output.push('\n'),
                (ItemKind::Comment, ItemKind::Statement) => output.push('\n'),
                (ItemKind::Statement, ItemKind::Comment)
                | (ItemKind::Statement, ItemKind::Statement) => output.push_str("\n\n"),
            }
        }
        match item {
            TopLevelItem::Comment(text) => output.push_str(text.trim_end()),
            TopLevelItem::Statement(text) => output.push_str(&text),
        }
        previous = Some(kind);
    }
    output
}

fn opening_delimiter(token: Token<'_>) -> Option<char> {
    match token.text {
        "(" => Some(')'),
        "[" => Some(']'),
        "{" => Some('}'),
        _ => None,
    }
}

fn is_closing_delimiter(token: Token<'_>) -> bool {
    matches!(token.text, ")" | "]" | "}")
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ItemKind {
    Comment,
    Statement,
}

enum TopLevelItem<'a> {
    Comment(&'a str),
    Statement(String),
}

impl TopLevelItem<'_> {
    fn kind(&self) -> ItemKind {
        match self {
            TopLevelItem::Comment(_) => ItemKind::Comment,
            TopLevelItem::Statement(_) => ItemKind::Statement,
        }
    }
}

fn top_level_items<'source>(
    source: &'source str,
    tokens: &[Token<'source>],
    document: &Document,
) -> Option<Vec<TopLevelItem<'source>>> {
    let mut items = Vec::new();
    let mut cursor = 0;
    for statement in &document.items {
        append_top_level_comments(tokens, cursor, statement.span.start, &mut items)?;
        if tokens
            .iter()
            .any(|token| token.is_comment() && statement.span.contains(token.span))
        {
            return None;
        }
        items.push(TopLevelItem::Statement(format_statement(
            source, statement,
        )?));
        cursor = statement.span.end;
    }
    append_top_level_comments(tokens, cursor, source.len(), &mut items)?;
    Some(items)
}

fn append_top_level_comments<'source>(
    tokens: &[Token<'source>],
    start: usize,
    end: usize,
    items: &mut Vec<TopLevelItem<'source>>,
) -> Option<()> {
    for &token in tokens
        .iter()
        .filter(|token| token.span.start < end && token.span.end > start)
    {
        if token.span.start < start || token.span.end > end {
            return None;
        }
        if token.is_comment() {
            items.push(TopLevelItem::Comment(token.text));
        } else if !token.is_whitespace() {
            return None;
        }
    }
    Some(())
}

fn format_statement(source: &str, statement: &Item) -> Option<String> {
    let mut lines = Vec::new();
    for span in &statement.line_parts {
        let tokens = dogwood_syntax::tokenize(span.text(source)).ok()?;
        let line = lay_out(&tokens, 0);
        if !line.is_empty() {
            lines.push(line);
        }
    }
    Some(lines.join("\n"))
}

fn lay_out(parts: &[Token<'_>], depth: usize) -> String {
    let indent = INDENT.chars().count() * depth;
    let text = flat(parts);
    if indent + text.chars().count() <= LINE_WIDTH {
        return text;
    }

    let mut line = String::new();
    let mut index = 0;
    while index < parts.len() {
        let part = parts[index];
        if opening_delimiter(part).is_some() {
            let end = group_end(parts, index);
            let inner = &parts[index + 1..end];
            // Render the inline group exactly as the top-level `flat(parts)`
            // width check measured it, so a group that fits is emitted
            // byte-for-byte the way it was measured. Rebuilding it as
            // `open + flat(inner) + close` would strip the inner slice's
            // padding, making the next `format` pass measure shorter text and
            // collapse the layout — i.e. formatting would not be idempotent.
            let whole = flat(&parts[index..=end]);
            let last_line_len = line
                .rsplit('\n')
                .next()
                .map(str::chars)
                .map(Iterator::count)
                .unwrap_or(0);
            let implicit_indent = if line.contains('\n') { 0 } else { indent };
            // The fit check must also account for whatever stays on this line
            // after the closing delimiter (e.g. a trailing `;` or a method
            // call), or an inline group that just fits can push the full line
            // past the width target on the next pass.
            let trailing_len = flat(&parts[end + 1..]).chars().count();
            if flat(inner).is_empty()
                || implicit_indent + last_line_len + whole.chars().count() + trailing_len
                    <= LINE_WIDTH
            {
                line.push_str(&whole);
            } else {
                let items = split_items(inner);
                line.push_str(part.text);
                line.push('\n');
                for (item_index, item) in items.iter().enumerate() {
                    if item_index > 0 {
                        line.push('\n');
                    }
                    line.push_str(&INDENT.repeat(depth + 1));
                    line.push_str(&lay_out(item, depth + 1));
                }
                line.push('\n');
                line.push_str(&INDENT.repeat(depth));
                line.push_str(parts[end].text);
            }
            index = end + 1;
        } else {
            if part.is_whitespace() {
                line.push(' ');
            } else {
                line.push_str(part.text);
            }
            index += 1;
        }
    }
    line.trim().to_string()
}

fn split_items<'tokens, 'source>(
    parts: &'tokens [Token<'source>],
) -> Vec<&'tokens [Token<'source>]> {
    for separators in [&[","][..], &["&&", "||"][..]] {
        let mut items = Vec::new();
        let mut start = 0;
        let mut depth = 0_isize;

        for (index, &part) in parts.iter().enumerate() {
            if depth == 0 && separators.contains(&part.text) {
                if part.text == "," {
                    items.push(trimmed(&parts[start..=index]));
                    start = index + 1;
                } else {
                    items.push(trimmed(&parts[start..index]));
                    start = index;
                }
                continue;
            }
            depth += depth_change(part);
        }
        items.push(trimmed(&parts[start..]));
        items.retain(|item| !flat(item).is_empty());
        if items.len() > 1 {
            return items;
        }
    }
    vec![trimmed(parts)]
}

fn group_end(parts: &[Token<'_>], start: usize) -> usize {
    let mut depth = 0_isize;
    for (index, &part) in parts.iter().enumerate().skip(start) {
        depth += depth_change(part);
        if depth == 0 {
            return index;
        }
    }
    parts.len().saturating_sub(1)
}

fn depth_change(token: Token<'_>) -> isize {
    if opening_delimiter(token).is_some() {
        1
    } else if is_closing_delimiter(token) {
        -1
    } else {
        0
    }
}

fn trimmed<'tokens, 'source>(mut parts: &'tokens [Token<'source>]) -> &'tokens [Token<'source>] {
    while parts.first().is_some_and(|token| token.is_whitespace()) {
        parts = &parts[1..];
    }
    while parts.last().is_some_and(|token| token.is_whitespace()) {
        parts = &parts[..parts.len() - 1];
    }
    parts
}

fn flat(parts: &[Token<'_>]) -> String {
    let mut output = String::new();
    for &part in trimmed(parts) {
        if part.is_whitespace() {
            output.push(' ');
        } else {
            output.push_str(part.text);
        }
    }
    output
}

#[cfg(test)]
mod tests {
    use super::format_policies;

    const GATEWAY: &str = "Drupe::Gateway::\"arn:xxxxxxx:111111111111:gateway/helpdesk\"";

    fn temporal_policy() -> String {
        format!(
            "@id(\"policy_6\")\n\
             forbid (principal, action == Drupe::Action::\"grant_access\", \
             resource == {GATEWAY}) unless temporal {{ formerly within 24h \
             Drupe::Action::\"verify_identity\"::request{{ input.user_name: \
             context.input.user_name, input.method: \"manager\", eventPrincipal: principal, \
             eventResource: resource }} }};"
        )
    }

    #[test]
    fn formats_a_long_temporal_policy() {
        assert_eq!(
            format_policies(&temporal_policy()),
            format!(
                concat!(
                    "@id(\"policy_6\")\n",
                    "forbid (\n",
                    "  principal,\n",
                    "  action == Drupe::Action::\"grant_access\",\n",
                    "  resource == {}\n",
                    ")\n",
                    "unless temporal {{\n",
                    "  formerly within 24h ",
                    "Drupe::Action::\"verify_identity\"::request{{\n",
                    "    input.user_name: context.input.user_name,\n",
                    "    input.method: \"manager\",\n",
                    "    eventPrincipal: principal,\n",
                    "    eventResource: resource\n",
                    "  }}\n",
                    "}};"
                ),
                GATEWAY
            )
        );
    }

    #[test]
    fn breaks_a_long_condition_before_boolean_operators() {
        let source = "forbid (principal, action, resource) when { \
            context.input.amount > 1000 && context.input.currency == \"USD\" \
            && context.input.approved == false };";
        assert_eq!(
            format_policies(source),
            concat!(
                "forbid (principal, action, resource)\n",
                "when {\n",
                "  context.input.amount > 1000\n",
                "  && context.input.currency == \"USD\"\n",
                "  && context.input.approved == false\n",
                "};"
            )
        );
    }

    #[test]
    fn separates_annotations_policies_and_declarations() {
        let source = "@id(\"a\") permit (principal, action, resource); \
            def cedar allowed(?value) { ?value == true }; \
            @id(\"b\") forbid (principal, action, resource);";
        assert_eq!(
            format_policies(source),
            "@id(\"a\")\n\
             permit (principal, action, resource);\n\n\
             def cedar allowed(?value) { ?value == true };\n\n\
             @id(\"b\")\n\
             forbid (principal, action, resource);"
        );
    }

    #[test]
    fn preserves_strings_verbatim() {
        let source = format!(
            "forbid (principal, action, resource == {GATEWAY}) when \
             {{ context.input.note like \"*a,  b ( }} //*\" }};"
        );
        assert!(format_policies(&source).contains("like \"*a,  b ( } //*\""));
    }

    #[test]
    fn preserves_standalone_comments_and_formats_the_policy_after_them() {
        let source = "// allow lookups\n\
            permit (principal, action, resource) when { true };";
        assert_eq!(
            format_policies(source),
            "// allow lookups\n\
             permit (principal, action, resource)\n\
             when { true };"
        );
    }

    #[test]
    fn leaves_embedded_comments_and_invalid_source_unchanged() {
        for source in [
            "permit (principal, action, resource) when { // why\ntrue };",
            "permit (principal, action, resource when { true };",
            "permit (principal, action, resource) when { \"unfinished };",
            "permit ( principal, action, resource ) when { true } trailing;",
        ] {
            assert_eq!(format_policies(source), source);
        }
    }

    #[test]
    fn does_not_double_count_indent_after_an_internal_break() {
        let values = (0..30).map(|_| "\"a\"").collect::<Vec<_>>().join(", ");
        for pad in [53, 54] {
            let padded = "x".repeat(pad);
            let source = format!(
                "permit (principal, action, resource) when {{ \
                 [{values}].containsAll([\"{padded}\", \"y\"]) && true }};"
            );
            let formatted = format_policies(&source);
            let group = format!("  ].containsAll([\"{padded}\", \"y\"])");
            assert!(
                formatted.contains(&group),
                "a {width}-column line was broken prematurely:\n{formatted}",
                width = group.chars().count()
            );
        }
    }

    #[test]
    fn formatting_is_idempotent_across_padding_widths() {
        // A group whose padded form crosses the width boundary used to break on
        // the first pass and then collapse — producing different output and an
        // over-width line — on the second. Sweeping the padding exercises both
        // sides of the inline-fit decision, so a second `format` pass must
        // reproduce the first byte-for-byte and never exceed the width target.
        for pad in 0..24 {
            let a = "a".repeat(pad);
            let source = format!(
                "permit (principal, action, resource) when {{ if [ \"{a}\" ].contains(\"a\") \
                 then [ \"b\" ].contains(\"b\") else [ \"c\" ].contains(\"c\") }};"
            );
            let once = format_policies(&source);
            let twice = format_policies(&once);
            assert_eq!(
                once, twice,
                "formatting is not idempotent for pad={pad}:\n--- once ---\n{once}\n--- twice ---\n{twice}"
            );
            let widest = once
                .lines()
                .map(|line| line.chars().count())
                .max()
                .unwrap_or(0);
            assert!(
                widest <= 80,
                "pad={pad} produced a {widest}-column line, over the 80-column target:\n{once}"
            );
        }
    }

    #[test]
    fn formatting_is_idempotent_and_changes_only_whitespace() {
        let source = temporal_policy();
        let once = format_policies(&source);
        assert_eq!(format_policies(&once), once);
        assert_eq!(
            source
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect::<String>(),
            once.chars()
                .filter(|c| !c.is_whitespace())
                .collect::<String>()
        );
    }

    #[test]
    fn preserves_a_byte_order_mark() {
        let source = "\u{feff}permit (principal, action, resource) when { true };";
        assert_eq!(
            format_policies(source),
            "\u{feff}permit (principal, action, resource)\nwhen { true };"
        );
    }
}
