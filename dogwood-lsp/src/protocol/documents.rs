use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use dogwood_lsp::project::file_uri_to_path;
use lsp_types::{
    Position, Range, TextDocumentContentChangeEvent, TextDocumentItem, Uri,
    VersionedTextDocumentIdentifier,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Document {
    version: i32,
    revision: u64,
    kind: DocumentKind,
    text: Arc<str>,
    path: PathBuf,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum DocumentKind {
    Policy,
    EventSchema,
    Dependency,
}

impl Document {
    pub(crate) fn text(&self) -> &str {
        &self.text
    }

    pub(crate) fn text_snapshot(&self) -> Arc<str> {
        Arc::clone(&self.text)
    }

    pub(crate) fn version(&self) -> i32 {
        self.version
    }

    pub(crate) fn revision(&self) -> u64 {
        self.revision
    }

    pub(crate) fn path(&self) -> &Path {
        &self.path
    }

    pub(crate) const fn kind(&self) -> DocumentKind {
        self.kind
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum DocumentError {
    UnsupportedDocument,
    DuplicateOpen,
    DocumentNotOpen,
    VersionNotNewer,
    EmptyChanges,
    InvalidRange,
    InvalidRangeLength,
}

impl fmt::Display for DocumentError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let message = match self {
            Self::UnsupportedDocument => {
                "only supported Dogwood document kinds on unambiguous file URIs are accepted"
            }
            Self::DuplicateOpen => "document is already open",
            Self::DocumentNotOpen => "document is not open",
            Self::VersionNotNewer => "document version is not newer",
            Self::EmptyChanges => "contentChanges must not be empty",
            Self::InvalidRange => "change range is not a valid UTF-16 document range",
            Self::InvalidRangeLength => "rangeLength does not match the UTF-16 change range",
        };
        formatter.write_str(message)
    }
}

impl Error for DocumentError {}

#[derive(Debug, Default)]
pub(crate) struct DocumentStore {
    documents: HashMap<Uri, Document>,
    paths: HashMap<PathBuf, Uri>,
    disk_revisions: HashMap<PathBuf, u64>,
    next_revision: u64,
}

impl DocumentStore {
    pub(crate) fn open(
        &mut self,
        item: TextDocumentItem,
        is_explicit_dependency: impl FnOnce(&Path) -> bool,
    ) -> Result<(), DocumentError> {
        let path = file_uri_to_path(&item.uri).map_err(|_| DocumentError::UnsupportedDocument)?;
        let explicit_dependency = is_explicit_dependency(&path);
        let kind = document_kind(&path, &item.language_id, explicit_dependency)
            .ok_or(DocumentError::UnsupportedDocument)?;
        if self.documents.contains_key(&item.uri) || self.paths.contains_key(&path) {
            return Err(DocumentError::DuplicateOpen);
        }

        let revision = self.allocate_revision();
        self.paths.insert(path.clone(), item.uri.clone());
        self.documents.insert(
            item.uri,
            Document {
                version: item.version,
                revision,
                kind,
                text: Arc::from(item.text),
                path,
            },
        );
        Ok(())
    }

    pub(crate) fn change(
        &mut self,
        identifier: VersionedTextDocumentIdentifier,
        changes: Vec<TextDocumentContentChangeEvent>,
    ) -> Result<(), DocumentError> {
        let document = self
            .documents
            .get(&identifier.uri)
            .ok_or(DocumentError::DocumentNotOpen)?;

        if identifier.version <= document.version {
            return Err(DocumentError::VersionNotNewer);
        }
        if changes.is_empty() {
            return Err(DocumentError::EmptyChanges);
        }

        let mut text = document.text().to_owned();
        for change in changes {
            apply_change(&mut text, change)?;
        }

        let revision = self.allocate_revision();
        let document = self
            .documents
            .get_mut(&identifier.uri)
            .expect("document was checked above");
        document.version = identifier.version;
        document.revision = revision;
        document.text = Arc::from(text);
        Ok(())
    }

    pub(crate) fn close(&mut self, uri: &Uri) -> Result<(), DocumentError> {
        let document = self
            .documents
            .remove(uri)
            .ok_or(DocumentError::DocumentNotOpen)?;
        self.paths.remove(document.path());
        Ok(())
    }

    pub(crate) fn note_disk_change(&mut self, path: PathBuf) {
        let revision = self.allocate_revision();
        self.disk_revisions.insert(path, revision);
    }

    pub(crate) fn disk_revision(&self, path: &Path) -> u64 {
        self.disk_revisions.get(path).copied().unwrap_or(0)
    }

    pub(crate) fn get(&self, uri: &Uri) -> Option<&Document> {
        self.documents.get(uri)
    }

    pub(crate) fn get_by_path(&self, path: &Path) -> Option<(&Uri, &Document)> {
        let uri = self.paths.get(path)?;
        self.documents.get_key_value(uri)
    }

    pub(crate) fn contains_path(&self, path: &Path) -> bool {
        self.paths.contains_key(path)
    }

    pub(crate) fn paths(&self) -> impl Iterator<Item = &Path> {
        self.paths.keys().map(PathBuf::as_path)
    }

    fn allocate_revision(&mut self) -> u64 {
        self.next_revision = self
            .next_revision
            .checked_add(1)
            .expect("document revision counter exhausted");
        self.next_revision
    }
}

fn apply_change(
    text: &mut String,
    change: TextDocumentContentChangeEvent,
) -> Result<(), DocumentError> {
    let Some(range) = change.range else {
        if change.range_length.is_some() {
            return Err(DocumentError::InvalidRangeLength);
        }
        *text = change.text;
        return Ok(());
    };

    let (start, end) = byte_range(text, range)?;
    if let Some(expected) = change.range_length {
        let actual = utf16_len(&text[start..end]);
        if actual != expected {
            return Err(DocumentError::InvalidRangeLength);
        }
    }
    text.replace_range(start..end, &change.text);
    Ok(())
}

fn byte_range(text: &str, range: Range) -> Result<(usize, usize), DocumentError> {
    let start = byte_offset(text, range.start)?;
    let end = byte_offset(text, range.end)?;
    if start > end {
        return Err(DocumentError::InvalidRange);
    }
    Ok((start, end))
}

fn byte_offset(text: &str, position: Position) -> Result<usize, DocumentError> {
    let target_line = usize::try_from(position.line).map_err(|_| DocumentError::InvalidRange)?;
    let (line_start, content_end) =
        line_content_range(text, target_line).ok_or(DocumentError::InvalidRange)?;
    let line = &text[line_start..content_end];
    let target_character =
        usize::try_from(position.character).map_err(|_| DocumentError::InvalidRange)?;
    let mut utf16_offset = 0usize;
    for (byte_offset, character) in line.char_indices() {
        if utf16_offset == target_character {
            return Ok(line_start + byte_offset);
        }
        utf16_offset += character.len_utf16();
        if utf16_offset > target_character {
            return Err(DocumentError::InvalidRange);
        }
    }
    if utf16_offset == target_character {
        Ok(content_end)
    } else {
        Err(DocumentError::InvalidRange)
    }
}

fn line_content_range(text: &str, target_line: usize) -> Option<(usize, usize)> {
    let bytes = text.as_bytes();
    let mut line = 0usize;
    let mut line_start = 0usize;
    let mut index = 0usize;

    while index < bytes.len() {
        let terminator_len = match bytes[index] {
            b'\r' if bytes.get(index + 1) == Some(&b'\n') => 2,
            b'\r' | b'\n' => 1,
            _ => {
                index += 1;
                continue;
            }
        };
        if line == target_line {
            return Some((line_start, index));
        }
        line += 1;
        index += terminator_len;
        line_start = index;
    }

    (line == target_line).then_some((line_start, text.len()))
}

fn utf16_len(text: &str) -> u32 {
    text.encode_utf16()
        .count()
        .try_into()
        .expect("document change range length exceeds u32")
}

pub(crate) fn is_dw_uri(uri: &Uri) -> bool {
    uri.path().as_str().ends_with(".dw")
}

fn document_kind(
    path: &Path,
    language_id: &str,
    explicit_dependency: bool,
) -> Option<DocumentKind> {
    match path.extension().and_then(|extension| extension.to_str()) {
        Some("dw") => Some(DocumentKind::Policy),
        Some("dwschema") => Some(DocumentKind::EventSchema),
        Some("cedarschema" | "json") => Some(DocumentKind::Dependency),
        _ if explicit_dependency => Some(DocumentKind::Dependency),
        _ if language_id == "dogwood-event-schema" => Some(DocumentKind::EventSchema),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;
    use std::str::FromStr;

    use lsp_types::{
        Position, Range, TextDocumentContentChangeEvent, TextDocumentItem, Uri,
        VersionedTextDocumentIdentifier,
    };

    use super::{DocumentError, DocumentKind, DocumentStore};

    fn uri(value: &str) -> Uri {
        Uri::from_str(value).expect("test URI should be valid")
    }

    fn item(uri: Uri, version: i32, language_id: &str, text: &str) -> TextDocumentItem {
        TextDocumentItem::new(uri, language_id.to_owned(), version, text.to_owned())
    }

    fn full_change(text: &str) -> TextDocumentContentChangeEvent {
        TextDocumentContentChangeEvent {
            range: None,
            range_length: None,
            text: text.to_owned(),
        }
    }

    fn ranged_change(
        start: (u32, u32),
        end: (u32, u32),
        text: &str,
    ) -> TextDocumentContentChangeEvent {
        TextDocumentContentChangeEvent {
            range: Some(Range::new(
                Position::new(start.0, start.1),
                Position::new(end.0, end.1),
            )),
            range_length: None,
            text: text.to_owned(),
        }
    }

    fn identifier(uri: Uri, version: i32) -> VersionedTextDocumentIdentifier {
        VersionedTextDocumentIdentifier::new(uri, version)
    }

    fn changed(source: &str, changes: Vec<TextDocumentContentChangeEvent>) -> String {
        let document_uri = uri("file:///policy.dw");
        let mut store = DocumentStore::default();
        store
            .open(item(document_uri.clone(), 1, "dogwood", source), |_| false)
            .unwrap();
        store
            .change(identifier(document_uri.clone(), 2), changes)
            .unwrap();
        store.get(&document_uri).unwrap().text().to_owned()
    }

    #[test]
    fn open_change_and_close_manage_immutable_revisions() {
        let document_uri = uri("file:///policy.dw");
        let mut store = DocumentStore::default();

        store
            .open(item(document_uri.clone(), 1, "dogwood", "old"), |_| false)
            .unwrap();
        let old = store.get(&document_uri).unwrap().text_snapshot();
        let first_revision = store.get(&document_uri).unwrap().revision();

        store
            .change(
                identifier(document_uri.clone(), 3),
                vec![full_change("new")],
            )
            .unwrap();
        let document = store.get(&document_uri).unwrap();
        assert_eq!(document.version(), 3);
        assert!(document.revision() > first_revision);
        assert_eq!(document.text(), "new");
        assert_eq!(&*old, "old");

        store.close(&document_uri).unwrap();
        assert!(store.get(&document_uri).is_none());
    }

    #[test]
    fn incremental_changes_cover_insert_delete_replace_and_ordering() {
        let cases = [
            ("alpha", vec![ranged_change((0, 5), (0, 5), "!")], "alpha!"),
            ("alpha", vec![ranged_change((0, 1), (0, 4), "")], "aa"),
            (
                "alpha",
                vec![ranged_change((0, 1), (0, 4), "OMEG")],
                "aOMEGa",
            ),
            (
                "alpha",
                vec![
                    ranged_change((0, 0), (0, 1), "A"),
                    ranged_change((0, 5), (0, 5), "!"),
                    ranged_change((0, 1), (0, 5), "LPHA"),
                ],
                "ALPHA!",
            ),
        ];

        for (source, changes, expected) in cases {
            assert_eq!(changed(source, changes), expected);
        }
    }

    #[test]
    fn incremental_changes_use_utf16_and_preserve_crlf_boundaries() {
        assert_eq!(
            changed(
                "a😀b\r\nsecond\r\n",
                vec![
                    ranged_change((0, 1), (0, 3), "X"),
                    ranged_change((1, 6), (1, 6), "!"),
                    ranged_change((1, 0), (2, 0), ""),
                ]
            ),
            "aXb\r\n"
        );
    }

    #[test]
    fn incremental_changes_recognize_lone_cr_and_lf_boundaries() {
        assert_eq!(
            changed(
                "a😀b\rsecond\nthird\r\nfourth",
                vec![
                    ranged_change((0, 1), (0, 3), "X"),
                    ranged_change((1, 0), (1, 6), "SECOND"),
                    ranged_change((2, 5), (3, 0), "\r\n"),
                ]
            ),
            "aXb\rSECOND\nthird\r\nfourth"
        );
    }

    #[test]
    fn full_replacement_can_appear_in_an_ordered_change_list() {
        assert_eq!(
            changed(
                "old",
                vec![
                    ranged_change((0, 0), (0, 3), "intermediate"),
                    full_change("new"),
                    ranged_change((0, 3), (0, 3), "!")
                ]
            ),
            "new!"
        );
    }

    #[test]
    fn seeded_utf16_edit_sequences_match_a_byte_reference_after_every_batch() {
        const SEED: u64 = 0xC623_7C88_0000_0008;
        const REPLACEMENTS: [&str; 9] = [
            "",
            "x",
            "\u{1f600}",
            "\u{00e9}",
            " ",
            "\r\n",
            "\r",
            "\n",
            "alpha",
        ];

        let document_uri = uri("file:///seeded.dw");
        let mut store = DocumentStore::default();
        let mut expected = "alpha\r\n\u{1f600} beta\romega\nlast".to_owned();
        store
            .open(item(document_uri.clone(), 1, "dogwood", &expected), |_| {
                false
            })
            .unwrap();
        let mut random = Lcg::new(SEED);

        for version in 2..=97 {
            let mut changes = Vec::new();
            for _ in 0..(1 + random.next() as usize % 6) {
                let candidates = position_candidates(&expected);
                let left = random.next() as usize % candidates.len();
                let right = random.next() as usize % candidates.len();
                let (start_index, end_index) = if left <= right {
                    (left, right)
                } else {
                    (right, left)
                };
                let (start_byte, start_position) = candidates[start_index];
                let (end_byte, end_position) = candidates[end_index];
                let replacement = REPLACEMENTS[random.next() as usize % REPLACEMENTS.len()];
                let range_length = expected[start_byte..end_byte].encode_utf16().count() as u32;
                changes.push(TextDocumentContentChangeEvent {
                    range: Some(Range::new(start_position, end_position)),
                    range_length: Some(range_length),
                    text: replacement.to_owned(),
                });
                expected.replace_range(start_byte..end_byte, replacement);
            }

            store
                .change(identifier(document_uri.clone(), version), changes)
                .unwrap_or_else(|error| {
                    panic!("seed={SEED:#x} version={version}: edit failed: {error}")
                });
            let actual = store.get(&document_uri).unwrap();
            assert_eq!(
                actual.text(),
                expected,
                "seed={SEED:#x} version={version}: incremental/full mismatch"
            );
            assert_eq!(actual.version(), version);
        }
    }

    #[test]
    fn invalid_changes_are_atomic() {
        let document_uri = uri("file:///policy.dw");
        let mut store = DocumentStore::default();
        store
            .open(
                item(document_uri.clone(), 4, "dogwood", "a😀b\r\nnext"),
                |_| false,
            )
            .unwrap();
        let revision = store.get(&document_uri).unwrap().revision();

        let cases = [
            (
                identifier(document_uri.clone(), 4),
                vec![full_change("equal")],
                DocumentError::VersionNotNewer,
            ),
            (
                identifier(document_uri.clone(), 5),
                Vec::new(),
                DocumentError::EmptyChanges,
            ),
            (
                identifier(document_uri.clone(), 5),
                vec![
                    ranged_change((1, 0), (1, 4), "NEXT"),
                    ranged_change((0, 2), (0, 3), "split"),
                ],
                DocumentError::InvalidRange,
            ),
            (
                identifier(document_uri.clone(), 5),
                vec![ranged_change((0, 0), (0, 99), "past")],
                DocumentError::InvalidRange,
            ),
            (
                identifier(document_uri.clone(), 5),
                vec![ranged_change((1, 1), (0, 0), "reverse")],
                DocumentError::InvalidRange,
            ),
            (
                identifier(document_uri.clone(), 5),
                vec![TextDocumentContentChangeEvent {
                    range: Some(Range::new(Position::new(0, 0), Position::new(0, 1))),
                    range_length: Some(2),
                    text: "wrong".to_owned(),
                }],
                DocumentError::InvalidRangeLength,
            ),
        ];

        for (identifier, changes, expected) in cases {
            assert_eq!(store.change(identifier, changes), Err(expected));
            let document = store.get(&document_uri).unwrap();
            assert_eq!(document.version(), 4);
            assert_eq!(document.revision(), revision);
            assert_eq!(document.text(), "a😀b\r\nnext");
        }
    }

    #[test]
    fn duplicate_open_preserves_the_original_document() {
        let document_uri = uri("file:///policy.dw");
        let mut store = DocumentStore::default();
        store
            .open(item(document_uri.clone(), 1, "dogwood", "original"), |_| {
                false
            })
            .unwrap();

        assert_eq!(
            store.open(
                item(document_uri.clone(), 2, "other", "replacement"),
                |_| false
            ),
            Err(DocumentError::DuplicateOpen)
        );
        assert_eq!(store.get(&document_uri).unwrap().text(), "original");
    }

    #[test]
    fn unknown_changes_and_closes_leave_existing_documents_unchanged() {
        let document_uri = uri("file:///policy.dw");
        let unknown_uri = uri("file:///unknown.dw");
        let mut store = DocumentStore::default();
        store
            .open(item(document_uri.clone(), 1, "dogwood", "original"), |_| {
                false
            })
            .unwrap();

        assert_eq!(
            store.change(identifier(unknown_uri.clone(), 2), vec![full_change("new")]),
            Err(DocumentError::DocumentNotOpen)
        );
        assert_eq!(
            store.close(&unknown_uri),
            Err(DocumentError::DocumentNotOpen)
        );
        assert_eq!(store.get(&document_uri).unwrap().text(), "original");
    }

    #[test]
    fn unsupported_uris_are_not_opened() {
        let cases = [
            uri("file:///policy.txt"),
            uri("https://example.com/policy.dw"),
        ];
        let mut store = DocumentStore::default();

        for unsupported_uri in cases {
            assert_eq!(
                store.open(item(unsupported_uri.clone(), 1, "dogwood", "text"), |_| {
                    false
                }),
                Err(DocumentError::UnsupportedDocument)
            );
            assert!(store.get(&unsupported_uri).is_none());
        }

        let supported_uri = uri("file:///policy.dw");
        store
            .open(
                item(supported_uri.clone(), 1, "unrecognized-language-id", "text"),
                |_| false,
            )
            .unwrap();
        assert_eq!(
            store.get(&supported_uri).unwrap().kind(),
            DocumentKind::Policy
        );
    }

    #[test]
    fn arbitrary_paths_open_only_when_explicitly_configured_as_dependencies() {
        let configured_uri = uri("file:///schema.txt");
        let unrelated_uri = uri("file:///notes.txt");
        let configured_path = Path::new("/schema.txt");
        let mut store = DocumentStore::default();

        store
            .open(
                item(configured_uri.clone(), 1, "plaintext", "schema"),
                |path| path == configured_path,
            )
            .unwrap();
        assert_eq!(
            store.get(&configured_uri).unwrap().kind(),
            DocumentKind::Dependency
        );

        assert_eq!(
            store.open(
                item(unrelated_uri.clone(), 1, "plaintext", "notes"),
                |path| path == configured_path
            ),
            Err(DocumentError::UnsupportedDocument)
        );
        assert!(store.get(&unrelated_uri).is_none());
    }

    #[test]
    fn supported_document_kinds_remain_immutable() {
        let cases = [
            (
                "file:///policy.dw",
                "dogwood-event-schema",
                false,
                Some(DocumentKind::Policy),
            ),
            (
                "file:///events.dwschema",
                "plaintext",
                false,
                Some(DocumentKind::EventSchema),
            ),
            (
                "file:///schema",
                "dogwood-event-schema",
                false,
                Some(DocumentKind::EventSchema),
            ),
            (
                "file:///schema.txt",
                "dogwood-event-schema",
                false,
                Some(DocumentKind::EventSchema),
            ),
            (
                "file:///actions.cedarschema",
                "dogwood-event-schema",
                false,
                Some(DocumentKind::Dependency),
            ),
            (
                "file:///providers.json",
                "dogwood-event-schema",
                false,
                Some(DocumentKind::Dependency),
            ),
            ("file:///schema", "dogwood", false, None),
            ("file:///schema.txt", "unknown", false, None),
            (
                "file:///configured.input",
                "dogwood-event-schema",
                true,
                Some(DocumentKind::Dependency),
            ),
        ];

        for (source, language_id, explicit, expected) in cases {
            let document_uri = uri(source);
            let mut store = DocumentStore::default();
            let result = store.open(item(document_uri.clone(), 1, language_id, "text"), |_| {
                explicit
            });
            match expected {
                Some(kind) => {
                    result.unwrap();
                    assert_eq!(store.get(&document_uri).unwrap().kind(), kind, "{source}");
                }
                None => assert_eq!(result, Err(DocumentError::UnsupportedDocument), "{source}"),
            }
        }
    }

    fn position_candidates(source: &str) -> Vec<(usize, Position)> {
        let mut candidates = Vec::new();
        let mut line = 0_u32;
        let mut character = 0_u32;
        let mut offset = 0;
        candidates.push((offset, Position::new(line, character)));
        while offset < source.len() {
            let tail = &source[offset..];
            if tail.starts_with("\r\n") {
                offset += 2;
                line += 1;
                character = 0;
                candidates.push((offset, Position::new(line, character)));
                continue;
            }
            let scalar = tail.chars().next().unwrap();
            offset += scalar.len_utf8();
            if matches!(scalar, '\r' | '\n') {
                line += 1;
                character = 0;
            } else {
                character += scalar.len_utf16() as u32;
            }
            candidates.push((offset, Position::new(line, character)));
        }
        candidates
    }

    struct Lcg(u64);

    impl Lcg {
        const fn new(seed: u64) -> Self {
            Self(seed)
        }

        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            self.0
        }
    }
}
