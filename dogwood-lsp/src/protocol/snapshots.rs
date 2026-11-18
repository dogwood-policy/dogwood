use std::path::PathBuf;
use std::sync::Arc;

use dogwood_lsp::diagnostics::{BundleDocuments, SourceDocument};
use dogwood_lsp::frontend::BundleInput;
use lsp_types::Uri;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SourceOrigin {
    Open { version: i32, revision: u64 },
    Disk { revision: u64 },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SourceIdentity {
    pub(crate) path: PathBuf,
    pub(crate) origin: SourceOrigin,
}

#[derive(Clone, Debug)]
pub(crate) struct SourceSnapshot {
    pub(crate) uri: Uri,
    pub(crate) identity: SourceIdentity,
    pub(crate) text: Arc<str>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct BundleIdentity {
    pub(crate) policy: SourceIdentity,
    pub(crate) action_schema: SourceIdentity,
    pub(crate) event_schema: Option<SourceIdentity>,
    pub(crate) providers: Option<SourceIdentity>,
    pub(crate) macros: Option<SourceIdentity>,
}

#[derive(Clone, Debug)]
pub(crate) struct BundleSnapshot {
    pub(crate) policy: SourceSnapshot,
    pub(crate) action_schema: SourceSnapshot,
    pub(crate) event_schema: Option<SourceSnapshot>,
    pub(crate) providers: Option<SourceSnapshot>,
    pub(crate) macros: Option<SourceSnapshot>,
}

impl BundleSnapshot {
    pub(crate) fn identity(&self) -> BundleIdentity {
        BundleIdentity {
            policy: self.policy.identity.clone(),
            action_schema: self.action_schema.identity.clone(),
            event_schema: self
                .event_schema
                .as_ref()
                .map(|source| source.identity.clone()),
            providers: self
                .providers
                .as_ref()
                .map(|source| source.identity.clone()),
            macros: self.macros.as_ref().map(|source| source.identity.clone()),
        }
    }

    pub(crate) fn frontend_input(&self) -> BundleInput<'_> {
        BundleInput {
            policy: &self.policy.text,
            action_schema: &self.action_schema.text,
            event_schema: self
                .event_schema
                .as_ref()
                .map(|source| source.text.as_ref()),
            providers: self.providers.as_ref().map(|source| source.text.as_ref()),
            macros: self.macros.as_ref().map(|source| source.text.as_ref()),
        }
    }

    pub(crate) fn documents(&self) -> BundleDocuments<'_> {
        BundleDocuments {
            policy: source_document(&self.policy),
            action_schema: source_document(&self.action_schema),
            event_schema: self.event_schema.as_ref().map(source_document),
            providers: self.providers.as_ref().map(source_document),
            macros: self.macros.as_ref().map(source_document),
        }
    }
}

fn source_document(source: &SourceSnapshot) -> SourceDocument<'_> {
    SourceDocument {
        uri: &source.uri,
        text: &source.text,
    }
}
