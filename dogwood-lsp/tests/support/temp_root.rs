//! The canonical path of a test's temporary workspace.

use std::fs;
use std::path::{Path, PathBuf};

/// The canonical path of the existing directory `root`. The temporary
/// directory can be reached through a symlink (`/var` on macOS), and the
/// server rejects an explicitly configured path that goes through one.
pub(crate) fn canonical(root: &Path) -> PathBuf {
    fs::canonicalize(root).expect("temporary workspace should canonicalize")
}
