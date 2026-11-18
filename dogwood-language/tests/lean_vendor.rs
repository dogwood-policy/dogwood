//! The pinned export of the Lean project's dependencies, `dogwood-lean/vendor/`, which
//! the build script builds the Lean frontend with when the Lean project has no
//! `.lake/packages` (a build without network access): every file has the digest
//! `vendor/MANIFEST` records, the manifest's own digest checks out, its revisions are
//! the ones `lake-manifest.json` pins, and the vendored modules are exactly the
//! modules of cedar-lean and Batteries that the specification (`Dogwood`, its proofs
//! and examples too) and the frontend's library (`Dogwood.Frontend.Library`) import,
//! transitively.
//! So a new import of either fails here, in every build, and not only in a build
//! without network. `dogwood-lean/scripts/vendor_deps.py write`
//! regenerates the export (and `check` compares it with upstream).
//!
//! The test needs the repository's `dogwood-lean` directory; a crate fetched from a
//! registry has none, and the test then checks nothing.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

fn hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// `text` without its comments (`--` to the end of the line, and nested `/- … -/`).
fn strip_comments(text: &str) -> String {
    let b = text.as_bytes();
    let (mut out, mut i, mut depth) = (Vec::new(), 0, 0usize);
    while i < b.len() {
        if b[i..].starts_with(b"/-") {
            depth += 1;
            i += 2;
        } else if depth > 0 && b[i..].starts_with(b"-/") {
            depth -= 1;
            i += 2;
        } else if depth > 0 {
            if b[i] == b'\n' {
                out.push(b'\n');
            }
            i += 1;
        } else if b[i..].starts_with(b"--") {
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
        } else {
            out.push(b[i]);
            i += 1;
        }
    }
    String::from_utf8(out).expect("UTF-8")
}

/// The modules a Lean file's header imports.
fn imports(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    for line in strip_comments(text).lines() {
        let mut words = line.split_whitespace().peekable();
        let Some(&first) = words.peek() else {
            continue;
        };
        if first == "module" || first == "prelude" {
            continue;
        }
        while words
            .peek()
            .is_some_and(|w| ["public", "private", "meta"].contains(w))
        {
            words.next();
        }
        if words.next() != Some("import") {
            break; // the header ends at the first command
        }
        out.extend(words.filter(|w| *w != "all").map(str::to_owned));
    }
    out
}

#[test]
fn the_vendored_lean_dependencies_are_the_libraries_imports() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../dogwood-lean");
    let vendor = root.join("vendor");
    if !vendor.join("MANIFEST").is_file() {
        eprintln!("no dogwood-lean/vendor here (a crate from a registry): nothing to check");
        return;
    }
    let text = std::fs::read_to_string(vendor.join("MANIFEST")).unwrap();
    let (body, last) = text.trim_end_matches('\n').rsplit_once('\n').unwrap();
    assert_eq!(
        last.strip_prefix("tree-sha256 "),
        Some(hex(format!("{body}\n").as_bytes()).as_str()),
        "vendor/MANIFEST's digest does not match its contents"
    );

    // Every file has the manifest's digest, and nothing else is vendored.
    let mut listed = BTreeSet::new();
    let mut origins: BTreeMap<String, (String, String)> = BTreeMap::new();
    for line in body.lines() {
        let fields: Vec<&str> = line.split(' ').collect();
        match fields.as_slice() {
            ["sha256", digest, rel] => {
                let bytes =
                    std::fs::read(vendor.join(rel)).unwrap_or_else(|e| panic!("vendor/{rel}: {e}"));
                assert_eq!(&hex(&bytes), digest, "vendor/{rel} is not the manifest's");
                listed.insert(rel.to_string());
            }
            ["origin", dir, name, rev, ..] => {
                origins.insert(name.to_string(), (dir.to_string(), rev.to_string()));
            }
            _ => {}
        }
    }
    let mut on_disk = BTreeSet::new();
    let mut stack = vec![vendor.clone()];
    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                stack.push(path);
            } else if path.file_name().is_some_and(|n| n != "MANIFEST") {
                let rel = path.strip_prefix(&vendor).unwrap();
                on_disk.insert(slash_path(rel));
            }
        }
    }
    assert_eq!(
        on_disk, listed,
        "the files under vendor/ are not the manifest's"
    );

    // The manifest's revisions are the ones the Lean project pins.
    let lake: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(root.join("lake-manifest.json")).unwrap())
            .unwrap();
    let pinned: BTreeMap<String, String> = lake["packages"]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| {
            (
                p["name"].as_str().unwrap().to_owned(),
                p["rev"].as_str().unwrap().to_owned(),
            )
        })
        .collect();
    let vendored: BTreeMap<String, String> = origins
        .iter()
        .map(|(name, (_, rev))| (name.clone(), rev.clone()))
        .collect();
    assert_eq!(
        vendored, pinned,
        "vendor/ is not at lake-manifest.json's revisions; run dogwood-lean/scripts/vendor_deps.py write"
    );

    // The vendored modules are exactly the library's imports, transitively.
    let dir_of = |name: &str| origins[name].0.clone();
    let file_of = |module: &str| -> Option<PathBuf> {
        let rel = format!("{}.lean", module.replace('.', "/"));
        match module.split('.').next().unwrap() {
            "Dogwood" => Some(root.join(rel)),
            "Cedar" => Some(vendor.join(dir_of("Cedar")).join(rel)),
            "Batteries" => Some(vendor.join(dir_of("batteries")).join(rel)),
            "Init" | "Std" | "Lean" | "Lake" => None,
            other => panic!("{module}: a module of no known package ({other})"),
        }
    };
    let mut seen = BTreeSet::new();
    let mut needed = BTreeSet::new();
    let mut todo = vec!["Dogwood".to_owned(), "Dogwood.Frontend.Library".to_owned()];
    while let Some(module) = todo.pop() {
        if !seen.insert(module.clone()) {
            continue;
        }
        let Some(file) = file_of(&module) else {
            continue;
        };
        let text = std::fs::read_to_string(&file).unwrap_or_else(|e| {
            panic!(
                "{module} ({}): {e}; run dogwood-lean/scripts/vendor_deps.py write",
                file.display()
            )
        });
        if let Ok(rel) = file.strip_prefix(&vendor) {
            needed.insert(slash_path(rel));
        }
        todo.extend(imports(&text));
    }
    let modules: BTreeSet<String> = listed
        .iter()
        .filter(|f| f.ends_with(".lean") && !f.ends_with("/lakefile.lean"))
        .cloned()
        .collect();
    assert_eq!(
        needed, modules,
        "the vendored modules are not the libraries' imports; run \
         dogwood-lean/scripts/vendor_deps.py write"
    );
    assert!(modules.len() > 50, "{} vendored modules", modules.len());
}

/// `rel` with its components separated by `/`, as the manifest writes paths on
/// every platform.
fn slash_path(rel: &std::path::Path) -> String {
    let parts: Vec<_> = rel
        .components()
        .map(|c| c.as_os_str().to_string_lossy())
        .collect();
    parts.join("/")
}
