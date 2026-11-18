//! The build script of `dogwood-language`.
//!
//! The crate declares `links = "dogwood_lean"`, so this script always runs, and
//! what it prints as `cargo:KEY=VALUE` reaches the build script of every crate
//! that depends on this one directly, as `DEP_DOGWOOD_LEAN_<KEY>`.
//!
//! Without the `lean-frontend` feature it prints `cargo:lean=0` and does nothing
//! else: the default build needs no Lean toolchain and links nothing but Rust.
//!
//! With `lean-frontend` it links the Lean frontend, one static archive
//! `libdogwood_lean_frontend.a` holding the C shim (`src/lean_frontend/shim.c`),
//! the Lean frontend's library (`Dogwood.Frontend.Library` of `dogwood-lean/`
//! and every module it imports, from cedar-lean and Batteries too, except
//! Batteries' tactics, linters and other extensions of the elaborator, which the
//! library leaves out: see `frontendFfi` in `dogwood-lean/lakefile.lean`), Lean's
//! own `Init` and `Std` libraries whole, the parts of Lean's `Lean` library and of
//! the Lean kernel (`libleancpp.a`) they reach, the Lean runtime (`libleanrt.a`),
//! and the runtime's static dependencies. The archive is the process's one Lean
//! runtime: a dependent crate that links Lean modules of its own links them
//! against it (see "Link metadata" below). The archive comes from one of two
//! places: prebuilt, or built from the Lean sources.
//!
//! **The manifest.** An archive sits next to its manifest,
//! `libdogwood_lean_frontend.link`, which records the SHA-256 digest of the
//! sources it was built from (`source-sha256`: the Lean project's inputs and the
//! shim, see `source_hash`), the SHA-256 digest of the archive file
//! (`archive-sha256`), the SHA-256 digest of the crate's side of the bridge
//! (`bridge-sha256`: this script and `src/lean_frontend/`), the Lean version, the
//! shared libraries the archive needs, the built Lean packages (relative to the
//! manifest), the SHA-256 digest of their files (`packages-sha256`), and the Rust
//! release of the Unicode tables the Lean frontend escapes strings with
//! (`tables-rust-version`). A build
//! from source leaves the archive, its manifest, the built Lean packages
//! (`dogwood-lean/`) and the list of their files (`libdogwood_lean_frontend.files`,
//! relative to the manifest) in its `$OUT_DIR`, which is itself a prebuilt
//! directory: a packaging step publishes the archive, the manifest and the listed
//! files.
//!
//! **Prebuilt.** A prebuilt archive is used when its manifest checks out: its Lean
//! version is this crate's, the archive file's digest is the manifest's, and,
//! when the Lean sources are present (a checkout of the repository), the
//! manifest's source digest is theirs; when they are absent (a crate fetched from
//! a registry has none), the manifest's bridge digest is this crate's instead. The
//! archive is
//! * the one `$DOGWOOD_LEAN_PREBUILT` names (a file `libdogwood_lean_frontend.a`),
//!   which must check out, or the build fails; else
//! * one found on `$PATH`: a `<dir>/../lib/libdogwood_lean_frontend.a`, next to its
//!   manifest, for a `<dir>` on `$PATH`, whose real path (links resolved) lies in
//!   this package's own published artifact (a path segment `Dogwood_Language` or
//!   `Dogwood_Language-<version>`) or in the `lib/` of a library farm
//!   (`…/<farm>/<target>.libfarm/lib/`, into which a build system copies the
//!   published `lib/` of each package of the dependency closure; `published_location`
//!   names the `<farm>` directory). An archive anywhere else is never considered, and
//!   one that does not check out is skipped, with a warning.
//!
//! This route runs neither Lean nor Lake, needs no Lean sources and no network,
//! and is taken before a build from source unless `$DOGWOOD_LEAN_FROM_SOURCE` is
//! set.
//!
//! **From source** (when no prebuilt archive is used, or `$DOGWOOD_LEAN_FROM_SOURCE`
//! is set; it needs the Lean sources):
//! 1. The Lean sources are `$DOGWOOD_LEAN_SOURCE`, else `../dogwood-lean` next to
//!    this crate (a checkout of the repository).
//! 2. Locate a Lean 4.34.0 toolchain: `$LEAN_SYSROOT`, else `lean --print-prefix`
//!    run in the Lean project (so that elan honours its `lean-toolchain`). Its
//!    headers are in `include/`, or `stage1/include/` (a toolchain installed from
//!    its build tree).
//! 3. Copy the Lean project into `$OUT_DIR/dogwood-lean` (a build script must not
//!    write to its source directory) with its dependencies: the sources of the
//!    packages in the project's `.lake/packages` when they are there, else the
//!    pinned export of exactly the modules the specification imports, `vendor/`, whose
//!    files are first checked against `vendor/MANIFEST` and which the copy's
//!    `lake-manifest.json` then names as path dependencies, so that Lake clones
//!    nothing (`dogwood-lean/scripts/vendor_deps.py` writes the export). A
//!    dependency configured in `lakefile.toml` (Batteries) is given the equivalent
//!    `lakefile.lean`, which the build uses, so that every package root has a
//!    `lakefile.lean`. Run `lake build frontendFfi` there (`$LAKE` overrides the
//!    `lake` command).
//! 4. Compile the shim with the `cc` crate against the toolchain's `lean.h`.
//! 5. Merge everything into one archive: `libInit.a` and `libleanrt.a` reference
//!    each other, and rustc cannot express a linker group, but a linker resolves
//!    references inside one archive by rescanning it. On Linux the shim, the
//!    frontend's library, `libInit.a`, `libStd.a` and `libleanrt.a`, whole, and
//!    the members of `libLean.a`, `libleancpp.a` and the extra archives they reach
//!    are first linked into one relocatable object (`cc -r`) without debug
//!    sections, which halves the archive (and the rlib that bundles it): most of
//!    `libLean.a` is Lean's elaborator, which the frontend does not run. (Debug
//!    sections are left out because a newer assembler writes them compressed in a
//!    form an older linker cannot read.)
//!
//! Lean's generated C is compiled by `$LEAN_CC` if set, else by the compiler the
//! `cc` crate selects (`$CC`, else the platform default), and archived by
//! `$LEAN_AR`, else the `cc` crate's archiver. The toolchain's bundled clang and
//! `llvm-ar` are never used: they need a newer glibc than some Linux
//! distributions have.
//!
//! The runtime's own dependencies depend on how the toolchain was built:
//! * an upstream (elan) toolchain ships static `libc++.a`, `libc++abi.a`,
//!   `libgmp.a` and `libuv.a` (and has mimalloc compiled into `libleanrt.a`);
//!   they go into the archive;
//! * a toolchain built against a C++ library, GMP, libuv and mimalloc of the
//!   system takes their static archives from `$DOGWOOD_LEAN_EXTRA_ARCHIVES`
//!   (colon-separated paths, e.g. `libstdc++.a`, `libgmp.a`, `libuv_a.a` and
//!   `libmimalloc.a`), whose members the runtime reaches go into the archive;
//! * without them, the archive is linked against the shared `libstdc++`, `libgmp`
//!   and `libuv`, and `libmimalloc` when one is there, searched in
//!   `$DOGWOOD_LEAN_LINK_SEARCH` (colon-separated) and the toolchain's `lib/`
//!   directories.
//!
//! In the first two cases the archive needs nothing at run time beyond libc,
//! `libpthread`, `libdl`, `librt` and `libm`.
//!
//! **The Unicode tables.** The Lean frontend prints strings, ids and patterns as Rust's
//! `escape_debug` does, with the Unicode tables of one Rust release
//! (`dogwood-lean/Dogwood/Frontend/UnicodeTables.lean`, from
//! `dogwood-lean/scripts/gen_unicode_tables.py`). The script compares that release (the Lean
//! sources', else the manifest's) with the compiler's (`$RUSTC --version`) and prints a
//! `cargo:warning` when they differ, saying how to regenerate the tables; it gives both to
//! the crate (`DOGWOOD_LEAN_TABLES_RUST`, `DOGWOOD_LEAN_RUSTC`), whose test of the tables
//! names them when it fails.
//!
//! **Link metadata.** With the feature, the script prints, for a dependent's
//! build script (`DEP_DOGWOOD_LEAN_<KEY>`):
//! * `lean=1` (`lean=0` without the feature, and nothing else);
//! * `LEAN_VERSION`: the Lean version the library's `.olean` files were built
//!   with, `4.34.0`;
//! * `SOURCE_SHA256`: the digest of the Lean sources and the shim the archive was
//!   built from (the manifest's source digest). C code compiled against one set
//!   of `.olean` files calls that set's symbols, so a dependent's archive must
//!   name the digest it was compiled against;
//! * `TOOLCHAIN`: the toolchain's prefix (`bin/lean`, `bin/lake`, `lib/lean/`, and
//!   the headers in `include/` or `stage1/include/`); from a prebuilt archive,
//!   `$LEAN_SYSROOT` if set, else empty;
//! * `PACKAGES`: `DogwoodSpec=<dir>;Cedar=<dir>;batteries=<dir>`, the built Lake
//!   packages: each `<dir>` is a package root with its `lakefile.lean`, its
//!   sources, its `.lake/build/lib/lean/` (the `.olean`, `.ilean` and trace files)
//!   and its `.lake/build/ir/` (Lake's traces of the C, which it checks to find
//!   the library up to date), which a dependent requires by path; Lake finds them
//!   up to date and builds nothing of them. They are in `$OUT_DIR`, which Lake may
//!   write to when it loads them (a lock file). From a prebuilt archive, the
//!   packages its manifest names, when they are there and their files have the
//!   manifest's digest, copied into `$OUT_DIR` (so that the prebuilt directory may
//!   be read-only); else empty, with a warning when they are there but differ;
//! * `CC`, `AR` (from source only): the C compiler and archiver the build used
//!   for Lean's C (for a toolchain whose headers are in `stage1/include/`, the
//!   compiler is a script in `$OUT_DIR` that adds them to its search path).
//!
//! The archive is linked by this crate (`rustc-link-lib=static=…`), so a
//! dependent's archive, which rustc passes before this crate's, holds only the
//! dependent's own modules and C code, and its references resolve in this one.
//! A final link must collect unreferenced sections (`--gc-sections`, which rustc
//! passes for an executable unless `-C link-dead-code`): the library keeps one
//! reference into a left-out module of Batteries (`Except.pmap` of
//! `Batteries.Lean.Except`, from the `ExceptT` instance of
//! `Batteries.Classes.SatisfiesM`), in code nothing reaches.

fn main() {
    #[cfg(feature = "lean-frontend")]
    lean::link();
    #[cfg(not(feature = "lean-frontend"))]
    {
        println!("cargo:rerun-if-changed=build.rs");
        println!("cargo:lean=0");
    }
}

#[cfg(feature = "lean-frontend")]
mod lean {
    use std::collections::BTreeSet;
    use std::env;
    use std::ffi::OsString;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::Command;

    use sha2::{Digest, Sha256};

    /// The Lean project's files the frontend is built from, relative to its root.
    const LEAN_INPUTS: &[&str] = &[
        "lakefile.lean",
        "lean-toolchain",
        "lake-manifest.json",
        "Dogwood",
        "vendor",
    ];

    /// The pinned export of the Lean project's dependencies, relative to its root, and
    /// its manifest there.
    const VENDOR: &str = "vendor";
    const VENDOR_MANIFEST: &str = "vendor/MANIFEST";

    /// The Lean version the project pins (`dogwood-lean/lean-toolchain`).
    const LEAN_VERSION: &str = "4.34.0";

    /// The Lake package of the Lean project (`package DogwoodSpec` in its lakefile).
    const ROOT_PACKAGE: &str = "DogwoodSpec";

    /// Where the build from source copies the Lean project, relative to `$OUT_DIR`.
    const PROJECT: &str = "dogwood-lean";

    /// The static library `lake build frontendFfi` produces.
    const LEAN_LIB: &str = "libDogwoodFrontendFfi.a";

    /// The C shim, relative to the crate.
    const SHIM: &str = "src/lean_frontend/shim.c";

    /// The crate's side of the bridge, relative to the crate: what the archive's
    /// entry points are called through, and how the archive is built and linked.
    const BRIDGE: &[&str] = &["build.rs", "src/lean_frontend"];

    /// The archive this script links, its manifest, and the list of the built
    /// packages' files.
    const ARCHIVE: &str = "libdogwood_lean_frontend.a";
    const MANIFEST: &str = "libdogwood_lean_frontend.link";
    const FILES: &str = "libdogwood_lean_frontend.files";

    /// The package whose published artifact is searched for an archive, besides a
    /// library farm.
    const PACKAGE: &str = "Dogwood_Language";

    /// The Lean libraries of the toolchain the archive holds whole: the runtime and
    /// Lean's standard library, which a dependent's own Lean code may use beyond what
    /// the frontend reaches.
    const WHOLE_LEAN_LIBS: &[&str] = &["libInit.a", "libStd.a", "libleanrt.a"];

    /// The Lean libraries of the toolchain the archive holds the reached parts of.
    const REACHED_LEAN_LIBS: &[&str] = &["libleancpp.a", "libLean.a"];

    /// Shared libraries every build of the archive needs on Linux.
    const BASE_DYLIBS: &[&str] = &["pthread", "dl", "rt", "m"];

    pub fn link() {
        let manifest_dir =
            PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
        let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR"));
        let source = lean_source(&manifest_dir);
        let present = LEAN_INPUTS.iter().all(|i| source.join(i).exists());

        println!("cargo:rerun-if-changed=build.rs");
        for b in BRIDGE {
            println!("cargo:rerun-if-changed={b}");
        }
        if present {
            // Only when present: a path that does not exist reruns the script every time.
            for input in LEAN_INPUTS {
                println!("cargo:rerun-if-changed={}", source.join(input).display());
            }
        }
        for var in [
            "DOGWOOD_LEAN_PREBUILT",
            "DOGWOOD_LEAN_FROM_SOURCE",
            "DOGWOOD_LEAN_SOURCE",
            "DOGWOOD_LEAN_LINK_SEARCH",
            "DOGWOOD_LEAN_EXTRA_ARCHIVES",
            "LEAN_SYSROOT",
            "LEAN_CC",
            "LEAN_AR",
            "LAKE",
            "PATH",
        ] {
            println!("cargo:rerun-if-env-changed={var}");
        }

        // The source digest only when the sources are here; the bridge's always.
        let hash = present.then(|| source_hash(&manifest_dir, &source));
        let bridge = bridge_hash(&manifest_dir);
        let from_source = env::var_os("DOGWOOD_LEAN_FROM_SOURCE").is_some();
        let prebuilt = if from_source {
            None
        } else {
            find_prebuilt(hash.as_deref(), &bridge)
        };
        let (dir, built) = match prebuilt {
            Some(dir) => {
                // rustc bundles the archive into this crate's rlib, so a new archive must
                // rebuild the crate.
                println!("cargo:rerun-if-changed={}", dir.join(ARCHIVE).display());
                println!("cargo:rerun-if-changed={}", dir.join(MANIFEST).display());
                (dir, None)
            }
            None => {
                let Some(hash) = &hash else {
                    panic!(
                        "the `lean-frontend` feature needs the Lean frontend's archive, and there \
                         is none to use: no prebuilt archive (DOGWOOD_LEAN_PREBUILT is unset{}, \
                         and none was found on PATH next to its manifest; see the warnings, if \
                         any), and no Lean sources to build one from (no `dogwood-lean` \
                         directory at {}; a crate fetched from a registry has none). Set \
                         DOGWOOD_LEAN_PREBUILT to a prebuilt `{ARCHIVE}`, or DOGWOOD_LEAN_SOURCE \
                         to the repository's `dogwood-lean` directory.",
                        if from_source {
                            ", or DOGWOOD_LEAN_FROM_SOURCE is set"
                        } else {
                            ""
                        },
                        source.display()
                    )
                };
                let built = build_from_source(&manifest_dir, &source, &out_dir);
                let digest = sha256_file(&out_dir.join(ARCHIVE));
                let files = package_files(&out_dir, &built.packages);
                fs::write(
                    out_dir.join(FILES),
                    files
                        .iter()
                        .map(|f| format!("{}\n", f.display()))
                        .collect::<String>(),
                )
                .expect("write the list of the packages' files");
                let packages_digest = files_hash(&out_dir, &files, None);
                fs::write(
                    out_dir.join(MANIFEST),
                    manifest_text(&Manifest {
                        source: hash.clone(),
                        archive: digest,
                        bridge: bridge.clone(),
                        lean_version: LEAN_VERSION.to_owned(),
                        dylibs: built.dylibs.clone(),
                        packages: built.packages.clone(),
                        packages_digest,
                        tables_rust: tables_rust_version(&source).unwrap_or_default(),
                    }),
                )
                .expect("write the archive's manifest");
                (out_dir.clone(), Some(built))
            }
        };
        let manifest = read_manifest(&dir.join(MANIFEST));
        let hash = manifest.source.clone();
        check_tables(present.then_some(source.as_path()), &manifest);

        // Linked under a name that holds the source digest, so that no other archive of
        // the same name on the linker's search path is taken for this one.
        let linked = format!("dogwood_lean_frontend_{}", &hash[..16]);
        let link = out_dir.join(format!("lib{linked}.a"));
        let _ = fs::remove_file(&link);
        std::os::unix::fs::symlink(dir.join(ARCHIVE), &link).expect("link the archive");
        println!("cargo:rustc-link-search=native={}", out_dir.display());
        println!("cargo:rustc-link-lib=static={linked}");
        if let Some(b) = &built {
            for dir in &b.link_search {
                println!("cargo:rustc-link-search=native={}", dir.display());
            }
        } else if manifest
            .dylibs
            .iter()
            .any(|l| !BASE_DYLIBS.contains(&l.as_str()))
        {
            // A prebuilt archive linked against shared libraries other than the system's.
            for dir in split_paths("DOGWOOD_LEAN_LINK_SEARCH") {
                println!("cargo:rustc-link-search=native={}", dir.display());
            }
        }
        for lib in &manifest.dylibs {
            println!("cargo:rustc-link-lib=dylib={lib}");
        }

        // The link metadata (see the script's documentation).
        let (toolchain, cc) = match &built {
            Some(b) => (b.prefix.clone(), Some(b.cc.clone())),
            None => (
                env::var_os("LEAN_SYSROOT")
                    .map(PathBuf::from)
                    .unwrap_or_default(),
                None,
            ),
        };
        let packages: Vec<(String, PathBuf)> = if built.is_some() {
            manifest
                .packages
                .iter()
                .map(|(name, rel)| (name.clone(), out_dir.join(rel)))
                .collect()
        } else {
            prebuilt_packages(&dir, &out_dir, &manifest)
        };
        println!("cargo:lean=1");
        println!("cargo:LEAN_VERSION={LEAN_VERSION}");
        println!("cargo:SOURCE_SHA256={hash}");
        println!("cargo:TOOLCHAIN={}", toolchain.display());
        println!(
            "cargo:PACKAGES={}",
            packages
                .iter()
                .map(|(name, d)| format!("{name}={}", d.display()))
                .collect::<Vec<_>>()
                .join(";")
        );
        if let (Some(cc), Some(b)) = (cc, &built) {
            println!("cargo:CC={}", Path::new(&cc).display());
            println!("cargo:AR={}", Path::new(&b.ar).display());
        }
    }

    /// The Lean project: `$DOGWOOD_LEAN_SOURCE`, else `../dogwood-lean`.
    fn lean_source(manifest_dir: &Path) -> PathBuf {
        env::var_os("DOGWOOD_LEAN_SOURCE")
            .map(PathBuf::from)
            .unwrap_or_else(|| manifest_dir.join("../dogwood-lean"))
    }

    /// The non-empty paths of the colon-separated variable `var`.
    fn split_paths(var: &str) -> Vec<PathBuf> {
        env::split_paths(&env::var_os(var).unwrap_or_default())
            .filter(|d| !d.as_os_str().is_empty())
            .collect()
    }

    // ── The Unicode tables and the compiler ────────────────────────────

    /// The Lean frontend's Unicode tables, relative to the Lean project.
    const TABLES: &str = "Dogwood/Frontend/UnicodeTables.lean";

    /// The Rust release the Lean frontend's Unicode tables come from (`rustVersion` of
    /// [`TABLES`]), when the Lean sources are at `source`.
    fn tables_rust_version(source: &Path) -> Option<String> {
        let text = fs::read_to_string(source.join(TABLES)).ok()?;
        let key = "def rustVersion : String := \"";
        let at = text.find(key)? + key.len();
        Some(text[at..].split('"').next()?.to_owned())
    }

    /// The release of the Rust compiler compiling this crate (`$RUSTC --version`).
    fn rustc_version() -> Option<String> {
        let out = Command::new(env::var_os("RUSTC")?)
            .arg("--version")
            .output()
            .ok()?;
        String::from_utf8_lossy(&out.stdout)
            .split_whitespace()
            .nth(1)
            .map(str::to_owned)
    }

    /// Compare the Rust release of the Lean frontend's Unicode tables (the Lean sources', else
    /// the manifest's) with the compiler's, and warn when they differ: the Lean frontend prints
    /// strings, ids and patterns as Rust's `escape_debug` does with those tables, and where the
    /// compiler's `escape_debug` differs, the two frontends print a string differently, and give
    /// its rule other revisions. Both versions reach the crate (`DOGWOOD_LEAN_TABLES_RUST`,
    /// `DOGWOOD_LEAN_RUSTC`), whose test of the tables names them when it fails.
    fn check_tables(source: Option<&Path>, manifest: &Manifest) {
        let tables = source
            .and_then(tables_rust_version)
            .or_else(|| Some(manifest.tables_rust.clone()).filter(|v| !v.is_empty()));
        let rustc = rustc_version();
        println!(
            "cargo:rustc-env=DOGWOOD_LEAN_TABLES_RUST={}",
            tables.as_deref().unwrap_or("unknown")
        );
        println!(
            "cargo:rustc-env=DOGWOOD_LEAN_RUSTC={}",
            rustc.as_deref().unwrap_or("unknown")
        );
        match (tables, rustc) {
            (Some(t), Some(r)) if t == r => {}
            (t, r) => println!(
                "cargo:warning=the Lean frontend escapes strings with the Unicode tables of Rust \
                 {}, and this crate is compiled with Rust {}: where the two releases' \
                 `escape_debug` differ, the Lean and Rust frontends print a string differently, \
                 and give its rule other revisions. Regenerate the tables for this compiler: set \
                 RUST_VERSION in dogwood-lean/scripts/gen_unicode_tables.py to its release, and \
                 run `scripts/gen_unicode_tables.py --verify` in dogwood-lean/ with its rustc on \
                 PATH.",
                t.as_deref().unwrap_or("(not recorded)"),
                r.as_deref().unwrap_or("(unknown)"),
            ),
        }
    }

    // ── Prebuilt ────────────────────────────────────────────────────────

    /// The directory of the prebuilt archive to link, if any: `$DOGWOOD_LEAN_PREBUILT`'s,
    /// which must check out, else the first one found on `$PATH` that does.
    fn find_prebuilt(hash: Option<&str>, bridge: &str) -> Option<PathBuf> {
        if let Some(path) = env::var_os("DOGWOOD_LEAN_PREBUILT") {
            let archive = PathBuf::from(path);
            let dir = archive
                .parent()
                .map(Path::to_owned)
                .unwrap_or_else(|| PathBuf::from("."));
            if archive.file_name().and_then(|n| n.to_str()) != Some(ARCHIVE) {
                panic!(
                    "DOGWOOD_LEAN_PREBUILT must name a file `{ARCHIVE}` (next to its \
                     `{MANIFEST}`); it names {}",
                    archive.display()
                );
            }
            if let Err(why) = verify(&dir, hash, bridge) {
                panic!(
                    "DOGWOOD_LEAN_PREBUILT names an archive this crate cannot use: {why}. \
                     Unset it to use another archive or to build the Lean frontend from source, \
                     or set DOGWOOD_LEAN_FROM_SOURCE=1."
                );
            }
            return Some(dir);
        }
        for bin in env::split_paths(&env::var_os("PATH").unwrap_or_default()) {
            if bin.as_os_str().is_empty() {
                continue;
            }
            let dir = bin.join("../lib");
            let archive = dir.join(ARCHIVE);
            if !archive.is_file() || !dir.join(MANIFEST).is_file() {
                continue;
            }
            // Only this package's own published archive, or its copy in a library farm.
            let Ok(real) = fs::canonicalize(&archive) else {
                continue;
            };
            if !published_location(&real) {
                continue;
            }
            match verify(&dir, hash, bridge) {
                Ok(()) => return Some(dir),
                Err(why) => println!("cargo:warning=ignoring {}: {why}", archive.display()),
            }
        }
        None
    }

    /// Whether `real`, an archive's path with links resolved, is where this package's
    /// published archive reaches a dependent's build: inside the package's artifact (a path
    /// segment [`PACKAGE`] or `<PACKAGE>-<version>`), or in the `lib/` of a library farm
    /// (`…/<farm>/<target>.libfarm/lib/`, `<farm>` being the fixed name checked below), into
    /// which a build system copies the published `lib/` of each package of its dependency
    /// closure.
    fn published_location(real: &Path) -> bool {
        let parts: Vec<String> = real
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect();
        let in_artifact = parts
            .iter()
            .any(|c| c == PACKAGE || c.starts_with(&format!("{PACKAGE}-")));
        let n = parts.len();
        let in_farm = n >= 4
            && parts[n - 2] == "lib"
            && parts[n - 3].ends_with(".libfarm")
            && parts[n - 4] == "brazil-path";
        in_artifact || in_farm
    }

    /// Whether `dir`'s archive is this crate's: its manifest's Lean version is this crate's,
    /// its source digest `hash` when the sources are here (else its bridge digest
    /// `bridge`), and the archive file's SHA-256 digest the one the manifest records.
    fn verify(dir: &Path, hash: Option<&str>, bridge: &str) -> Result<(), String> {
        let manifest = dir.join(MANIFEST);
        if !manifest.is_file() {
            return Err(format!("there is no manifest {}", manifest.display()));
        }
        let m = read_manifest(&manifest);
        if m.lean_version != LEAN_VERSION {
            return Err(format!(
                "it was built with Lean `{}`; this crate's Lean is {LEAN_VERSION}",
                m.lean_version
            ));
        }
        if m.source.len() != 64 {
            return Err("its manifest records no source digest".into());
        }
        match hash {
            Some(hash) if m.source != hash => {
                return Err(format!(
                    "it was built from other sources (digest {}; this crate's is {hash})",
                    m.source
                ));
            }
            Some(_) => {}
            None if m.bridge != bridge => {
                return Err(format!(
                    "it was built by another version of this crate (bridge digest {}; this \
                     crate's is {bridge}), and this crate has no Lean sources to check it \
                     against",
                    if m.bridge.is_empty() {
                        "none"
                    } else {
                        &m.bridge
                    }
                ));
            }
            None => {}
        }
        let archive = dir.join(ARCHIVE);
        if !archive.is_file() {
            return Err(format!("there is no archive {}", archive.display()));
        }
        let digest = sha256_file(&archive);
        if m.archive != digest {
            return Err(format!(
                "the archive's SHA-256 digest {digest} is not the manifest's ({})",
                if m.archive.is_empty() {
                    "none"
                } else {
                    &m.archive
                }
            ));
        }
        Ok(())
    }

    /// A prebuilt archive's built packages, copied from `dir` into `out_dir`, when the
    /// manifest lists them, they are there, and their files have the manifest's digest
    /// (else none). Lake writes into a package's directory when it loads its configuration
    /// (a lock file), and a published directory may be read-only.
    fn prebuilt_packages(dir: &Path, out_dir: &Path, m: &Manifest) -> Vec<(String, PathBuf)> {
        let present = !m.packages.is_empty()
            && m.packages
                .iter()
                .all(|(_, rel)| dir.join(rel).join("lakefile.lean").is_file());
        if !present {
            return Vec::new();
        }
        let files = package_files(dir, &m.packages);
        let digest = files_hash(dir, &files, Some(out_dir));
        if digest != m.packages_digest {
            println!(
                "cargo:warning=the Lean packages next to {} are not the ones its manifest \
                 records (digest {digest}, the manifest's {}): DEP_DOGWOOD_LEAN_PACKAGES is \
                 empty",
                dir.join(ARCHIVE).display(),
                if m.packages_digest.is_empty() {
                    "none"
                } else {
                    &m.packages_digest
                }
            );
            return Vec::new();
        }
        m.packages
            .iter()
            .map(|(name, rel)| (name.clone(), out_dir.join(rel)))
            .collect()
    }

    /// A manifest's contents.
    struct Manifest {
        /// The SHA-256 digest of the sources (`source_hash`).
        source: String,
        /// The SHA-256 digest of the archive file.
        archive: String,
        /// The SHA-256 digest of the crate's side of the bridge (`bridge_hash`).
        bridge: String,
        /// The Lean version the archive and the packages were built with.
        lean_version: String,
        dylibs: Vec<String>,
        /// The built Lake packages, by name, relative to the manifest's directory.
        packages: Vec<(String, PathBuf)>,
        /// The SHA-256 digest of the packages' files (`package_files`, `files_hash`).
        packages_digest: String,
        /// The Rust release of the Unicode tables the Lean frontend escapes strings with
        /// (`tables_rust_version`).
        tables_rust: String,
    }

    fn read_manifest(path: &Path) -> Manifest {
        let text =
            fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        let mut m = Manifest {
            source: String::new(),
            archive: String::new(),
            bridge: String::new(),
            lean_version: String::new(),
            dylibs: Vec::new(),
            packages: Vec::new(),
            packages_digest: String::new(),
            tables_rust: String::new(),
        };
        for line in text.lines() {
            match line.split_once(' ') {
                Some(("source-sha256", h)) => m.source = h.to_owned(),
                Some(("archive-sha256", h)) => m.archive = h.to_owned(),
                Some(("bridge-sha256", h)) => m.bridge = h.to_owned(),
                Some(("packages-sha256", h)) => m.packages_digest = h.to_owned(),
                Some(("tables-rust-version", v)) => m.tables_rust = v.to_owned(),
                Some(("lean-version", v)) => m.lean_version = v.to_owned(),
                Some(("dylib", l)) => m.dylibs.push(l.to_owned()),
                Some(("package", p)) => {
                    if let Some((name, rel)) = p.split_once(' ') {
                        m.packages.push((name.to_owned(), PathBuf::from(rel)));
                    }
                }
                _ => {}
            }
        }
        m
    }

    fn manifest_text(m: &Manifest) -> String {
        let mut s = format!(
            "source-sha256 {}\narchive-sha256 {}\nbridge-sha256 {}\nlean-version {}\n",
            m.source, m.archive, m.bridge, m.lean_version
        );
        for (name, rel) in &m.packages {
            s.push_str(&format!("package {name} {}\n", rel.display()));
        }
        s.push_str(&format!("packages-sha256 {}\n", m.packages_digest));
        s.push_str(&format!("tables-rust-version {}\n", m.tables_rust));
        for l in &m.dylibs {
            s.push_str(&format!("dylib {l}\n"));
        }
        s
    }

    fn hex(digest: &[u8]) -> String {
        digest.iter().map(|b| format!("{b:02x}")).collect()
    }

    fn sha256_file(path: &Path) -> String {
        let bytes = fs::read(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        hex(&Sha256::digest(&bytes))
    }

    /// SHA-256 over files with their relative paths, in sorted order: each path, a NUL,
    /// the file's length (8 bytes, big-endian), and the file.
    fn tree_hash(mut all: Vec<(String, PathBuf)>) -> String {
        all.sort();
        let mut hasher = Sha256::new();
        for (rel, f) in all {
            let bytes = fs::read(&f).unwrap_or_else(|e| panic!("read {}: {e}", f.display()));
            hasher.update(rel.as_bytes());
            hasher.update([0]);
            hasher.update((bytes.len() as u64).to_be_bytes());
            hasher.update(&bytes);
        }
        hex(&hasher.finalize())
    }

    /// The digest of the archive's sources: the Lean project's inputs and the shim
    /// ([`tree_hash`], with the paths `dogwood-lean/<input>` and the shim's).
    fn source_hash(manifest_dir: &Path, source: &Path) -> String {
        let mut all: Vec<(String, PathBuf)> = Vec::new();
        for input in LEAN_INPUTS {
            files(&source.join(input), &mut |f| {
                let rel = f.strip_prefix(source).expect("inside the project");
                all.push((format!("dogwood-lean/{}", rel.display()), f.to_owned()));
            });
        }
        all.push((SHIM.to_owned(), manifest_dir.join(SHIM)));
        tree_hash(all)
    }

    /// The digest of the crate's side of the bridge ([`BRIDGE`], [`tree_hash`]), which a
    /// crate fetched from a registry holds: a prebuilt archive is used without the Lean
    /// sources only by a crate whose bridge is the one that built it.
    fn bridge_hash(manifest_dir: &Path) -> String {
        let mut all: Vec<(String, PathBuf)> = Vec::new();
        for b in BRIDGE {
            files(&manifest_dir.join(b), &mut |f| {
                let rel = f.strip_prefix(manifest_dir).expect("inside the crate");
                all.push((rel.display().to_string(), f.to_owned()));
            });
        }
        tree_hash(all)
    }

    /// Every file under `p` (or `p` itself).
    fn files(p: &Path, f: &mut dyn FnMut(&Path)) {
        if p.is_dir() {
            let mut entries: Vec<PathBuf> = fs::read_dir(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()))
                .map(|e| e.expect("dir entry").path())
                .collect();
            entries.sort();
            for e in entries {
                files(&e, f);
            }
        } else {
            f(p);
        }
    }

    /// The files of the built Lake `packages` under `dir` that a dependent needs, relative
    /// to `dir`: everything under each package root but its git metadata and its `.lake/`,
    /// of which only `build/lib/lean/` (the `.olean`, `.ilean` and trace files) and
    /// `build/ir/` without the objects (the C and Lake's traces of it, which Lake checks to
    /// find the modules up to date) are needed; a package root inside another's is the
    /// other package's.
    fn package_files(dir: &Path, packages: &[(String, PathBuf)]) -> Vec<PathBuf> {
        let roots: BTreeSet<PathBuf> = packages.iter().map(|(_, rel)| dir.join(rel)).collect();
        let mut out: BTreeSet<PathBuf> = BTreeSet::new();
        fn walk(p: &Path, root: &Path, roots: &BTreeSet<PathBuf>, out: &mut BTreeSet<PathBuf>) {
            let Ok(entries) = fs::read_dir(p) else {
                return;
            };
            for entry in entries {
                let path = entry.expect("dir entry").path();
                let name = path.file_name().unwrap_or_default();
                if path.is_dir() {
                    if name == ".git" || (path != *root && roots.contains(&path)) {
                        continue;
                    }
                    if p == root && name == ".lake" {
                        for sub in ["build/lib/lean", "build/ir"] {
                            walk_all(&path.join(sub), out);
                        }
                        continue;
                    }
                    walk(&path, root, roots, out);
                } else {
                    out.insert(path);
                }
            }
        }
        fn walk_all(p: &Path, out: &mut BTreeSet<PathBuf>) {
            if !p.is_dir() {
                return;
            }
            files(p, &mut |f| {
                let name = f.file_name().unwrap_or_default().to_string_lossy();
                // The objects: the archive holds their code.
                let object = [".o", ".o.export", ".o.noexport"]
                    .iter()
                    .any(|s| name.ends_with(s));
                if !object {
                    out.insert(f.to_owned());
                }
            });
        }
        for root in &roots {
            walk(root, root, &roots, &mut out);
        }
        out.into_iter()
            .map(|f| f.strip_prefix(dir).expect("under dir").to_owned())
            .collect()
    }

    /// [`tree_hash`] of `files` (relative to `dir`), copying each into `copy_to` (under the
    /// same relative path, rewriting only a file whose content differs) when given.
    fn files_hash(dir: &Path, files: &[PathBuf], copy_to: Option<&Path>) -> String {
        let mut hasher = Sha256::new();
        let mut sorted: Vec<&PathBuf> = files.iter().collect();
        sorted.sort_by_key(|f| f.display().to_string());
        for rel in sorted {
            let src = dir.join(rel);
            let bytes = fs::read(&src).unwrap_or_else(|e| panic!("read {}: {e}", src.display()));
            hasher.update(rel.display().to_string().as_bytes());
            hasher.update([0]);
            hasher.update((bytes.len() as u64).to_be_bytes());
            hasher.update(&bytes);
            if let Some(to) = copy_to {
                let dst = to.join(rel);
                if fs::read(&dst).ok().as_deref() != Some(bytes.as_slice()) {
                    fs::create_dir_all(dst.parent().expect("parent"))
                        .unwrap_or_else(|e| panic!("create {}: {e}", dst.display()));
                    fs::write(&dst, &bytes)
                        .unwrap_or_else(|e| panic!("write {}: {e}", dst.display()));
                }
            }
        }
        hex(&hasher.finalize())
    }

    // ── From source ─────────────────────────────────────────────────────

    /// What a build from source produced besides the archive.
    struct Built {
        /// The toolchain's prefix.
        prefix: PathBuf,
        /// The C compiler and archiver used for Lean's C.
        cc: OsString,
        ar: OsString,
        /// The shared libraries the archive needs, and where to search for them.
        dylibs: Vec<String>,
        link_search: Vec<PathBuf>,
        /// The built Lake packages, by name, relative to `$OUT_DIR`.
        packages: Vec<(String, PathBuf)>,
    }

    /// Build `$OUT_DIR/libdogwood_lean_frontend.a`.
    fn build_from_source(manifest_dir: &Path, source: &Path, out_dir: &Path) -> Built {
        // 1. The project, copied, with its dependencies.
        let work = out_dir.join(PROJECT);
        for input in LEAN_INPUTS {
            sync(&source.join(input), &work.join(input), &|name| {
                name != ".lake"
            });
        }
        let packages = source.join(".lake/packages");
        if packages.is_dir() {
            for entry in fs::read_dir(&packages).expect("read the Lean packages") {
                let entry = entry.expect("dir entry");
                // The dependency's sources and git metadata, not its build outputs.
                sync(
                    &entry.path(),
                    &work.join(".lake/packages").join(entry.file_name()),
                    &|name| name != ".lake",
                );
            }
        } else {
            use_vendored(&work);
        }
        let dependencies = lean_configurations(&work);

        // 2. The toolchain.
        let prefix = lean_prefix(&work);
        let lean_lib_dir = prefix.join("lib/lean");
        let include_dir = include_dir(&prefix);
        if !include_dir.join("lean/lean.h").is_file() || !lean_lib_dir.join("libleanrt.a").is_file()
        {
            panic!(
                "{} is not a Lean toolchain (no include/lean/lean.h or lib/lean/libleanrt.a); the \
                 Lean frontend needs Lean {LEAN_VERSION}",
                prefix.display()
            );
        }

        // 3. The Lean frontend.
        let mut lean_cc: OsString =
            env::var_os("LEAN_CC").unwrap_or_else(|| cc::Build::new().get_compiler().path().into());
        if include_dir != prefix.join("include") {
            // Lake compiles Lean's C with `-I <prefix>/include`: give it a compiler that also
            // searches where the headers are.
            let wrapper = out_dir.join("lean-cc");
            let text = format!(
                "#!/bin/sh\nexec '{}' -I '{}' \"$@\"\n",
                Path::new(&lean_cc).display(),
                include_dir.display()
            );
            if fs::read_to_string(&wrapper).ok().as_deref() != Some(text.as_str()) {
                fs::write(&wrapper, text).expect("write the compiler wrapper");
            }
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&wrapper, fs::Permissions::from_mode(0o755))
                .expect("make the compiler wrapper executable");
            lean_cc = wrapper.into();
        }
        let lean_ar: OsString = env::var_os("LEAN_AR")
            .unwrap_or_else(|| cc::Build::new().get_archiver().get_program().to_owned());
        let lake = lake_command(&prefix);
        check_version(&prefix, &lake);
        run(Command::new(&lake)
            .args(["build", "frontendFfi"])
            .current_dir(&work)
            .env("LEAN_CC", &lean_cc)
            .env("LEAN_AR", &lean_ar));
        let frontend = work.join(".lake/build/lib").join(LEAN_LIB);

        // 4. The shim.
        cc::Build::new()
            .file(manifest_dir.join(SHIM))
            .include(&include_dir)
            .opt_level(2)
            .warnings(true)
            .cargo_metadata(false)
            .compile("dogwood_lean_shim");
        let shim = out_dir.join("libdogwood_lean_shim.a");

        // 5. One archive. On Linux, the shim, the frontend's library and the whole of Lean's
        // runtime and standard library, with the members of Lean's other libraries (and of
        // the extra archives) they reach, are first linked into one relocatable object (each
        // member whole, as a final link takes it): most of `libLean.a` is Lean's elaborator,
        // which the frontend does not run.
        let sys_lib = prefix.join("lib");
        let extra: Vec<PathBuf> = split_paths("DOGWOOD_LEAN_EXTRA_ARCHIVES");
        for a in &extra {
            println!("cargo:rerun-if-changed={}", a.display());
        }
        let mut dylibs: Vec<String> = Vec::new();
        let mut link_search: Vec<PathBuf> = Vec::new();
        let mut static_deps: Vec<PathBuf> = Vec::new();
        if sys_lib.join("libc++.a").is_file() {
            // An upstream toolchain: the runtime's dependencies are static too.
            static_deps.extend(
                ["libc++.a", "libc++abi.a", "libgmp.a", "libuv.a"].map(|l| sys_lib.join(l)),
            );
        } else if extra.is_empty() {
            // A toolchain built against shared libraries, and no static ones given.
            link_search.extend(split_paths("DOGWOOD_LEAN_LINK_SEARCH"));
            link_search.push(lean_lib_dir.clone());
            link_search.push(sys_lib.clone());
            dylibs.extend(["stdc++", "gmp", "uv"].map(String::from));
            if link_search
                .iter()
                .any(|d| d.join("libmimalloc.so").exists() || d.join("libmimalloc.a").exists())
            {
                dylibs.push("mimalloc".into());
            }
        }
        static_deps.extend(extra);
        let whole: Vec<PathBuf> = [shim, frontend]
            .into_iter()
            .chain(WHOLE_LEAN_LIBS.iter().map(|l| lean_lib_dir.join(l)))
            .collect();
        let reached: Vec<PathBuf> = REACHED_LEAN_LIBS
            .iter()
            .map(|l| lean_lib_dir.join(l))
            .collect();
        let mut members = Vec::new();
        let prelinked = cfg!(target_os = "linux").then(|| out_dir.join("dogwood_lean_frontend.o"));
        match &prelinked {
            Some(object) => {
                let group: Vec<PathBuf> = reached.into_iter().chain(static_deps).collect();
                prelink(&whole, &group, object);
                members.push(object.clone());
            }
            None => {
                members.extend(whole);
                members.extend(reached);
                members.extend(static_deps);
            }
        }
        merge_archives(&lean_ar, &members, &out_dir.join(ARCHIVE), out_dir);
        if let Some(object) = prelinked {
            // The archive holds a copy.
            let _ = fs::remove_file(object);
        }

        if cfg!(target_os = "linux") {
            dylibs.extend(BASE_DYLIBS.iter().map(|s| s.to_string()));
        } else {
            dylibs.push("m".into());
        }
        let mut packages = vec![(ROOT_PACKAGE.to_owned(), PathBuf::from(PROJECT))];
        packages.extend(
            dependencies
                .into_iter()
                .map(|(name, rel)| (name, Path::new(PROJECT).join(rel))),
        );
        Built {
            prefix,
            cc: lean_cc,
            ar: lean_ar,
            dylibs,
            link_search,
            packages,
        }
    }

    /// The directory of the toolchain at `prefix` holding `lean/lean.h`: `include/`, else
    /// `stage1/include/` (a toolchain installed from its build tree).
    fn include_dir(prefix: &Path) -> PathBuf {
        ["include", "stage1/include"]
            .iter()
            .map(|d| prefix.join(d))
            .find(|d| d.join("lean/lean.h").is_file())
            .unwrap_or_else(|| prefix.join("include"))
    }

    /// The `lake` command: `$LAKE`, else the toolchain's, else `lake` on `PATH`.
    fn lake_command(prefix: &Path) -> OsString {
        env::var_os("LAKE").unwrap_or_else(|| {
            let bundled = prefix.join("bin/lake");
            if bundled.is_file() {
                bundled.into()
            } else {
                "lake".into()
            }
        })
    }

    /// The pinned export `vendor/` stands in for the project's `.lake/packages`: check its
    /// files against `vendor/MANIFEST`, and name each package it exports as a path
    /// dependency in the copy's `lake-manifest.json`, at the revision the manifest pins.
    fn use_vendored(work: &Path) {
        let vendor = work.join(VENDOR);
        let text = fs::read_to_string(work.join(VENDOR_MANIFEST)).unwrap_or_else(|e| {
            panic!(
                "the Lean project has neither `.lake/packages` nor a pinned export of its \
                 dependencies (`{VENDOR_MANIFEST}`: {e})"
            )
        });
        let (body, last) = text
            .trim_end_matches('\n')
            .rsplit_once('\n')
            .unwrap_or_default();
        let tree = last.strip_prefix("tree-sha256 ").unwrap_or_default();
        if tree != hex(&Sha256::digest(format!("{body}\n").as_bytes())) {
            panic!("{VENDOR_MANIFEST}: its digest does not match its contents");
        }
        // origin <dir> <package> <revision> <subdirectory> <repository>
        let mut origins: Vec<(String, String, String)> = Vec::new();
        for line in body.lines() {
            let fields: Vec<&str> = line.split(' ').collect();
            match fields.as_slice() {
                ["sha256", digest, rel] => {
                    let path = vendor.join(rel);
                    let actual = fs::read(&path)
                        .map(|b| hex(&Sha256::digest(&b)))
                        .unwrap_or_else(|e| panic!("{VENDOR_MANIFEST}: {}: {e}", path.display()));
                    if actual != *digest {
                        panic!(
                            "{VENDOR_MANIFEST}: {rel} has the SHA-256 digest {actual}, not the \
                             manifest's {digest}"
                        );
                    }
                }
                ["origin", dir, name, rev, ..] => {
                    origins.push((dir.to_string(), name.to_string(), rev.to_string()))
                }
                _ => {}
            }
        }
        let manifest_path = work.join("lake-manifest.json");
        let mut manifest = fs::read_to_string(&manifest_path)
            .unwrap_or_else(|e| panic!("read {}: {e}", manifest_path.display()));
        for entry in manifest_entries(&manifest) {
            if json_string(&entry, "type").as_deref() != Some("git") {
                continue;
            }
            let name = json_string(&entry, "name").unwrap_or_default();
            let Some((dir, _, rev)) = origins.iter().find(|(_, n, _)| *n == name) else {
                panic!(
                    "the Lean project's dependency `{name}` is not in its pinned export \
                     (`{VENDOR_MANIFEST}`); run `dogwood-lean/scripts/vendor_deps.py write`"
                );
            };
            if json_string(&entry, "rev").as_deref() != Some(rev.as_str()) {
                panic!(
                    "the pinned export of `{name}` (`{VENDOR_MANIFEST}`) is not at the revision \
                     lake-manifest.json records; run `dogwood-lean/scripts/vendor_deps.py write`"
                );
            }
            let scope = json_string(&entry, "scope").unwrap_or_default();
            let inherited = entry.contains("\"inherited\": true");
            let config =
                json_string(&entry, "configFile").unwrap_or_else(|| "lakefile.lean".into());
            let path_entry = format!(
                "{{\"type\": \"path\", \"scope\": \"{scope}\", \"name\": \"{name}\", \
                 \"manifestFile\": \"lake-manifest.json\", \"inherited\": {inherited}, \
                 \"dir\": \"{VENDOR}/{dir}\", \"configFile\": \"{config}\"}}"
            );
            manifest = manifest.replacen(&entry, &path_entry, 1);
        }
        if fs::read_to_string(&manifest_path).ok().as_deref() != Some(manifest.as_str()) {
            fs::write(&manifest_path, &manifest)
                .unwrap_or_else(|e| panic!("write {}: {e}", manifest_path.display()));
        }
    }

    /// The Lake packages of the copied project at `work`, other than its own, by name, with
    /// their roots relative to `work` (a path dependency's `dir`, else `.lake/packages/<name>`,
    /// then the manifest's `subDir`). A package configured in `lakefile.toml` only is given
    /// the equivalent `lakefile.lean` ([`toml_to_lean`]), and the copy's `lake-manifest.json`
    /// names it, so that every package root has a `lakefile.lean` and this build and a
    /// dependent's load the same configuration.
    fn lean_configurations(work: &Path) -> Vec<(String, PathBuf)> {
        let manifest_path = work.join("lake-manifest.json");
        let mut manifest = fs::read_to_string(&manifest_path)
            .unwrap_or_else(|e| panic!("read {}: {e}", manifest_path.display()));
        let mut out = Vec::new();
        for entry in manifest_entries(&manifest) {
            let name = json_string(&entry, "name")
                .unwrap_or_else(|| panic!("a package of lake-manifest.json has no name: {entry}"));
            let rel = match json_string(&entry, "type").as_deref() {
                Some("path") => PathBuf::from(json_string(&entry, "dir").unwrap_or_else(|| {
                    panic!("a path package of lake-manifest.json has no dir: {entry}")
                })),
                _ => {
                    let mut rel = PathBuf::from(".lake/packages").join(&name);
                    if let Some(sub) = json_string(&entry, "subDir") {
                        rel.push(sub);
                    }
                    rel
                }
            };
            let root = work.join(&rel);
            let (lean, toml) = (root.join("lakefile.lean"), root.join("lakefile.toml"));
            if json_string(&entry, "configFile").as_deref() == Some("lakefile.toml") {
                if toml.is_file() {
                    let text = fs::read_to_string(&toml)
                        .unwrap_or_else(|e| panic!("read {}: {e}", toml.display()));
                    let generated = toml_to_lean(&name, &text);
                    if fs::read_to_string(&lean).ok().as_deref() != Some(generated.as_str()) {
                        fs::write(&lean, generated)
                            .unwrap_or_else(|e| panic!("write {}: {e}", lean.display()));
                    }
                }
                let fixed = entry.replacen(
                    "\"configFile\": \"lakefile.toml\"",
                    "\"configFile\": \"lakefile.lean\"",
                    1,
                );
                manifest = manifest.replacen(&entry, &fixed, 1);
            }
            out.push((name, rel));
        }
        if fs::read_to_string(&manifest_path).ok().as_deref() != Some(manifest.as_str()) {
            fs::write(&manifest_path, &manifest)
                .unwrap_or_else(|e| panic!("write {}: {e}", manifest_path.display()));
        }
        out
    }

    /// The text of each object of the `packages` array of a `lake-manifest.json` (Lake writes
    /// flat objects there: no nested object or array, and no brace inside a string).
    fn manifest_entries(manifest: &str) -> Vec<String> {
        let Some(start) = manifest.find("\"packages\"") else {
            return Vec::new();
        };
        let rest = &manifest[start..];
        let Some(open) = rest.find('[') else {
            return Vec::new();
        };
        let mut out = Vec::new();
        let mut depth = 0usize;
        let mut begin = 0usize;
        for (i, c) in rest[open + 1..].char_indices() {
            match c {
                '{' => {
                    if depth == 0 {
                        begin = i;
                    }
                    depth += 1;
                }
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        out.push(rest[open + 1 + begin..open + 1 + i + 1].to_owned());
                    }
                }
                ']' if depth == 0 => break,
                _ => {}
            }
        }
        out
    }

    /// The string value of `key` in a flat JSON object's text (`None` for `null`, or when
    /// absent). The values Lake writes there need no unescaping.
    fn json_string(object: &str, key: &str) -> Option<String> {
        let at = object.find(&format!("\"{key}\""))?;
        let rest = object[at + key.len() + 2..]
            .trim_start()
            .strip_prefix(':')?;
        let rest = rest.trim_start().strip_prefix('"')?;
        Some(rest[..rest.find('"')?].to_owned())
    }

    /// A `lakefile.lean` equivalent to the `lakefile.toml` `text` of package `name`, for what
    /// a build of the package's libraries reads: the package's name and Lean options, and its
    /// libraries that are named only (the others, test libraries with globs and options of
    /// their own, and the executables, scripts and drivers are not needed to build the
    /// frontend). Anything else is an error, so that a new kind of configuration is noticed.
    fn toml_to_lean(name: &str, text: &str) -> String {
        enum Table {
            Top,
            Options,
            Lib,
            Skipped,
        }
        let mut table = Table::Top;
        let mut options: Vec<(String, String)> = Vec::new();
        let mut libs: Vec<String> = Vec::new();
        let mut lib: Option<(Option<String>, bool)> = None;
        let finish = |lib: &mut Option<(Option<String>, bool)>, libs: &mut Vec<String>| {
            if let Some((Some(n), true)) = lib.take() {
                libs.push(n);
            }
        };
        let unquote = |v: &str| -> Option<String> {
            v.strip_prefix('"')
                .and_then(|v| v.strip_suffix('"'))
                .filter(|v| !v.contains(['"', '\\']))
                .map(str::to_owned)
        };
        for raw in text.lines() {
            let line = raw.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            if line.starts_with('[') {
                finish(&mut lib, &mut libs);
                table = match line {
                    "[leanOptions]" => Table::Options,
                    "[[lean_lib]]" => {
                        lib = Some((None, true));
                        Table::Lib
                    }
                    "[[lean_exe]]" => Table::Skipped,
                    _ => panic!(
                        "{name}'s lakefile.toml has a table `{line}` the build cannot translate \
                         into a lakefile.lean (build.rs, toml_to_lean)"
                    ),
                };
                continue;
            }
            let (key, value) = line
                .split_once('=')
                .map(|(k, v)| (k.trim(), v.trim()))
                .unwrap_or_else(|| panic!("{name}'s lakefile.toml: not a key and value: {line}"));
            match table {
                Table::Top => match key {
                    "name" => assert_eq!(
                        unquote(value).as_deref(),
                        Some(name),
                        "{name}'s lakefile.toml names another package"
                    ),
                    "testDriver" | "lintDriver" | "defaultTargets" => {}
                    _ => panic!(
                        "{name}'s lakefile.toml has a key `{key}` the build cannot translate \
                         (build.rs, toml_to_lean)"
                    ),
                },
                Table::Options => {
                    let value = match value {
                        "true" | "false" => value.to_owned(),
                        v if v.parse::<u64>().is_ok() => v.to_owned(),
                        v => format!(
                            "\"{}\"",
                            unquote(v).unwrap_or_else(|| panic!(
                                "{name}'s lakefile.toml: an option value the build cannot \
                                 translate: {line}"
                            ))
                        ),
                    };
                    options.push((key.to_owned(), value));
                }
                Table::Lib => {
                    let entry = lib.as_mut().expect("in a library");
                    match key {
                        "name" => entry.0 = unquote(value),
                        _ => entry.1 = false,
                    }
                }
                Table::Skipped => {}
            }
        }
        finish(&mut lib, &mut libs);
        let options = options
            .iter()
            .map(|(k, v)| format!("⟨`{k}, {v}⟩"))
            .collect::<Vec<_>>()
            .join(", ");
        let mut s = format!(
            "import Lake\nopen Lake DSL\n\n/-\nWritten by the build of the `dogwood-language` \
             crate's Lean frontend: the configuration of `lakefile.toml` that a build of this \
             package's libraries reads, for a Lake workspace that requires the package by a \
             path to a `lakefile.lean`.\n-/\n\npackage {name} where\n  leanOptions := #[{options}]\n"
        );
        for l in libs {
            s.push_str(&format!("\nlean_lib {l}\n"));
        }
        s
    }

    /// The prefix of a Lean toolchain (the directory holding `bin/`, `lib/`, and the
    /// headers), or a build failure that says how to get one.
    fn lean_prefix(project: &Path) -> PathBuf {
        match env::var_os("LEAN_SYSROOT") {
            Some(p) => PathBuf::from(p),
            None => {
                let out = Command::new("lean")
                    .arg("--print-prefix")
                    .current_dir(project)
                    .output()
                    .unwrap_or_else(|e| {
                        panic!(
                            "cannot run `lean` ({e}). The `lean-frontend` feature builds the Lean \
                             frontend, which needs a Lean {LEAN_VERSION} toolchain: install elan \
                             (https://github.com/leanprover/elan), which reads \
                             `dogwood-lean/lean-toolchain`, or set LEAN_SYSROOT to a toolchain; \
                             or set DOGWOOD_LEAN_PREBUILT to a prebuilt archive."
                        )
                    });
                if !out.status.success() {
                    panic!(
                        "`lean --print-prefix` failed in {}: {}",
                        project.display(),
                        String::from_utf8_lossy(&out.stderr)
                    );
                }
                PathBuf::from(String::from_utf8_lossy(&out.stdout).trim())
            }
        }
    }

    /// Fail unless the toolchain is Lean 4.34.0: as `bin/lean --version` reports it, or
    /// `lake --version` (`lake` may be a script that sets the library path a toolchain's
    /// binaries need, which `bin/lean` alone may not find).
    fn check_version(prefix: &Path, lake: &OsString) {
        let lean = prefix.join("bin/lean");
        let report = |cmd: &mut Command| {
            cmd.arg("--version")
                .output()
                .ok()
                .filter(|o| o.status.success())
                .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_owned())
        };
        let from_lean = report(&mut Command::new(&lean));
        if from_lean
            .as_deref()
            .is_some_and(|v| v.contains(&format!("version {LEAN_VERSION},")))
        {
            return;
        }
        let from_lake = report(&mut Command::new(lake));
        if from_lake
            .as_deref()
            .is_some_and(|v| v.contains(&format!("(Lean version {LEAN_VERSION})")))
        {
            return;
        }
        panic!(
            "the Lean toolchain at {} is `{}` (`{}`); the Lean frontend needs Lean \
             {LEAN_VERSION} (`dogwood-lean/lean-toolchain`). Set LEAN_SYSROOT to a \
             {LEAN_VERSION} toolchain, or let elan select it.",
            prefix.display(),
            from_lean.unwrap_or_else(|| format!("{} does not run", lean.display())),
            from_lake.unwrap_or_else(|| format!("{lake:?} --version does not run")),
        );
    }

    /// Copy `src` (a file or a directory tree) to `dst`, rewriting only files whose
    /// content changed, so that Lake's up-to-date checks see stable inputs. A directory
    /// entry is copied only when `keep` accepts its name.
    fn sync(src: &Path, dst: &Path, keep: &dyn Fn(&str) -> bool) {
        if src.is_dir() {
            fs::create_dir_all(dst).unwrap_or_else(|e| panic!("create {}: {e}", dst.display()));
            for entry in fs::read_dir(src).unwrap_or_else(|e| panic!("read {}: {e}", src.display()))
            {
                let entry = entry.expect("dir entry");
                let name = entry.file_name();
                if keep(&name.to_string_lossy()) {
                    sync(&entry.path(), &dst.join(&name), keep);
                }
            }
        } else if src.is_file() {
            let bytes = fs::read(src).unwrap_or_else(|e| panic!("read {}: {e}", src.display()));
            if fs::read(dst).ok().as_deref() != Some(bytes.as_slice()) {
                fs::create_dir_all(dst.parent().expect("parent"))
                    .unwrap_or_else(|e| panic!("create {}: {e}", dst.display()));
                fs::write(dst, bytes).unwrap_or_else(|e| panic!("write {}: {e}", dst.display()));
            }
        }
    }

    /// Link into the relocatable object `out` (`-r`), without debug sections (`-S`), every
    /// member of `whole`, and the members of `reached` they need, transitively.
    fn prelink(whole: &[PathBuf], reached: &[PathBuf], out: &Path) {
        let _ = fs::remove_file(out);
        let mut cmd = cc::Build::new().get_compiler().to_command();
        cmd.args(["-r", "-nostdlib", "-Wl,-S", "-o"])
            .arg(out)
            .arg("-Wl,--whole-archive")
            .args(whole)
            .arg("-Wl,--no-whole-archive")
            .arg("-Wl,--start-group")
            .args(reached)
            .arg("-Wl,--end-group");
        run(&mut cmd);
    }

    /// Combine static archives (and objects) into one.
    fn merge_archives(ar: &OsString, members: &[PathBuf], out: &Path, scratch: &Path) {
        for m in members {
            assert!(m.is_file(), "missing static library {}", m.display());
        }
        let _ = fs::remove_file(out);
        if cfg!(target_os = "macos") {
            run(Command::new("libtool")
                .arg("-static")
                .arg("-o")
                .arg(out)
                .args(members));
            return;
        }
        // GNU ar's MRI script. MRI treats `+` as a line continuation, so every member is
        // first linked under a plain name.
        let staging = scratch.join("archive-members");
        let _ = fs::remove_dir_all(&staging);
        fs::create_dir_all(&staging).expect("create the staging directory");
        let mut script = format!("CREATE {}\n", out.display());
        for (i, m) in members.iter().enumerate() {
            let object = m.extension().is_some_and(|e| e == "o");
            let link = staging.join(format!("member{i}.{}", if object { "o" } else { "a" }));
            std::os::unix::fs::symlink(m, &link).expect("link an archive member");
            let command = if object { "ADDMOD" } else { "ADDLIB" };
            script.push_str(&format!("{command} {}\n", link.display()));
        }
        script.push_str("SAVE\nEND\n");
        let mut child = Command::new(ar)
            .arg("-M")
            .stdin(std::process::Stdio::piped())
            .spawn()
            .unwrap_or_else(|e| panic!("cannot run {ar:?}: {e}"));
        use std::io::Write;
        child
            .stdin
            .take()
            .expect("stdin")
            .write_all(script.as_bytes())
            .expect("write the MRI script");
        let status = child.wait().expect("wait for ar");
        assert!(status.success(), "`{ar:?} -M` failed merging {members:?}");
    }

    fn run(cmd: &mut Command) {
        let out = cmd
            .output()
            .unwrap_or_else(|e| panic!("cannot run {cmd:?}: {e}"));
        if !out.status.success() {
            panic!(
                "{cmd:?} failed ({}):\n--- stdout ---\n{}\n--- stderr ---\n{}",
                out.status,
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
        }
    }
}
