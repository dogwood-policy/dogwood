//! With the `lean` feature, compiles `lean/` against the Lean library of the
//! `dogwood-language` crate and links it with that crate's Lean runtime, as
//! any crate that links Lean code of its own does: from the link metadata the
//! language crate's build script prints (`links = "dogwood_lean"`), read here as
//! `DEP_DOGWOOD_LEAN_*`.
//!
//! 1. Write a Lake project in `$OUT_DIR/lean` whose lakefile requires the
//!    published packages (`PACKAGES`) by path, with a manifest that lists them,
//!    and this crate's module (`lean/DependentProbe.lean`).
//! 2. Check that Lake finds the library up to date in this workspace (`lake build
//!    --no-build Dogwood.Frontend.Library`): it must build nothing of it.
//! 3. Build this crate's module only (`lake build DependentProbe:static`), with
//!    the language crate's toolchain (`TOOLCHAIN`) and C compiler (`CC`).
//! 4. Compile the shim (`src/shim.c`) against the toolchain's `lean.h`, and link
//!    it and the module's archive: neither holds a Lean runtime or a module of the
//!    library; their references resolve in the language crate's archive, which
//!    rustc passes after them.
//!
//! Without the feature it does nothing.

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=lean");
    println!("cargo:rerun-if-changed=src/shim.c");
    println!("cargo:rerun-if-env-changed=LAKE");
    for key in [
        "LEAN",
        "LEAN_VERSION",
        "TOOLCHAIN",
        "PACKAGES",
        "SOURCE_SHA256",
        "CC",
        "AR",
    ] {
        println!("cargo:rerun-if-env-changed=DEP_DOGWOOD_LEAN_{key}");
    }
    #[cfg(feature = "lean")]
    shared::build();
}

#[cfg(feature = "lean")]
mod shared {
    use std::env;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::Command;

    /// The Lean version this crate's module is written for.
    const LEAN_VERSION: &str = "4.34.0";

    /// This crate's Lake package and library.
    const PACKAGE: &str = "DogwoodLeanDependent";
    const LIBRARY: &str = "DependentProbe";

    fn meta(key: &str) -> Option<String> {
        env::var(format!("DEP_DOGWOOD_LEAN_{key}")).ok()
    }

    pub fn build() {
        let manifest_dir = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").unwrap());
        let out_dir = PathBuf::from(env::var_os("OUT_DIR").unwrap());
        assert_eq!(
            meta("LEAN").as_deref(),
            Some("1"),
            "the language crate publishes no Lean library: its `lean-frontend` feature is off"
        );
        let version = meta("LEAN_VERSION").expect("DEP_DOGWOOD_LEAN_LEAN_VERSION");
        assert_eq!(
            version, LEAN_VERSION,
            "the library is built with Lean {version}"
        );
        let toolchain = PathBuf::from(meta("TOOLCHAIN").unwrap_or_default());
        // `$LAKE` may be a script that runs the toolchain's `lake` with the library path its
        // binaries need.
        let lake = env::var_os("LAKE")
            .map(PathBuf::from)
            .unwrap_or_else(|| toolchain.join("bin/lake"));
        assert!(
            toolchain.join("bin/lake").is_file(),
            "DEP_DOGWOOD_LEAN_TOOLCHAIN names no Lean toolchain ({}); a prebuilt language \
             crate publishes one only with LEAN_SYSROOT set",
            toolchain.display()
        );
        // The headers: `include/`, or `stage1/include/` for a toolchain installed from its
        // build tree.
        let include = ["include", "stage1/include"]
            .iter()
            .map(|d| toolchain.join(d))
            .find(|d| d.join("lean/lean.h").is_file())
            .unwrap_or_else(|| toolchain.join("include"));
        let packages: Vec<(String, PathBuf)> = meta("PACKAGES")
            .unwrap_or_default()
            .split(';')
            .filter(|p| !p.is_empty())
            .map(|p| {
                let (name, dir) = p.split_once('=').expect("PACKAGES: <name>=<dir>;…");
                (name.to_owned(), PathBuf::from(dir))
            })
            .collect();
        assert!(
            !packages.is_empty(),
            "DEP_DOGWOOD_LEAN_PACKAGES names no built Lean packages"
        );
        let digest = meta("SOURCE_SHA256").expect("DEP_DOGWOOD_LEAN_SOURCE_SHA256");
        println!("cargo:rustc-env=DOGWOOD_LEAN_COMPILED_AGAINST={digest}");

        // 1. The Lake project.
        let work = out_dir.join("lean");
        fs::create_dir_all(&work).unwrap();
        let mut lakefile = String::from("import Lake\nopen Lake DSL\n\n");
        let mut entries = Vec::new();
        for (name, dir) in &packages {
            lakefile.push_str(&format!("require {name} from \"{}\"\n", dir.display()));
            entries.push(format!(
                "{{\"type\": \"path\", \"scope\": \"\", \"name\": \"{name}\", \
                 \"manifestFile\": \"lake-manifest.json\", \"inherited\": false, \
                 \"dir\": \"{}\", \"configFile\": \"lakefile.lean\"}}",
                dir.display()
            ));
        }
        lakefile.push_str(&format!(
            "\npackage {PACKAGE} where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n\n\
             lean_lib {LIBRARY}\n"
        ));
        write(&work.join("lakefile.lean"), &lakefile);
        write(
            &work.join("lake-manifest.json"),
            &format!(
                "{{\"version\": \"1.1.0\", \"packagesDir\": \".lake/packages\", \"packages\": \
                 [{}], \"name\": \"{PACKAGE}\", \"lakeDir\": \".lake\"}}\n",
                entries.join(", ")
            ),
        );
        write(
            &work.join("lean-toolchain"),
            &format!("leanprover/lean4:v{LEAN_VERSION}\n"),
        );
        let module = format!("{LIBRARY}.lean");
        write(
            &work.join(&module),
            &fs::read_to_string(manifest_dir.join("lean").join(&module)).unwrap(),
        );

        // The language crate's C compiler and archiver for Lean's C (from source), else the
        // `cc` crate's: never the toolchain's bundled clang and `llvm-ar`, which some Linux
        // distributions' glibc cannot run.
        let mut cc = meta("CC")
            .map(PathBuf::from)
            .unwrap_or_else(|| cc::Build::new().get_compiler().path().to_owned());
        if meta("CC").is_none() && include != toolchain.join("include") {
            // Lake compiles the C with `-I <toolchain>/include`; the compiler also searches
            // where the headers are.
            let wrapper = out_dir.join("lean-cc");
            write(
                &wrapper,
                &format!(
                    "#!/bin/sh\nexec '{}' -I '{}' \"$@\"\n",
                    cc.display(),
                    include.display()
                ),
            );
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&wrapper, fs::Permissions::from_mode(0o755)).unwrap();
            cc = wrapper;
        }
        let ar = meta("AR")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from(cc::Build::new().get_archiver().get_program()));
        let lake_cmd = || {
            let mut c = Command::new(&lake);
            c.current_dir(&work).env("LEAN_CC", &cc).env("LEAN_AR", &ar);
            c
        };

        // 2. The library is up to date here: Lake builds nothing of it.
        let check = lake_cmd()
            .args(["build", "--no-build", "Dogwood.Frontend.Library"])
            .output()
            .unwrap();
        assert!(
            check.status.success(),
            "Lake does not find the language crate's Lean library up to date in this \
             workspace:\n{}{}",
            String::from_utf8_lossy(&check.stdout),
            String::from_utf8_lossy(&check.stderr)
        );

        // 3. This crate's module.
        let built = lake_cmd()
            .args(["build", &format!("{LIBRARY}:static")])
            .output()
            .unwrap();
        let log = format!(
            "{}{}",
            String::from_utf8_lossy(&built.stdout),
            String::from_utf8_lossy(&built.stderr)
        );
        assert!(built.status.success(), "lake build failed:\n{log}");
        for line in log.lines() {
            if let Some((_, what)) = line.split_once(" Built ") {
                assert!(
                    what.starts_with(LIBRARY) || what.starts_with(&format!("{PACKAGE}/")),
                    "Lake built a module of the library: {line}"
                );
            }
        }
        let lib_dir = work.join(".lake/build/lib");
        assert!(
            lib_dir.join(format!("lib{PACKAGE}_{LIBRARY}.a")).is_file(),
            "no archive in {}",
            lib_dir.display()
        );

        // 4. The shim, then the module's archive.
        cc::Build::new()
            .file(manifest_dir.join("src/shim.c"))
            .include(&include)
            .opt_level(2)
            .compile("dogwood_lean_dependent_shim");
        println!("cargo:rustc-link-search=native={}", lib_dir.display());
        println!("cargo:rustc-link-lib=static={PACKAGE}_{LIBRARY}");
    }

    fn write(path: &Path, text: &str) {
        if fs::read_to_string(path).ok().as_deref() != Some(text) {
            fs::write(path, text).unwrap();
        }
    }
}
