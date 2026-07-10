#![cfg(feature = "cli")]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

struct TestProject {
    root: PathBuf,
}

impl TestProject {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!(
            "xark-build-cache-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(root.join("src")).unwrap();

        let xark = Path::new(env!("CARGO_MANIFEST_DIR"));
        std::fs::write(
            root.join("Cargo.toml"),
            format!(
                "[package]\n\
                 name = \"cache-regression\"\n\
                 version = \"0.0.0\"\n\
                 edition = \"2021\"\n\n\
                 [lib]\n\
                 crate-type = [\"lib\"]\n\n\
                 [dependencies]\n\
                 xark = {{ path = {:?}, default-features = false }}\n",
                xark
            ),
        )
        .unwrap();
        std::fs::write(
            root.join("src/lib.rs"),
            "#![no_std]\n\
             use xark::prelude::*;\n\
             pub fn circuit(x: Private<Field>, out: Public<Field>) {\n\
                 assert_eq(x * x, out);\n\
             }\n",
        )
        .unwrap();
        Self { root }
    }

    fn build(&self) -> Output {
        Command::new(env!("CARGO_BIN_EXE_xark"))
            .args(["build", self.root.to_str().unwrap(), "--field", "bn254"])
            .output()
            .unwrap()
    }

    fn out(&self) -> PathBuf {
        self.root.join("target/xark/cache-regression")
    }
}

impl Drop for TestProject {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.root);
    }
}

fn assert_success(output: &Output) {
    assert!(
        output.status.success(),
        "xark build failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn build_cache_never_accepts_or_manufactures_stale_artifacts() {
    let project = TestProject::new();
    assert_success(&project.build());

    let source = project.root.join("src/lib.rs");
    let source_mtime = std::fs::metadata(&source).unwrap().modified().unwrap();
    let stamp = project.out().join(".xark-build-stamp");
    let fingerprint = std::fs::read_to_string(&stamp).unwrap();

    // A required side-effect disappearing must invalidate Cargo without changing
    // source metadata. The extractor recreates it after a package-scoped clean.
    std::fs::remove_file(project.out().join("r1cs.json")).unwrap();
    let regenerated = project.build();
    assert_success(&regenerated);
    assert!(project.out().join("r1cs.json").is_file());
    assert_eq!(
        std::fs::metadata(&source).unwrap().modified().unwrap(),
        source_mtime,
        "cache invalidation must not touch user sources"
    );
    assert_eq!(fingerprint, std::fs::read_to_string(&stamp).unwrap());

    // A complete, unchanged build can remain a Cargo cache hit.
    let cached = project.build();
    assert_success(&cached);
    assert_eq!(fingerprint, std::fs::read_to_string(&stamp).unwrap());

    // A failed Cargo invocation must win over artifacts left by the good build.
    std::fs::write(&source, "this is not valid Rust").unwrap();
    let broken = project.build();
    assert!(
        !broken.status.success(),
        "broken source must fail xark build"
    );
    assert!(
        String::from_utf8_lossy(&broken.stderr).contains("circuit compilation failed"),
        "expected Cargo failure diagnostic, got:\n{}",
        String::from_utf8_lossy(&broken.stderr)
    );
    assert!(
        project.out().join("r1cs.json").is_file(),
        "the previous good artifact may remain, but must not imply success"
    );
}
