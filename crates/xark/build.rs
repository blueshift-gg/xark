//! Capture the toolchain the `xark` binary is built with, so the CLI can drive
//! `cargo`/the rustc-driver with the *same* nightly (sysroot + toolchain),
//! independent of the ambient toolchain where `xark build` is later run.
use std::process::Command;
fn main() {
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".into());
    if let Ok(out) = Command::new(&rustc).args(["--print", "sysroot"]).output() {
        if out.status.success() {
            let sysroot = String::from_utf8_lossy(&out.stdout).trim().to_string();
            let tc = std::path::Path::new(&sysroot)
                .file_name().and_then(|s| s.to_str()).unwrap_or("nightly").to_string();
            println!("cargo:rustc-env=XARK_SYSROOT={sysroot}");
            println!("cargo:rustc-env=XARK_TOOLCHAIN={tc}");
            // Bake the toolchain lib dir into the binary rpath so librustc_driver
            // loads at runtime without DYLD_LIBRARY_PATH / LD_LIBRARY_PATH.
            println!("cargo:rustc-link-arg-bins=-Wl,-rpath,{sysroot}/lib");
        }
    }
    println!("cargo:rerun-if-changed=build.rs");
}
