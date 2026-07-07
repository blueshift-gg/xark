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

            // Guardrail: if built against the FLOATING `nightly` channel (dir name
            // `nightly-<target>`, no date) rather than the pinned `nightly-YYYY-MM-DD`,
            // the baked rpath points at a rolling dir that `rustup update` will move
            // out from under the binary — causing a `dyld: librustc_driver … not
            // loaded` failure later. Warn loudly and say how to fix it.
            let floating = tc
                .strip_prefix("nightly-")
                .is_some_and(|rest| !rest.starts_with(|c: char| c.is_ascii_digit()));
            if floating {
                println!(
                    "cargo:warning=xark built against the FLOATING `nightly` toolchain \
                     ({tc}); its librustc_driver rpath will break on `rustup update`. \
                     Install with the pinned toolchain instead: \
                     `cargo +nightly-2026-05-03 install --path crates/xark --features cli` \
                     (or run the install from within `crates/xark/`)."
                );
            }
        }
    }
    println!("cargo:rerun-if-changed=build.rs");
}
