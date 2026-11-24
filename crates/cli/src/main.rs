//! `xark`: the user-facing toolchain CLI.

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() {
    xark_cli::entrypoint();
}
