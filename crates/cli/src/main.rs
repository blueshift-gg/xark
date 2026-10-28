//! `xark`: the user-facing toolchain CLI (`xark build|setup|prove|verify|…`).
//!
//! Uses mimalloc to parallelize circuit loading without allocator contention.

// mimalloc: circuit loading makes millions of small `Vec<Term>` allocations that
// the system allocator serializes across rayon threads.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

mod cli;
mod commands;
mod style;
mod xark_project;

fn main() {
    // A bare `xark` shows the roadmap; otherwise clap owns the process (it calls
    // `std::process::exit` on error / for completions, and re-reads argv itself).
    if std::env::args().len() == 1 {
        print_roadmap();
        return;
    }
    commands::main();
}

/// The zero-to-on-chain roadmap, shown when `xark` is run with no arguments.
fn print_roadmap() {
    let steps: &[(&str, &str)] = &[
        ("xark doctor", "check your toolchain is set up"),
        (
            "xark init my-circuit",
            "scaffold a circuit crate (rust-analyzer ready)",
        ),
        ("xark build .", "compile the circuit → R1CS (+ schema.json)"),
        (
            "xark client .",
            "generate a typed TypeScript client (prove + verify in JS)",
        ),
        ("xark setup .", "generate the proving/verifying keys"),
        (
            "xark prove . --inputs …",
            "produce (and self-check) a proof",
        ),
        ("xark verify .", "verify a proof locally"),
        (
            "xark export .",
            "generate the on-chain Solana verifier crate",
        ),
    ];
    // Align by display columns, not bytes (some commands contain `…`).
    let width = steps
        .iter()
        .map(|(c, _)| c.chars().count())
        .max()
        .unwrap_or(0);
    println!(
        "{}",
        style::brand("xark — write, prove & verify zero-knowledge circuits in Rust")
    );
    println!("\nThe path from zero to an on-chain proof:\n");
    for (cmd, hint) in steps {
        println!(
            "  {}{}   {}",
            style::brand(cmd),
            " ".repeat(width.saturating_sub(cmd.chars().count())),
            style::dim(hint),
        );
    }
    println!(
        "\n{}",
        style::dim(
            "Run `xark <command> --help` for details, or `xark doctor` to check your setup."
        )
    );
}
