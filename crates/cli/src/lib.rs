//! `xark`: the user-facing circuit toolchain and Groth16 prover commands.

mod cli;
pub mod commands;
mod style;
mod xark_project;

/// Run the regular `xark` command-line interface.
pub fn entrypoint() {
    if std::env::args().len() == 1 {
        print_roadmap();
    } else {
        commands::main();
    }
}

/// Print the getting-started path when the CLI is invoked without arguments.
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
    let width = steps
        .iter()
        .map(|(command, _)| command.chars().count())
        .max()
        .unwrap_or(0);
    println!(
        "{}",
        style::brand("xark — write, prove & verify zero-knowledge circuits in Rust")
    );
    println!("\nThe path from zero to an on-chain proof:\n");
    for (command, hint) in steps {
        println!(
            "  {}{}   {}",
            style::brand(command),
            " ".repeat(width.saturating_sub(command.chars().count())),
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
