//! Dev tool: size of compiled circuits, for comparing builds.
//!
//! `cargo run -p xark-frontend --release --example xbcstat -- [--rows] <a.xbc> [<b.xbc> …]`
//!
//! One line per artifact: R1CS rows as built, rows and variables after the setup
//! minimizer (what Groth16 setup and proving pay for), and witness ops. `--rows`
//! prints only the row count (streamed, without expanding the circuit).

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let rows_only = args.iter().any(|a| a == "--rows");
    for path in args.iter().filter(|a| *a != "--rows") {
        let b = std::fs::read(path).unwrap_or_else(|e| panic!("reading {path}: {e}"));
        let rows = xark_ir::function_decode::stream_count_constraints(&b);
        if rows_only {
            println!("{rows}");
            continue;
        }
        let witness = xark_ir::function_decode::stream_count_witness(&b);
        let reduced = xark_ir::function_decode::expand_function_blob_reduced(&b)
            .unwrap_or_else(|e| panic!("expanding {path}: {e}"));
        println!(
            "{path} rows {rows} reduced_rows {} reduced_vars {} witness {witness}",
            reduced.constraints.len(),
            reduced.vars.len()
        );
    }
}
