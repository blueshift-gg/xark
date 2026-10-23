//! Dev tool: build a circuit crate with the stable frontend and fingerprint it.
//!
//! `cargo run -p xark-frontend --release --example stablec -- <crate-dir> [--compare other.xbc]
//! [--out circuit.xbc]` (`--out` keeps the built `circuit.xbc`, to compare against later).

use std::path::PathBuf;
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let dir = std::fs::canonicalize(&args[0]).expect("crate dir");
    let dir = if dir.is_file() {
        dir.parent().unwrap().to_path_buf()
    } else {
        dir
    };
    let compare = args
        .iter()
        .position(|a| a == "--compare")
        .map(|i| PathBuf::from(&args[i + 1]));
    // `XARK_WASM_TARGET_DIR`: a separate cargo target (e.g. one per toolchain).
    let target = std::env::var_os("XARK_WASM_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| dir.join("target/xark-wasm"));
    let t = Instant::now();
    let wasm = if args.iter().any(|a| a == "--wasm") {
        std::fs::read(&args[0]).unwrap()
    } else {
        xark_frontend::build_crate(&dir, &target).unwrap_or_else(|e| {
            eprintln!("error: {e}");
            std::process::exit(1)
        })
    };
    let t_build = t.elapsed();
    let t = Instant::now();
    let notes = std::env::var_os("XARK_NOTES").is_some();
    let out = xark_frontend::lower_module(&wasm, xark_ir::FieldSpec::named("bn254"), false, notes)
        .map(|l| l.output)
        .unwrap_or_else(|e| {
            eprintln!("error: {e}");
            std::process::exit(1)
        });
    let t_lower = t.elapsed();
    let xbc = &out.xbc;
    if let Some(path) = args
        .iter()
        .position(|a| a == "--out")
        .and_then(|i| args.get(i + 1))
    {
        std::fs::write(path, xbc).unwrap_or_else(|e| panic!("writing {path}: {e}"));
        println!("wrote {path}");
    }
    let digest = xark_ir::function_decode::stream_digest(xbc);
    // Faithfulness: the compact artifact must expand to exactly the flat lowering.
    match xark_ir::function_decode::verify_blob_matches(xbc, &out.r1cs, &out.primitive) {
        Ok((c, w, v)) => {
            println!("verify: artifact == flat lowering ({c} rows, {w} witness ops, {v} vars)")
        }
        Err(e) => println!("verify: MISMATCH: {e}"),
    }
    println!(
        "stable: {} vars, {} constraints, {} witness ops, xbc {} B, digest {digest:032x}  (cargo {:.2}s, lower {:.2}s, wasm {} B)",
        out.primitive.vars.len(),
        out.r1cs.constraints.len(),
        out.primitive.witness_gen.len(),
        xbc.len(),
        t_build.as_secs_f64(),
        t_lower.as_secs_f64(),
        wasm.len()
    );
    if std::env::var_os("XARK_STATS").is_some() {
        stats(&out.r1cs);
    }
    if let Some(other) = compare {
        let o = std::fs::read(&other).unwrap();
        let od = xark_ir::function_decode::stream_digest(&o);
        let n = xark_ir::function_decode::stream_count_constraints(&o);
        println!(
            "other : {n} constraints, digest {od:032x} → {}",
            if od == digest {
                "IDENTICAL"
            } else {
                "DIFFERENT"
            }
        );
        println!(
            "xbc bytes {}",
            if &o == xbc { "identical" } else { "differ" }
        );
    }
}

/// Rows / variables / nonzeros, before and after the setup minimizer, and repeated
/// multiplications (same `a`, `b` up to order).
fn stats(r: &xark_ir::R1csProgram) {
    let nnz = |r: &xark_ir::R1csProgram| -> usize {
        r.constraints
            .iter()
            .map(|c| c.a.terms.len() + c.b.terms.len() + c.c.terms.len())
            .sum()
    };
    let used = |r: &xark_ir::R1csProgram| -> usize {
        let mut s = std::collections::HashSet::new();
        for c in &r.constraints {
            for l in [&c.a, &c.b, &c.c] {
                for t in &l.terms {
                    s.insert(t.var);
                }
            }
        }
        s.len()
    };
    let mut seen = std::collections::HashMap::new();
    let mut dup = 0usize;
    for c in &r.constraints {
        if c.a.is_constant() || c.b.is_constant() {
            continue;
        }
        let (x, y) = (format!("{:?}", c.a), format!("{:?}", c.b));
        let k = if x < y { (x, y) } else { (y, x) };
        if seen.insert(k, ()).is_some() {
            dup += 1;
        }
    }
    println!(
        "stats: rows {} vars {} nnz {} repeated-mul {}",
        r.constraints.len(),
        used(r),
        nnz(r),
        dup
    );
    let t = std::time::Instant::now();
    let m = xark_ir::minimize::minimize(r);
    println!(
        "stats: minimized rows {} vars {} nnz {} ({:.2}s)",
        m.constraints.len(),
        used(&m),
        nnz(&m),
        t.elapsed().as_secs_f64()
    );
}
