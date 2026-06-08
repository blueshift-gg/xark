//! Bitwuzla Keccak-f[1600] bit-blasted equivalence harness — Layer B,
//! track 2 of `docs/FORMAL_VERIFICATION_PLAN.md`.
//!
//! Two independent QF_BV encodings of the FIPS 202 §3.2 Keccak-f[1600]
//! permutation (24 rounds, 5×5×64-bit state): a clean spec (`ref_`,
//! chained-binary θ + gather ρ+π + commuted χ) and an encoding mirroring
//! `crates/acir-r1cs/src/gadgets/keccak.rs::keccakf1600_in_circuit`
//! step-by-step (`gad_`, n-ary `xor_n_inputs` θ + scatter ρ+π + `(NOT
//! B[x+1]) AND B[x+2]` χ). Asserts disagreement on any of 25 output lanes
//! and feeds to Bitwuzla. UNSAT ⇒ bit-equivalent over all 1600-bit inputs.

use std::process::{Command, Stdio};

const KECCAK_LANES: usize = 25;
const KECCAK_ROUNDS: usize = 24;

const KECCAKF_RC: [u64; KECCAK_ROUNDS] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

const ROTATION_OFFSETS: [[u32; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];

fn bv64_const(v: u64) -> String {
    format!("(_ bv{v} 64)")
}

fn rotl(x: &str, n: u32) -> String {
    format!("((_ rotate_left {n}) {x})")
}

fn xor2(a: &str, b: &str) -> String {
    format!("(bvxor {a} {b})")
}

fn xor_n(operands: &[String]) -> String {
    assert!(operands.len() >= 2);
    let mut s = String::from("(bvxor");
    for o in operands {
        s.push(' ');
        s.push_str(o);
    }
    s.push(')');
    s
}

fn and(a: &str, b: &str) -> String {
    format!("(bvand {a} {b})")
}

fn not(a: &str) -> String {
    format!("(bvnot {a})")
}

#[derive(Clone, Copy)]
struct Style {
    n_ary_theta: bool,
    scatter_pi: bool,
    chi_and_lhs_not: bool,
}

const GAD_STYLE: Style = Style {
    n_ary_theta: true,
    scatter_pi: true,
    chi_and_lhs_not: true,
};

const REF_STYLE: Style = Style {
    n_ary_theta: false,
    scatter_pi: false,
    chi_and_lhs_not: false,
};

fn emit_permutation(
    prefix: &str,
    style: Style,
    input_names: &[String; KECCAK_LANES],
) -> (String, [String; KECCAK_LANES]) {
    let mut body = String::new();

    let mut lanes: Vec<String> = input_names.iter().cloned().collect();

    for round in 0..KECCAK_ROUNDS {
        // θ
        let mut c_names: Vec<String> = Vec::with_capacity(5);
        for x in 0..5 {
            let cols: [String; 5] = [
                lanes[x].clone(),
                lanes[x + 5].clone(),
                lanes[x + 10].clone(),
                lanes[x + 15].clone(),
                lanes[x + 20].clone(),
            ];
            let expr = if style.n_ary_theta {
                xor_n(&cols)
            } else {
                let mut acc = xor2(&cols[0], &cols[1]);
                acc = xor2(&acc, &cols[2]);
                acc = xor2(&acc, &cols[3]);
                acc = xor2(&acc, &cols[4]);
                acc
            };
            let name = format!("{prefix}C_r{round}_x{x}");
            body.push_str(&format!("(define-fun {name} () (_ BitVec 64) {expr})\n"));
            c_names.push(name);
        }
        let mut d_names: Vec<String> = Vec::with_capacity(5);
        for x in 0..5 {
            let left = &c_names[(x + 4) % 5];
            let right_rot = rotl(&c_names[(x + 1) % 5], 1);
            let expr = xor2(left, &right_rot);
            let name = format!("{prefix}D_r{round}_x{x}");
            body.push_str(&format!("(define-fun {name} () (_ BitVec 64) {expr})\n"));
            d_names.push(name);
        }
        let mut theta_out: Vec<String> = Vec::with_capacity(KECCAK_LANES);
        for y in 0..5 {
            for x in 0..5 {
                let idx = x + 5 * y;
                let expr = xor2(&lanes[idx], &d_names[x]);
                let name = format!("{prefix}T_r{round}_x{x}_y{y}");
                body.push_str(&format!("(define-fun {name} () (_ BitVec 64) {expr})\n"));
                theta_out.push(name);
            }
        }

        // ρ + π
        let mut b_names: Vec<String> = vec![String::new(); KECCAK_LANES];
        if style.scatter_pi {
            for y in 0..5 {
                for x in 0..5 {
                    let nx = y;
                    let ny = (2 * x + 3 * y) % 5;
                    let src = &theta_out[x + 5 * y];
                    let r = ROTATION_OFFSETS[x][y];
                    let expr = rotl(src, r);
                    let name = format!("{prefix}B_r{round}_x{nx}_y{ny}");
                    body.push_str(&format!(
                        "(define-fun {name} () (_ BitVec 64) {expr})\n"
                    ));
                    b_names[nx + 5 * ny] = name;
                }
            }
        } else {
            for big_y in 0..5 {
                for big_x in 0..5 {
                    let x = (big_x + 3 * big_y) % 5;
                    let y = big_x;
                    let src = &theta_out[x + 5 * y];
                    let r = ROTATION_OFFSETS[x][y];
                    let expr = rotl(src, r);
                    let name = format!("{prefix}B_r{round}_x{big_x}_y{big_y}");
                    body.push_str(&format!(
                        "(define-fun {name} () (_ BitVec 64) {expr})\n"
                    ));
                    b_names[big_x + 5 * big_y] = name;
                }
            }
        }

        // χ
        let mut chi_out: Vec<String> = Vec::with_capacity(KECCAK_LANES);
        for y in 0..5 {
            for x in 0..5 {
                let b_self = &b_names[x + 5 * y];
                let b_plus1 = &b_names[((x + 1) % 5) + 5 * y];
                let b_plus2 = &b_names[((x + 2) % 5) + 5 * y];
                let nb = not(b_plus1);
                let and_expr = if style.chi_and_lhs_not {
                    and(&nb, b_plus2)
                } else {
                    and(b_plus2, &nb)
                };
                let expr = xor2(b_self, &and_expr);
                let name = format!("{prefix}X_r{round}_x{x}_y{y}");
                body.push_str(&format!("(define-fun {name} () (_ BitVec 64) {expr})\n"));
                chi_out.push(name);
            }
        }

        // ι
        let rc = bv64_const(KECCAKF_RC[round]);
        let iota_expr = xor2(&chi_out[0], &rc);
        let iota_name = format!("{prefix}I_r{round}");
        body.push_str(&format!(
            "(define-fun {iota_name} () (_ BitVec 64) {iota_expr})\n"
        ));

        let mut next_lanes: Vec<String> = chi_out.clone();
        next_lanes[0] = iota_name;
        lanes = next_lanes;
    }

    let mut out_names: [String; KECCAK_LANES] = std::array::from_fn(|_| String::new());
    for y in 0..5 {
        for x in 0..5 {
            let idx = x + 5 * y;
            let name = format!("{prefix}OUT_{x}_{y}");
            body.push_str(&format!(
                "(define-fun {name} () (_ BitVec 64) {})\n",
                lanes[idx]
            ));
            out_names[idx] = name;
        }
    }

    (body, out_names)
}

fn bitwuzla_bin() -> String {
    std::env::var("BITWUZLA_BIN").unwrap_or_else(|_| "bitwuzla".to_string())
}

fn bitwuzla_available() -> bool {
    Command::new(bitwuzla_bin())
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

fn run_bitwuzla(smt: &str, timeout_s: u64) -> String {
    use std::io::Write;
    let mut child = Command::new(bitwuzla_bin())
        .arg("-t")
        .arg((timeout_s * 1000).to_string())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn bitwuzla");
    {
        let stdin = child.stdin.as_mut().expect("stdin");
        stdin.write_all(smt.as_bytes()).expect("write smt");
    }
    let out = child.wait_with_output().expect("wait bitwuzla");
    let s = String::from_utf8_lossy(&out.stdout);
    s.lines().next().unwrap_or("(no output)").trim().to_string()
}

fn build_equivalence_smt() -> String {
    let mut s = String::new();
    s.push_str("(set-logic QF_BV)\n");

    let mut input_names: [String; KECCAK_LANES] = std::array::from_fn(|_| String::new());
    for y in 0..5 {
        for x in 0..5 {
            let idx = x + 5 * y;
            let n = format!("S{x}_{y}");
            s.push_str(&format!("(declare-const {n} (_ BitVec 64))\n"));
            input_names[idx] = n;
        }
    }

    let (ref_body, ref_outs) = emit_permutation("ref_", REF_STYLE, &input_names);
    s.push_str(&ref_body);
    let (gad_body, gad_outs) = emit_permutation("gad_", GAD_STYLE, &input_names);
    s.push_str(&gad_body);

    let diffs: Vec<String> = (0..KECCAK_LANES)
        .map(|i| format!("(distinct {} {})", ref_outs[i], gad_outs[i]))
        .collect();
    s.push_str(&format!("(assert (or {}))\n", diffs.join(" ")));
    s.push_str("(check-sat)\n");
    s
}

#[test]
fn keccak_f1600_gadget_equals_fips_spec() {
    if !bitwuzla_available() && std::env::var_os("XARK_RUN_BITWUZLA").is_none() {
        eprintln!(
            "bitwuzla: not on PATH and XARK_RUN_BITWUZLA not set — skipping.\n  \
             Install bitwuzla (https://bitwuzla.github.io/docs/install.html) to run \
             this Layer-B equivalence proof."
        );
        return;
    }

    let smt = build_equivalence_smt();
    let timeout_s: u64 = std::env::var("BITWUZLA_TIMEOUT_S")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(900);

    eprintln!(
        "  Bitwuzla Keccak-f[1600] permutation equivalence:\n  \
         SMT-LIB size: {} bytes; running bitwuzla (timeout {}s)…",
        smt.len(),
        timeout_s
    );
    let res = run_bitwuzla(&smt, timeout_s);
    eprintln!("  bitwuzla: {res}");

    match res.as_str() {
        "unsat" => {
            eprintln!(
                "  ✓ Equivalence PROVEN: the gadget-structure encoding of\n  \
                 Keccak-f[1600] equals the FIPS 202 §3.2 spec encoding over\n  \
                 all 1600-bit inputs."
            );
        }
        "sat" => panic!(
            "Bitwuzla found a 1600-bit input where the gadget-structure and \
             FIPS-spec encodings of Keccak-f[1600] disagree — this is a real \
             algorithmic-divergence bug. Investigate `crates/acir-r1cs/\
             src/gadgets/keccak.rs` vs FIPS 202 §3.2."
        ),
        "unknown" => panic!(
            "Bitwuzla returned `unknown` — either the time limit ({timeout_s}s) was \
             too small or the encoding regressed in solver-friendliness. Raise \
             BITWUZLA_TIMEOUT_S or investigate."
        ),
        other => panic!("bitwuzla returned unexpected output: {other:?}"),
    }
}

#[test]
fn keccak_smt_generator_well_formed() {
    let smt = build_equivalence_smt();
    assert!(smt.starts_with("(set-logic QF_BV)\n"));
    assert!(smt.contains("(check-sat)\n"));
    for y in 0..5 {
        for x in 0..5 {
            assert!(
                smt.contains(&format!("ref_OUT_{x}_{y}")),
                "ref output ({x},{y}) missing"
            );
            assert!(
                smt.contains(&format!("gad_OUT_{x}_{y}")),
                "gad output ({x},{y}) missing"
            );
        }
    }
    for y in 0..5 {
        for x in 0..5 {
            assert!(
                smt.contains(&format!("(declare-const S{x}_{y} (_ BitVec 64))")),
                "S{x}_{y} declaration missing"
            );
        }
    }
    for &rc in &KECCAKF_RC {
        assert!(
            smt.contains(&format!("(_ bv{rc} 64)")),
            "RC {rc:#x} missing from SMT body"
        );
    }
    for round in 0..KECCAK_ROUNDS {
        assert!(
            smt.contains(&format!("ref_C_r{round}_x0")),
            "ref θ C[0] for round {round} missing"
        );
        assert!(
            smt.contains(&format!("gad_C_r{round}_x0")),
            "gad θ C[0] for round {round} missing"
        );
        assert!(
            smt.contains(&format!("ref_I_r{round}")),
            "ref ι for round {round} missing"
        );
        assert!(
            smt.contains(&format!("gad_I_r{round}")),
            "gad ι for round {round} missing"
        );
    }
}
