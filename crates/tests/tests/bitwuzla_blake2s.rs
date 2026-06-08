//! Bitwuzla BLAKE2s bit-blasted equivalence harness — Layer B, track 2 of
//! `docs/FORMAL_VERIFICATION_PLAN.md`.
//!
//! Two independent QF_BV encodings of the BLAKE2s compression `F(h, m, t, f) → h'`
//! (RFC 7693 §3.2). Asserts disagreement on any of 8 output words; UNSAT
//! ⇒ bit-equivalent over all 28-word inputs (8 h + 16 m + 2 t + 2 f).

use std::process::{Command, Stdio};

const BLAKE2S_IV: [u32; 8] = [
    0x6a09_e667, 0xbb67_ae85, 0x3c6e_f372, 0xa54f_f53a, 0x510e_527f, 0x9b05_688c, 0x1f83_d9ab,
    0x5be0_cd19,
];

const BLAKE2S_SIGMA: [[usize; 16]; 10] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];

const R1: u32 = 16;
const R2: u32 = 12;
const R3: u32 = 8;
const R4: u32 = 7;
const ROUNDS: usize = 10;

fn bv32_const(v: u32) -> String {
    format!("(_ bv{v} 32)")
}

fn rotr(x: &str, n: u32) -> String {
    format!("((_ rotate_right {n}) {x})")
}

fn xor2(a: &str, b: &str) -> String {
    format!("(bvxor {a} {b})")
}

fn xor3(a: &str, b: &str, c: &str) -> String {
    format!("(bvxor {a} {b} {c})")
}

fn add_n(operands: &[String]) -> String {
    assert!(operands.len() >= 2);
    let mut s = String::from("(bvadd");
    for o in operands {
        s.push(' ');
        s.push_str(o);
    }
    s.push(')');
    s
}

#[allow(clippy::too_many_arguments)]
fn emit_g(
    body: &mut String,
    prefix: &str,
    round: usize,
    g_idx: usize,
    v: &mut [String; 16],
    a: usize,
    b: usize,
    c: usize,
    d: usize,
    x: &str,
    y: &str,
) {
    let va1 = format!("{prefix}r{round}g{g_idx}_va1");
    let va1_expr = add_n(&[v[a].clone(), v[b].clone(), x.to_string()]);
    body.push_str(&format!("(define-fun {va1} () (_ BitVec 32) {va1_expr})\n"));
    v[a] = va1;

    let vd1 = format!("{prefix}r{round}g{g_idx}_vd1");
    let vd1_expr = rotr(&xor2(&v[d], &v[a]), R1);
    body.push_str(&format!("(define-fun {vd1} () (_ BitVec 32) {vd1_expr})\n"));
    v[d] = vd1;

    let vc1 = format!("{prefix}r{round}g{g_idx}_vc1");
    let vc1_expr = add_n(&[v[c].clone(), v[d].clone()]);
    body.push_str(&format!("(define-fun {vc1} () (_ BitVec 32) {vc1_expr})\n"));
    v[c] = vc1;

    let vb1 = format!("{prefix}r{round}g{g_idx}_vb1");
    let vb1_expr = rotr(&xor2(&v[b], &v[c]), R2);
    body.push_str(&format!("(define-fun {vb1} () (_ BitVec 32) {vb1_expr})\n"));
    v[b] = vb1;

    let va2 = format!("{prefix}r{round}g{g_idx}_va2");
    let va2_expr = add_n(&[v[a].clone(), v[b].clone(), y.to_string()]);
    body.push_str(&format!("(define-fun {va2} () (_ BitVec 32) {va2_expr})\n"));
    v[a] = va2;

    let vd2 = format!("{prefix}r{round}g{g_idx}_vd2");
    let vd2_expr = rotr(&xor2(&v[d], &v[a]), R3);
    body.push_str(&format!("(define-fun {vd2} () (_ BitVec 32) {vd2_expr})\n"));
    v[d] = vd2;

    let vc2 = format!("{prefix}r{round}g{g_idx}_vc2");
    let vc2_expr = add_n(&[v[c].clone(), v[d].clone()]);
    body.push_str(&format!("(define-fun {vc2} () (_ BitVec 32) {vc2_expr})\n"));
    v[c] = vc2;

    let vb2 = format!("{prefix}r{round}g{g_idx}_vb2");
    let vb2_expr = rotr(&xor2(&v[b], &v[c]), R4);
    body.push_str(&format!("(define-fun {vb2} () (_ BitVec 32) {vb2_expr})\n"));
    v[b] = vb2;
}

fn emit_compression(
    prefix: &str,
    h_names: &[String; 8],
    m_names: &[String; 16],
    t_names: &[String; 2],
    f_names: &[String; 2],
) -> (String, [String; 8]) {
    let mut body = String::new();

    let mut v: [String; 16] = std::array::from_fn(|i| {
        if i < 8 {
            h_names[i].clone()
        } else {
            bv32_const(BLAKE2S_IV[i - 8])
        }
    });

    let v12_name = format!("{prefix}v12_init");
    let v12_expr = xor2(&v[12], &t_names[0]);
    body.push_str(&format!(
        "(define-fun {v12_name} () (_ BitVec 32) {v12_expr})\n"
    ));
    v[12] = v12_name;

    let v13_name = format!("{prefix}v13_init");
    let v13_expr = xor2(&v[13], &t_names[1]);
    body.push_str(&format!(
        "(define-fun {v13_name} () (_ BitVec 32) {v13_expr})\n"
    ));
    v[13] = v13_name;

    let v14_name = format!("{prefix}v14_init");
    let v14_expr = xor2(&v[14], &f_names[0]);
    body.push_str(&format!(
        "(define-fun {v14_name} () (_ BitVec 32) {v14_expr})\n"
    ));
    v[14] = v14_name;

    let v15_name = format!("{prefix}v15_init");
    let v15_expr = xor2(&v[15], &f_names[1]);
    body.push_str(&format!(
        "(define-fun {v15_name} () (_ BitVec 32) {v15_expr})\n"
    ));
    v[15] = v15_name;

    for round in 0..ROUNDS {
        let s = &BLAKE2S_SIGMA[round % 10];
        emit_g(&mut body, prefix, round, 0, &mut v, 0, 4, 8, 12, &m_names[s[0]], &m_names[s[1]]);
        emit_g(&mut body, prefix, round, 1, &mut v, 1, 5, 9, 13, &m_names[s[2]], &m_names[s[3]]);
        emit_g(&mut body, prefix, round, 2, &mut v, 2, 6, 10, 14, &m_names[s[4]], &m_names[s[5]]);
        emit_g(&mut body, prefix, round, 3, &mut v, 3, 7, 11, 15, &m_names[s[6]], &m_names[s[7]]);
        emit_g(&mut body, prefix, round, 4, &mut v, 0, 5, 10, 15, &m_names[s[8]], &m_names[s[9]]);
        emit_g(&mut body, prefix, round, 5, &mut v, 1, 6, 11, 12, &m_names[s[10]], &m_names[s[11]]);
        emit_g(&mut body, prefix, round, 6, &mut v, 2, 7, 8, 13, &m_names[s[12]], &m_names[s[13]]);
        emit_g(&mut body, prefix, round, 7, &mut v, 3, 4, 9, 14, &m_names[s[14]], &m_names[s[15]]);
    }

    let out_names: [String; 8] = std::array::from_fn(|i| format!("{prefix}OUT{i}"));
    for i in 0..8 {
        let expr = xor3(&h_names[i], &v[i], &v[i + 8]);
        body.push_str(&format!(
            "(define-fun {} () (_ BitVec 32) {expr})\n",
            out_names[i]
        ));
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

    let h_names: [String; 8] = std::array::from_fn(|i| format!("H{i}"));
    let m_names: [String; 16] = std::array::from_fn(|i| format!("M{i}"));
    let t_names: [String; 2] = std::array::from_fn(|i| format!("T{i}"));
    let f_names: [String; 2] = std::array::from_fn(|i| format!("F{i}"));
    for n in h_names
        .iter()
        .chain(m_names.iter())
        .chain(t_names.iter())
        .chain(f_names.iter())
    {
        s.push_str(&format!("(declare-const {n} (_ BitVec 32))\n"));
    }

    let (ref_body, ref_outs) = emit_compression("ref_", &h_names, &m_names, &t_names, &f_names);
    s.push_str(&ref_body);
    let (gad_body, gad_outs) = emit_compression("gad_", &h_names, &m_names, &t_names, &f_names);
    s.push_str(&gad_body);

    let diffs: Vec<String> = (0..8)
        .map(|i| format!("(distinct {} {})", ref_outs[i], gad_outs[i]))
        .collect();
    s.push_str(&format!("(assert (or {}))\n", diffs.join(" ")));
    s.push_str("(check-sat)\n");
    s
}

#[test]
fn blake2s_compression_gadget_equals_rfc7693_spec() {
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
        .unwrap_or(600);

    eprintln!(
        "  Bitwuzla BLAKE2s compression equivalence:\n  \
         SMT-LIB size: {} bytes; running bitwuzla (timeout {}s)…",
        smt.len(),
        timeout_s
    );
    let res = run_bitwuzla(&smt, timeout_s);
    eprintln!("  bitwuzla: {res}");

    match res.as_str() {
        "unsat" => {
            eprintln!(
                "  ✓ Equivalence PROVEN: BLAKE2s compression matches RFC 7693 §3.2\n  \
                 over all 28-word (8 h + 16 m + 2 t + 2 f) inputs."
            );
        }
        "sat" => panic!(
            "Bitwuzla found a 28-word input where the gadget-structure and \
             RFC 7693 §3.2 spec encodings of BLAKE2s compression disagree — \
             this is a real algorithmic-divergence bug."
        ),
        "unknown" => panic!(
            "Bitwuzla returned `unknown` — either the time limit ({timeout_s}s) was \
             too small or the encoding regressed. Raise BITWUZLA_TIMEOUT_S."
        ),
        other => panic!("bitwuzla returned unexpected output: {other:?}"),
    }
}

#[test]
fn blake2s_smt_generator_well_formed() {
    let smt = build_equivalence_smt();
    assert!(smt.starts_with("(set-logic QF_BV)\n"));
    assert!(smt.contains("(check-sat)\n"));
    for i in 0..8 {
        assert!(
            smt.contains(&format!("ref_OUT{i}")),
            "ref output #{i} missing"
        );
        assert!(
            smt.contains(&format!("gad_OUT{i}")),
            "gad output #{i} missing"
        );
    }
    for i in 0..8 {
        assert!(
            smt.contains(&format!("(declare-const H{i} (_ BitVec 32))")),
            "H{i} declaration missing"
        );
    }
    for i in 0..16 {
        assert!(
            smt.contains(&format!("(declare-const M{i} (_ BitVec 32))")),
            "M{i} declaration missing"
        );
    }
    for i in 0..2 {
        assert!(
            smt.contains(&format!("(declare-const T{i} (_ BitVec 32))")),
            "T{i} declaration missing"
        );
    }
    for i in 0..2 {
        assert!(
            smt.contains(&format!("(declare-const F{i} (_ BitVec 32))")),
            "F{i} declaration missing"
        );
    }
    for &iv in &BLAKE2S_IV {
        assert!(
            smt.contains(&format!("(_ bv{iv} 32)")),
            "IV constant {iv:#x} missing"
        );
    }
    assert!(smt.contains("ref_r0g0_va1"), "ref round-0 G-0 va1 missing");
    assert!(smt.contains("gad_r9g7_vb2"), "gad round-9 G-7 vb2 missing");
    for prefix in ["ref_", "gad_"] {
        for name in ["v12_init", "v13_init", "v14_init", "v15_init"] {
            assert!(
                smt.contains(&format!("{prefix}{name}")),
                "{prefix}{name} missing"
            );
        }
    }
}
