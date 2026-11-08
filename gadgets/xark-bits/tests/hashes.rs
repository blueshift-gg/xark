//! The hash gadgets end to end: compile a circuit, solve it, check it.
//!
//! * `xor3`, `maj3`, `chi`, `ch` (one row each): on every bit input, exactly one
//!   output is accepted, by exhaustive witness search over BN254 and over every
//!   value of a small field (bug checklist 8, the hinted-bit class); the same
//!   function built from pairwise XOR/AND/NOT rows accepts exactly the same
//!   (inputs, output) pairs, honest and mutated (12); each derived variable of an
//!   accepted witness, tampered alone, is rejected (7).
//! * `reduce::<N>`: at the width's edges it returns the low 32 bits, rejects
//!   `sum ≥ 2^N` (and `r − 1`) where a full `to_bits::<N>` twin does, and has no
//!   free or forgeable variable; `N > 253` doesn't compile (9).
//! * SHA-256, Keccak-256, BLAKE2s, BLAKE3 against the `sha2`, `sha3`, `blake2`,
//!   `blake3` crates: empty, short, block-boundary and multi-block messages; a wrong
//!   digest and a byte ≥ 256 are rejected (10: bytes are range-checked before use);
//!   no variable is free and sampled derived variables can't be tampered (7, 8).

use std::collections::BTreeMap;

use num_bigint::BigUint;
use xark_ir::primitive::{PrimitiveProgram, VarRole};
use xark_ir::solver;
use xark_ir::witness_search::{WitnessSearch, search_witnesses};

const BN254_R: &str =
    "21888242871839275222246405745257275088548364400416034343698204186575808495617";

fn compile(name: &str, field: &str, body: &str) -> PrimitiveProgram {
    let src = format!("#![no_std]\nuse xark::prelude::*;\n{body}");
    let c = xark_test_harness::compile_source(name, &src, field);
    assert!(c.status_success, "{name}: {}", c.stderr);
    c.program()
}

/// Input values by name (`x`, or `x[i]` for an array) → var id.
fn inputs(p: &PrimitiveProgram, vals: &[(String, String)]) -> BTreeMap<u32, String> {
    vals.iter()
        .map(|(n, v)| {
            let var = p.vars.iter().find(|x| x.name == *n);
            (
                var.unwrap_or_else(|| panic!("no input `{n}`")).id,
                v.clone(),
            )
        })
        .collect()
}

fn named(prefix: &str, vals: &[String]) -> Vec<(String, String)> {
    vals.iter()
        .enumerate()
        .map(|(i, v)| (format!("{prefix}[{i}]"), v.clone()))
        .collect()
}

/// Exhaustive witness search: exactly one witness (`true`) or none (`false`).
fn unique_or_none(p: &PrimitiveProgram, ins: &BTreeMap<u32, String>) -> bool {
    match search_witnesses(p, ins, 1 << 14).unwrap() {
        WitnessSearch::Unique(_) => true,
        WitnessSearch::None => false,
        other => panic!("{ins:?}: {other:?}"),
    }
}

/// The honest witness for `ins` is accepted, no variable is free, and each derived
/// variable a row reads (all of them, or `samples` spread evenly over the circuit),
/// bumped by one, breaks some row.
/// `constant`: the circuit computes a constant (an empty message's hash), so it has
/// no derived variable.
fn accepts_and_rejects_forgeries(
    p: &PrimitiveProgram,
    ins: &BTreeMap<u32, String>,
    samples: Option<usize>,
    constant: bool,
) {
    let assign = solver::solve_and_check(p, ins).unwrap_or_else(|e| panic!("{e:?}"));
    let holes = solver::analyze_underconstrained(p, &assign);
    assert!(holes.is_empty(), "under-constrained {holes:?}");
    let read: std::collections::BTreeSet<u32> = p
        .constraints
        .iter()
        .flat_map(|e| {
            let muls = e.mul_terms.iter().flat_map(|t| [t.left, t.right]);
            muls.chain(e.linear_terms.iter().map(|t| t.var))
                .collect::<Vec<_>>()
        })
        .collect();
    let derived: Vec<_> = p
        .vars
        .iter()
        .filter(|v| v.role == VarRole::Derived && read.contains(&v.id))
        .collect();
    assert_eq!(derived.is_empty(), constant, "derived variables");
    let step = samples.map_or(1, |n| derived.len().div_ceil(n).max(1));
    for v in derived.iter().step_by(step) {
        let mut bad = assign.clone();
        let x: BigUint = assign[&v.id].to_decimal().parse().unwrap();
        bad.insert(v.id, solver::fp_from_decimal(&(x + 1u8).to_string(), p));
        assert!(
            solver::check(p, &bad).is_err(),
            "tampering {} still satisfies every row",
            v.name
        );
    }
}

// ---------------------------------------------------------------------------
// The single-row bit gadgets
// ---------------------------------------------------------------------------

/// (gadget, the same function from pairwise rows, the spec on bits)
type BitGadget = (&'static str, &'static str, fn(u8, u8, u8) -> u8);

const GADGETS: [BitGadget; 4] = [
    ("xark_bits::xor3(a, b, c)", "a.xor(b).xor(c)", |a, b, c| {
        a ^ b ^ c
    }),
    (
        "xark_bits::maj3(a, b, c)",
        "a.and(b).xor(a.and(c)).xor(b.and(c))",
        |a, b, c| (a & b) | (a & c) | (b & c),
    ),
    (
        "xark_bits::chi(a, b, c)",
        "a.xor(b.not().and(c))",
        |a, b, c| a ^ ((1 - b) & c),
    ),
    (
        "xark_bits::ch(a, b, c)",
        "a.and(b).xor(a.not().and(c))",
        |a, b, c| if a == 1 { b } else { c },
    ),
];

fn bit_circuit(expr: &str) -> String {
    format!(
        "#[circuit]\npub fn circuit(a: Private<Field>, b: Private<Field>, c: Private<Field>, \
         out: Public<Field>) {{\n\
         \x20   a.require_bool();\n    b.require_bool();\n    c.require_bool();\n\
         \x20   require_eq({expr}, out);\n}}\n"
    )
}

fn abc(a: u8, b: u8, c: u8, out: String) -> Vec<(String, String)> {
    vec![
        ("a".into(), a.to_string()),
        ("b".into(), b.to_string()),
        ("c".into(), c.to_string()),
        ("out".into(), out),
    ]
}

/// On each bit input, the one-row gadget accepts exactly the spec's output (BN254),
/// as its pairwise twin does, also for outputs `2` and `r − 1`; the honest witness
/// has no forgeable variable.
#[test]
fn single_row_bit_gadgets_accept_exactly_their_bit() {
    let minus_one = (BN254_R.parse::<BigUint>().unwrap() - 1u8).to_string();
    for (i, (gadget, pairwise, spec)) in GADGETS.iter().enumerate() {
        let one = compile(&format!("bitgadget_{i}"), "bn254", &bit_circuit(gadget));
        let twin = compile(
            &format!("bitgadget_twin_{i}"),
            "bn254",
            &bit_circuit(pairwise),
        );
        for a in 0..2u8 {
            for b in 0..2u8 {
                for c in 0..2u8 {
                    let want = spec(a, b, c);
                    for out in ["0", "1", "2", minus_one.as_str()] {
                        let ok = out == want.to_string();
                        let v = abc(a, b, c, out.into());
                        let what = format!("{gadget} on ({a}, {b}, {c}) = {out}");
                        assert_eq!(unique_or_none(&one, &inputs(&one, &v)), ok, "{what}");
                        assert_eq!(unique_or_none(&twin, &inputs(&twin, &v)), ok, "twin {what}");
                    }
                    let v = abc(a, b, c, want.to_string());
                    accepts_and_rejects_forgeries(&one, &inputs(&one, &v), None, false);
                }
            }
        }
    }
}

/// Over the field of 97 elements (the rows' multipliers ±1…±4 are nonzero mod any
/// p > 24), every one of the 97 output values is tried on each bit input: exactly
/// the spec's is accepted.
#[test]
fn single_row_bit_gadgets_are_unique_over_a_small_field() {
    for (i, (gadget, _, spec)) in GADGETS.iter().enumerate() {
        let p = compile(&format!("bitgadget97_{i}"), "97", &bit_circuit(gadget));
        for a in 0..2u8 {
            for b in 0..2u8 {
                for c in 0..2u8 {
                    let accepted: Vec<u32> = (0..97u32)
                        .filter(|out| {
                            unique_or_none(&p, &inputs(&p, &abc(a, b, c, out.to_string())))
                        })
                        .collect();
                    let want = vec![u32::from(spec(a, b, c))];
                    assert_eq!(accepted, want, "{gadget} on ({a}, {b}, {c}) mod 97");
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// reduce::<N>
// ---------------------------------------------------------------------------

fn reduce_circuit(n: usize, full: bool) -> String {
    // The twin: a full `to_bits::<N>` decomposition, keeping the low 32 bits.
    let body = if full {
        format!(
            "let bits = sum.to_bits::<{n}>();\n    let mut acc = Field::zero();\n    \
                 let mut p = Field::one();\n    for i in 0..32 {{ acc = acc + bits[i] * p; p = p + p; }}\n    \
                 require_eq(acc, out);"
        )
    } else {
        format!("require_eq(Field::from_bits::<32>(xark_bits::reduce::<{n}>(sum)), out);")
    };
    format!(
        "#[circuit]\npub fn circuit(sum: Private<Field>, out: Public<Field>) {{\n    {body}\n}}\n"
    )
}

/// At each production width, `reduce` returns the low 32 bits of every sum below
/// `2^N` (0, 1, 2³² − 1, 2³², 2^(N−1) ± 1, 2^N − 1) and rejects 2^N, 2^N + 2^(N−1)
/// and r − 1, exactly as the full decomposition does; a wrong low word is rejected,
/// and no variable is free or forgeable.
#[test]
fn reduce_is_exact_at_each_width() {
    let r: BigUint = BN254_R.parse().unwrap();
    let low = |v: &BigUint| (v % (BigUint::from(1u8) << 32u32)).to_string();
    for n in [33usize, 34, 35, 36] {
        let p = compile(&format!("reduce_{n}"), "bn254", &reduce_circuit(n, false));
        let twin = compile(
            &format!("reduce_twin_{n}"),
            "bn254",
            &reduce_circuit(n, true),
        );
        let top = BigUint::from(1u8) << (n as u32 - 1);
        let all = BigUint::from(1u8) << n as u32;
        let fits = [
            BigUint::from(0u8),
            BigUint::from(1u8),
            (BigUint::from(1u8) << 32u32) - 1u8,
            BigUint::from(1u8) << 32u32,
            &top - 1u8,
            top.clone(),
            &top + 1u8,
            &all - 1u8,
        ];
        let solves = |p: &PrimitiveProgram, sum: &BigUint, out: String| {
            let v = [
                ("sum".to_string(), sum.to_string()),
                ("out".to_string(), out),
            ];
            solver::solve_and_check(p, &inputs(p, &v)).is_ok()
        };
        for s in &fits {
            assert!(solves(&p, s, low(s)), "reduce::<{n}>({s})");
            assert!(solves(&twin, s, low(s)), "twin reduce::<{n}>({s})");
            let wrong = ((s + 1u8) % (BigUint::from(1u8) << 32u32)).to_string();
            assert!(
                !solves(&p, s, wrong.clone()),
                "reduce::<{n}>({s}) ≠ {wrong}"
            );
            let v = [
                ("sum".to_string(), s.to_string()),
                ("out".to_string(), low(s)),
            ];
            accepts_and_rejects_forgeries(&p, &inputs(&p, &v), None, false);
        }
        for s in [all.clone(), &all + &top, &r - 1u8] {
            assert!(
                !solves(&p, &s, low(&s)),
                "reduce::<{n}>({s}) must be rejected"
            );
            assert!(
                !solves(&twin, &s, low(&s)),
                "twin reduce::<{n}>({s}) must be rejected"
            );
        }
    }
}

/// `reduce::<254>` would let the sum wrap mod r (bug checklist 3, 9), and
/// `reduce::<32>` would leave no carry bit: neither compiles.
#[test]
fn reduce_rejects_widths_outside_33_to_253() {
    for n in [32usize, 254] {
        let src = format!(
            "#![no_std]\nuse xark::prelude::*;\n{}",
            reduce_circuit(n, false)
        );
        let c = xark_test_harness::compile_source(&format!("reduce_bad_{n}"), &src, "bn254");
        assert!(!c.status_success, "reduce::<{n}> compiled");
        assert!(c.stderr.contains("33 <= N <= 253"), "{}", c.stderr);
    }
}

// ---------------------------------------------------------------------------
// The hashes against reference crates
// ---------------------------------------------------------------------------

/// A deterministic message of `len` bytes.
fn message(len: usize) -> Vec<u8> {
    (0..len).map(|i| (i * 131 + 7) as u8).collect()
}

/// `hash::<L>(msg)` with the digest's words (`bits`-bit, `words` of them) bound to
/// the public `d`.
fn hash_circuit(call: &str, len: usize, words: usize, bits: usize) -> String {
    format!(
        "#[circuit]\npub fn circuit(msg: Private<[Field; {len}]>, d: Public<[Field; {words}]>) {{\n\
         \x20   let h = {call}::<{len}>(msg);\n\
         \x20   for i in 0..{words} {{\n\
         \x20       let mut acc = Field::zero();\n\
         \x20       let mut p = Field::one();\n\
         \x20       for j in 0..{bits} {{ acc = acc + h[i][j] * p; p = p + p; }}\n\
         \x20       require_eq(acc, d[i]);\n\
         \x20   }}\n}}\n"
    )
}

/// Each length's circuit accepts the reference digest, rejects it with one word
/// changed and with a message byte of 256, and has no free or (sampled) forgeable
/// variable.
fn check_hash(
    name: &str,
    call: &str,
    lens: &[usize],
    words: usize,
    bits: usize,
    reference: fn(&[u8]) -> Vec<u8>,
) {
    // Each length is its own circuit and search: one thread per length.
    std::thread::scope(|scope| {
        for &len in lens {
            scope.spawn(move || {
                let p = compile(
                    &format!("{name}_{len}"),
                    "bn254",
                    &hash_circuit(call, len, words, bits),
                );
                let msg = message(len);
                let digest = reference(&msg);
                let bytes = bits / 8;
                let word = |i: usize| -> String {
                    let w = &digest[i * bytes..(i + 1) * bytes];
                    // SHA-256's words are big-endian, the others little-endian.
                    if name == "sha256" {
                        BigUint::from_bytes_be(w).to_string()
                    } else {
                        BigUint::from_bytes_le(w).to_string()
                    }
                };
                let d: Vec<String> = (0..words).map(word).collect();
                let m: Vec<String> = msg.iter().map(u8::to_string).collect();
                let vals = |m: &[String], d: &[String]| {
                    let mut v = named("msg", m);
                    v.extend(named("d", d));
                    inputs(&p, &v)
                };
                let what = format!("{name}({len} bytes)");
                solver::solve_and_check(&p, &vals(&m, &d))
                    .unwrap_or_else(|e| panic!("{what}: {e:?}"));
                let mut bad = d.clone();
                bad[words - 1] =
                    (word(words - 1).parse::<BigUint>().unwrap() ^ BigUint::from(1u8)).to_string();
                assert!(
                    solver::solve_and_check(&p, &vals(&m, &bad)).is_err(),
                    "{what}: wrong digest accepted"
                );
                if len > 0 {
                    let mut wide = m.clone();
                    wide[0] = (u32::from(msg[0]) + 256).to_string();
                    assert!(
                        solver::solve_and_check(&p, &vals(&wide, &d)).is_err(),
                        "{what}: byte ≥ 256 accepted"
                    );
                }
                accepts_and_rejects_forgeries(&p, &vals(&m, &d), Some(64), len == 0);
            });
        }
    });
}

#[test]
fn sha256_matches_sha2() {
    use sha2::Digest;
    // Empty, one block, the last one-block length (55), the first two-block (56), a
    // full block, two full blocks' worth (119), and four blocks (247).
    check_hash(
        "sha256",
        "xark_sha256::sha256",
        &[0, 3, 55, 56, 64, 119, 247],
        8,
        32,
        |m| sha2::Sha256::digest(m).to_vec(),
    );
}

#[test]
fn keccak256_matches_sha3() {
    use sha3::Digest;
    // Empty, short, the last one-block length (135), a full rate block (136: two
    // permutations), and three blocks.
    check_hash(
        "keccak256",
        "xark_keccak::keccak256",
        &[0, 3, 135, 136, 300],
        4,
        64,
        |m| sha3::Keccak256::digest(m).to_vec(),
    );
}

#[test]
fn blake2s_matches_blake2() {
    use blake2::Digest;
    check_hash(
        "blake2s",
        "xark_blake2s::blake2s",
        &[0, 3, 64, 65, 200],
        8,
        32,
        |m| blake2::Blake2s256::digest(m).to_vec(),
    );
}

#[test]
fn blake3_matches_blake3() {
    check_hash(
        "blake3",
        "xark_blake3::blake3",
        &[0, 3, 64, 65, 200],
        8,
        32,
        |m| blake3::hash(m).as_bytes().to_vec(),
    );
}
