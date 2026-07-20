//! Gated harness that regenerates every committed Groth16 fixture under
//! `crates/tests/fixtures/groth16/<name>/` from a **faithful xark-native**
//! circuit built with the real gadget.
//!
//! Every fixture is xark-native end to end: gadget fixtures compile the corresponding
//! `examples/<gadget>` crate (real SHA-256, AES-128, Keccak, BLAKE2s/3,
//! Poseidon2, secp256k1 EC ops); ECDSA and the arithmetic/logic fixtures compile
//! purpose-built crates under `crates/tests/examples/<name>`.
//!
//! For each fixture we build a full, satisfying witness (the solver derives the
//! internal witness; public *outputs* are recovered from their binding
//! constraints, and any genuine public/private *inputs* are supplied from a
//! known-answer test map), then run real Groth16 setup + prove and assert the
//! proof verifies before writing the four `.bin` files.
//!
//! Run explicitly (`#[ignore]`d and env-gated). Use `--release`:
//!
//! ```bash
//! REGEN_FIXTURES=1 cargo test -p xark-tests --release \
//!     --test regen_fixtures -- --ignored --nocapture
//! ```

mod common;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use ark_bn254::{Bn254, Fr};
use ark_ff::{Field as _, Zero};
use ark_groth16::Groth16;
use ark_snark::SNARK;

use xark_backend::solana::{
    assemble_proof_bytes_le, assemble_public_inputs_bytes_le, assemble_vk_bytes_le,
};
use xark_backend::Groth16Keys;
use xark_ir::linear_combination::LinearCombination as IrLc;
use xark_ir::{primitive, solver, R1csProgram, VarId, Visibility};
use xark_prover::{fr_from_decimal, XarkCircuit};

/// secp256k1 ECDSA known-answer vector, generated with `k256`. The GLV
/// `ecdsa_verify` takes each 256-bit value as two 128-bit halves `[lo, hi]`
/// (10 public inputs) — see `xark_secp256k1::Fq4`.
const ECDSA_K1_KAT: &[(&str, &str)] = &[
    (
        "pubkey.x.limbs[0]",
        "117299088799582250395560111034933314319",
    ),
    (
        "pubkey.x.limbs[1]",
        "259440519671684123545587916950343488600",
    ),
    (
        "pubkey.y.limbs[0]",
        "197533179544423103898009492159805902490",
    ),
    (
        "pubkey.y.limbs[1]",
        "113291300625110951570919122229184586675",
    ),
    ("sig.r.limbs[0]", "315003556148935348562556824676081698499"),
    ("sig.r.limbs[1]", "305224178580023842502765843531985788795"),
    ("sig.s.limbs[0]", "34739722103927784686836260377017762291"),
    ("sig.s.limbs[1]", "26859405002682767357449321938879885918"),
    ("digest.limbs[0]", "156129739268667827118276520739168643892"),
    ("digest.limbs[1]", "308604824281941425083684239850222646004"),
];

/// secp256r1 (P-256) ECDSA known-answer vector, generated with `p256` and
/// verified off-circuit (`R.x mod n == r`). Compact **2×128-bit half** public form
/// (10 public inputs) — the repack of the earlier 3×86 vector; same signature.
const ECDSA_R1_KAT: &[(&str, &str)] = &[
    (
        "pubkey.x.limbs[0]",
        "155980732500594415992756698020363615685",
    ),
    (
        "pubkey.x.limbs[1]",
        "145220944681788350899783423254568517605",
    ),
    (
        "pubkey.y.limbs[0]",
        "38871051169009026178808143761631908797",
    ),
    (
        "pubkey.y.limbs[1]",
        "268881656657284688356269048913849994543",
    ),
    ("sig.r.limbs[0]", "118329509033871567403237738633297129333"),
    ("sig.r.limbs[1]", "115294649709585341303850469457176801846"),
    ("sig.s.limbs[0]", "142917374223568687255232207162823887626"),
    ("sig.s.limbs[1]", "274892915219377031903631266034741673399"),
    ("digest.limbs[0]", "156129739268667827118276520739168643892"),
    ("digest.limbs[1]", "308604824281941425083684239850222646004"),
];

/// secp256k1 generator `G` (2G / 3G KAT private inputs) as 3×86-bit limbs — the
/// private inputs of `examples/ec_incomplete` (public outputs are derived).
/// Copied from the `ec_incomplete_matches_vectors` snapshot test.
const EC_INCOMPLETE_G: &[(&str, &str)] = &[
    ("g.x.limbs[0]", "17117865558768631194064792"),
    ("g.x.limbs[1]", "12501176021340589225372855"),
    ("g.x.limbs[2]", "9198697782662356105779718"),
    ("g.y.limbs[0]", "6441780312434748884571320"),
    ("g.y.limbs[1]", "57953919405111227542741658"),
    ("g.y.limbs[2]", "5457536640262350763842127"),
];

/// The public outputs of `examples/ec_incomplete` for the `G` above: `2G`
/// (`d*`) and `3G` (`f*`) as 3×86-bit limbs. These output limbs appear in
/// several constraints (range checks + the incomplete-add checks), so they are
/// supplied from the verified `ec_incomplete_matches_vectors` snapshot vector
/// rather than recovered from a single binding constraint.
const EC_INCOMPLETE_OUT: &[(&str, &str)] = &[
    ("two_g.x.limbs[0]", "57105948487393027623526117"),
    ("two_g.x.limbs[1]", "2088890992725950981549619"),
    ("two_g.x.limbs[2]", "14961784698075395646489684"),
    ("two_g.y.limbs[0]", "46925586441427271765976362"),
    ("two_g.y.limbs[1]", "19820246243853867596485833"),
    ("two_g.y.limbs[2]", "2031033786214458435714136"),
    ("three_g.x.limbs[0]", "57545291876987742944507641"),
    ("three_g.x.limbs[1]", "75066192660561802595210765"),
    ("three_g.x.limbs[2]", "18828234277447069677687620"),
    ("three_g.y.limbs[0]", "2583640362791394057184882"),
    ("three_g.y.limbs[1]", "38197615293098406611150035"),
    ("three_g.y.limbs[2]", "4273588397735691711217203"),
];

/// A fixture spec: name, public-input count `N`, where the circuit crate lives,
/// and the known-answer inputs.
struct Spec {
    name: &'static str,
    n: usize,
    /// Crate directory (relative to the tests-crate manifest dir).
    crate_dir: PathBuf,
    /// Private inputs by variable name (every `PrivateInput` var must appear).
    private: BTreeMap<String, String>,
    /// Public inputs that are *genuine inputs* (supplied, not derived). Every
    /// other public var is a circuit *output*, recovered from its constraint.
    public_in: BTreeMap<String, String>,
}

fn manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn map(pairs: &[(&str, &str)]) -> BTreeMap<String, String> {
    pairs
        .iter()
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .collect()
}

/// A gadget fixture built from an out-of-workspace `examples/<gadget>` crate.
fn example_dir(gadget: &str) -> PathBuf {
    manifest_dir()
        .join("..")
        .join("..")
        .join("examples")
        .join(gadget)
}

/// An authored fixture crate under `crates/tests/examples/<name>`.
fn local_dir(name: &str) -> PathBuf {
    manifest_dir().join("../../examples").join(name)
}

/// Build the per-fixture spec (source crate + KAT inputs). Private inputs to the
/// hash gadgets are arbitrary (any in-range value works — the digest is derived);
/// EC/ECDSA inputs come from real, off-circuit-verified vectors.
fn specs() -> Vec<Spec> {
    // Helper: build flattened array-param private maps
    // (`["p[0]".."p[{n-1}]"] = start, start+1, ...`).
    let arr = |prefix: &str, n: usize, start: u64| -> BTreeMap<String, String> {
        (0..n)
            .map(|i| (format!("{prefix}[{i}]"), (start + i as u64).to_string()))
            .collect()
    };

    let mut v: Vec<Spec> = Vec::new();

    // ---- Arithmetic / logic fixtures (authored, faithful) ----
    v.push(Spec {
        name: "arithmetic_square",
        n: 1,
        crate_dir: local_dir("arithmetic_square"),
        private: map(&[("x", "3")]),
        public_in: BTreeMap::new(),
    }); // y = 9 (derived)
    v.push(Spec {
        name: "arithmetic_public_inputs",
        n: 1,
        crate_dir: local_dir("arithmetic_public_inputs"),
        private: map(&[("x", "2"), ("y", "3")]),
        public_in: BTreeMap::new(),
    }); // out = 11
    v.push(Spec {
        name: "bitwise_basic",
        n: 2,
        crate_dir: local_dir("bitwise_basic"),
        private: map(&[("a", "4042322160"), ("b", "252645135")]),
        public_in: BTreeMap::new(),
    }); // 0xF0F0F0F0 & 0x0F0F0F0F
    v.push(Spec {
        name: "range_basic",
        n: 1,
        crate_dir: local_dir("range_basic"),
        private: map(&[("x", "200")]),
        public_in: BTreeMap::new(),
    }); // out = 200
    v.push(Spec {
        name: "reorder_pi",
        n: 2,
        crate_dir: local_dir("reorder_pi"),
        private: map(&[("b", "4")]),
        public_in: map(&[("a", "7"), ("c", "9")]),
    }); // b*b = 16 = 7+9
    v.push(Spec {
        name: "mixed_pi",
        n: 2,
        crate_dir: local_dir("mixed_pi"),
        private: map(&[("x", "2")]),
        public_in: map(&[("y", "3")]),
    }); // ret = 2*3+2 = 8
    v.push(Spec {
        name: "return_values_only",
        n: 1,
        crate_dir: local_dir("return_values_only"),
        private: map(&[("x", "4")]),
        public_in: BTreeMap::new(),
    }); // ret = 16
    v.push(Spec {
        name: "large_pi",
        n: 16,
        crate_dir: local_dir("large_pi"),
        private: BTreeMap::new(),
        public_in: {
            // x0 + x15 = 30, total = 44.
            let mut m = BTreeMap::new();
            m.insert("x0".to_string(), "10".to_string());
            m.insert("x15".to_string(), "20".to_string());
            for i in 1..15 {
                m.insert(format!("x{i}"), "1".to_string());
            }
            m
        },
    });
    v.push(Spec {
        name: "memory_const",
        n: 1,
        crate_dir: local_dir("memory_const"),
        private: map(&[("x", "5")]),
        public_in: BTreeMap::new(),
    }); // y = 6*5 = 30
    v.push(Spec {
        name: "memory_var",
        n: 1,
        crate_dir: local_dir("memory_var"),
        private: map(&[
            ("arr0", "10"),
            ("arr1", "20"),
            ("arr2", "30"),
            ("arr3", "40"),
            ("sel0", "0"),
            ("sel1", "0"),
            ("sel2", "1"),
            ("sel3", "0"),
        ]),
        public_in: BTreeMap::new(),
    }); // y = arr2 = 30
    v.push(Spec {
        name: "multi_function",
        n: 1,
        crate_dir: local_dir("multi_function"),
        private: map(&[("x", "6")]),
        public_in: BTreeMap::new(),
    }); // y = 36
    v.push(Spec {
        name: "nested_calls",
        n: 1,
        crate_dir: local_dir("nested_calls"),
        private: map(&[("x", "6")]),
        public_in: BTreeMap::new(),
    }); // y = 6*6 + 1 = 37

    // ---- Gadget fixtures (real gadgets, from examples/) ----
    // Hash gadgets: arbitrary private message words; public digest is derived.
    v.push(Spec {
        name: "sha256_basic",
        n: 8,
        crate_dir: example_dir("sha256"),
        private: map(&[("m[0]", "1"), ("m[1]", "2")]),
        public_in: BTreeMap::new(),
    });
    v.push(Spec {
        name: "aes128_basic",
        n: 16,
        crate_dir: example_dir("aes"),
        private: {
            let mut m = arr("pt", 16, 0);
            m.extend(arr("key", 16, 16));
            m
        },
        public_in: BTreeMap::new(),
    });
    v.push(Spec {
        name: "keccak_basic",
        n: 4,
        crate_dir: example_dir("keccak"),
        private: arr("words", 17, 1),
        public_in: BTreeMap::new(),
    });
    v.push(Spec {
        name: "blake2s_basic",
        n: 9,
        crate_dir: example_dir("blake2s"),
        private: arr("m", 16, 1),
        public_in: map(&[("len", "64")]),
    });
    v.push(Spec {
        name: "blake3_basic",
        n: 9,
        crate_dir: example_dir("blake3"),
        private: arr("m", 16, 1),
        public_in: map(&[("len", "64")]),
    });
    v.push(Spec {
        name: "poseidon_basic",
        n: 3,
        crate_dir: example_dir("poseidon2"),
        private: map(&[("in0", "1"), ("in1", "2"), ("in2", "3")]),
        public_in: BTreeMap::new(),
    });

    // secp256k1 EC 2G/3G: private generator limbs; public 2G/3G outputs derived.
    v.push(Spec {
        name: "curve_basic",
        n: 12,
        crate_dir: example_dir("ec_incomplete"),
        private: map(EC_INCOMPLETE_G),
        public_in: map(EC_INCOMPLETE_OUT),
    });

    // ECDSA: a ZK proof that a public signature verifies — the public key `q`,
    // signature `(r, s)`, and message scalar `e` are all public. The GLV gadget
    // packs each 256-bit value into two 128-bit halves → 10 public inputs.
    v.push(Spec {
        name: "secp256k1_ecdsa",
        n: 10,
        crate_dir: local_dir("secp256k1_ecdsa"),
        private: BTreeMap::new(),
        public_in: map(ECDSA_K1_KAT),
    });
    v.push(Spec {
        name: "secp256r1_ecdsa",
        n: 10,
        crate_dir: local_dir("secp256r1_ecdsa"),
        private: BTreeMap::new(),
        public_in: map(ECDSA_R1_KAT),
    });

    v
}

/// The xark toolchain binary (rustc-driver `xark build`). Build it if absent.
fn xark_toolchain_bin() -> PathBuf {
    let xark_crate = manifest_dir().join("..").join("xark");
    for profile in ["release", "debug"] {
        let p = xark_crate.join("target").join(profile).join("xark");
        if p.exists() {
            return p;
        }
    }
    let status = Command::new("cargo")
        .args(["build", "--release", "--features", "cli", "--bin", "xark"])
        .current_dir(&xark_crate)
        .status()
        .expect("build xark toolchain");
    assert!(
        status.success(),
        "failed to build the xark toolchain binary"
    );
    xark_crate.join("target").join("release").join("xark")
}

/// Compile a circuit crate to `<out>/{r1cs,circuit}.json` via `xark build`.
fn build_circuit(spec: &Spec, out: &Path) {
    assert!(
        spec.crate_dir.join("Cargo.toml").exists(),
        "missing circuit crate {}",
        spec.crate_dir.display()
    );
    let target = out.join("cargo-target");
    let status = Command::new(xark_toolchain_bin())
        .arg("build")
        .arg(&spec.crate_dir)
        .arg("--out")
        .arg(out)
        // This regenerates the committed JSON fixtures, so it needs `circuit.json`
        // (a normal `xark build` writes only `circuit.xbc`).
        .arg("--emit-json")
        .env("CARGO_TARGET_DIR", &target)
        .status()
        .expect("spawn xark build");
    assert!(status.success(), "xark build failed for {}", spec.name);
    assert!(
        out.join("circuit.json").exists() && out.join("r1cs.json").exists(),
        "xark build produced no JSON for {}",
        spec.name
    );
}

/// Deterministic Groth16 setup for fixture generation.
///
/// Uses arkworks' native `circuit_specific_setup` (field-FFT + MSM) rather than
/// xark's ptau-based `setup_from_ptau`. The ptau path derives its Lagrange-basis
/// points via an O(n log n) FFT over *group* elements — millions of G2 scalar-muls
/// for a 2^21 domain — which made a large-circuit regen take ~30 minutes. A fixture
/// only needs a valid, self-consistent `(pk, vk)` for the on-chain verifier tests,
/// which this produces in a fraction of the time. The production `setup_from_ptau`
/// path stays covered by the dedicated small-circuit ceremony / ptau tests.
///
/// `test_rng` is deterministic, so regenerated fixtures remain reproducible.
fn setup(r1cs: &R1csProgram) -> Groth16Keys {
    // `for_setup_preminimized` (NOT `for_setup`): `r1cs` is already minimized by the
    // caller, and setup must synthesize the exact same circuit `for_proving_preminimized`
    // does — `for_setup`'s internal `maybe_minimize` would re-reduce it under a
    // different (unguarded) policy and desync the proving key from the proof.
    let mut rng = xark_backend::test_rng();
    let (proving_key, verifying_key) = Groth16::<Bn254>::circuit_specific_setup(
        XarkCircuit::for_setup_preminimized(r1cs.clone()),
        &mut rng,
    )
    .expect("circuit_specific_setup");
    Groth16Keys {
        proving_key,
        verifying_key,
    }
}

/// Evaluate an R1CS linear combination in `Fr` against the current assignment
/// (missing vars treated as zero).
fn eval_lc(lc: &IrLc, assign: &BTreeMap<VarId, Fr>) -> Fr {
    let mut acc = fr_from_decimal(&lc.constant.decimal());
    for t in &lc.terms {
        acc += fr_from_decimal(&t.coeff.decimal())
            * assign.get(&t.var).copied().unwrap_or_else(Fr::zero);
    }
    acc
}

/// Coefficient of variable `p` in an LC (zero if absent).
fn coeff_of(lc: &IrLc, p: VarId) -> Fr {
    lc.terms
        .iter()
        .find(|t| t.var == p)
        .map(|t| fr_from_decimal(&t.coeff.decimal()))
        .unwrap_or_else(Fr::zero)
}

/// Recover the value of a public *output* variable from its (unique) binding
/// constraint `A·B = C`. `p` must appear linearly in exactly one of A, B, C, and
/// every other variable in that constraint must already be assigned.
fn derive_public(r1cs: &R1csProgram, assign: &BTreeMap<VarId, Fr>, p: VarId, name: &str) -> Fr {
    for con in &r1cs.constraints {
        let alpha = coeff_of(&con.a, p);
        let beta = coeff_of(&con.b, p);
        let gamma = coeff_of(&con.c, p);
        if alpha.is_zero() && beta.is_zero() && gamma.is_zero() {
            continue;
        }
        assert!(
            !(alpha != Fr::zero() && beta != Fr::zero()),
            "public output `{name}` appears quadratically in constraint {}",
            con.id
        );
        // With p currently 0 in `assign`, these are A0, B0, C0.
        let a0 = eval_lc(&con.a, assign);
        let b0 = eval_lc(&con.b, assign);
        let c0 = eval_lc(&con.c, assign);
        // (A0+αp)(B0+βp) = C0+γp, with αβ=0  ⇒  p·(αB0 + βA0 − γ) = C0 − A0·B0.
        let denom = alpha * b0 + beta * a0 - gamma;
        assert!(
            !denom.is_zero(),
            "public output `{name}` is unconstrained in constraint {}",
            con.id
        );
        return (c0 - a0 * b0) * denom.inverse().unwrap();
    }
    panic!("no binding constraint found for public output `{name}`");
}

fn regen_one(spec: &Spec, work: &Path) {
    eprintln!("regen `{}` (N={})", spec.name, spec.n);
    let gendir = work.join(spec.name);
    std::fs::create_dir_all(&gendir).unwrap();
    build_circuit(spec, &gendir);

    // Load the circuit from the compact `circuit.xbc` (the per-template-reduced form
    // the prover uses), NOT the multi-GB flat `r1cs.json` — parsing that dominated
    // the runtime and memory. `expand_function_blob` yields both the primitive and
    // the R1CS from one decode, with consistent var ids.
    let xbc = std::fs::read(gendir.join("circuit.xbc")).expect("read circuit.xbc");
    let t = std::time::Instant::now();
    let cp = xark_ir::function_decode::expand_function_blob(&xbc).expect("expand circuit.xbc");
    let prim = cp.to_primitive();
    let r1cs = cp.to_r1cs();
    eprintln!(
        "  [timing] expand xbc: {:.1}s ({} constraints, {} witness-gen ops)",
        t.elapsed().as_secs_f64(),
        r1cs.constraints.len(),
        prim.witness_gen.len()
    );

    // Seed the solver inputs: every public/private var. Supplied inputs get their
    // KAT value; public *outputs* get a placeholder 0 (they never feed the hint
    // program, so the derived witness is unaffected) and are recovered afterwards.
    let mut id_inputs: BTreeMap<VarId, String> = BTreeMap::new();
    for var in &prim.vars {
        match var.role {
            primitive::VarRole::PrivateInput => {
                let val = spec.private.get(&var.name).unwrap_or_else(|| {
                    panic!("missing private input `{}` for `{}`", var.name, spec.name)
                });
                id_inputs.insert(var.id, val.clone());
            }
            primitive::VarRole::PublicInput => {
                let val = spec
                    .public_in
                    .get(&var.name)
                    .cloned()
                    .unwrap_or_else(|| "0".to_string());
                id_inputs.insert(var.id, val);
            }
            primitive::VarRole::Derived => {}
        }
    }

    let t = std::time::Instant::now();
    let assign_fp = solver::solve(&prim, &id_inputs).expect("solve witness");
    eprintln!("  [timing] solve: {:.1}s", t.elapsed().as_secs_f64());
    // `Fp::Bn254` already wraps the arkworks `Fr` — take it directly instead of a
    // per-var `num_bigint` decimal round-trip (`to_decimal` → parse), which was
    // single-threaded over ~1.6M vars.
    let mut assign: BTreeMap<VarId, Fr> = assign_fp
        .iter()
        .map(|(k, v)| (*k, v.as_bn254_fr().expect("bn254 field element")))
        .collect();

    // Recover public outputs (public vars not supplied as genuine inputs).
    let t = std::time::Instant::now();
    for v in &r1cs.variables {
        if v.visibility == Visibility::Public && !spec.public_in.contains_key(&v.name) {
            let val = derive_public(&r1cs, &assign, v.id, &v.name);
            assign.insert(v.id, val);
        }
    }
    eprintln!(
        "  [timing] derive_public: {:.1}s",
        t.elapsed().as_secs_f64()
    );

    // Minimize the flat R1CS to the form the real prover uses, so setup AND prove
    // run over the SAME minimized circuit. The regen previously set up Groth16 over
    // the full un-minimized flat expansion (millions of extra rows), which made
    // `circuit_specific_setup` pathologically slow. `minimize` preserves var ids, so
    // the witness `assign` (over every var) still maps.
    let t = std::time::Instant::now();
    let nz = |p: &R1csProgram| -> usize {
        p.constraints
            .iter()
            .map(|c| c.a.terms.len() + c.b.terms.len() + c.c.terms.len())
            .sum()
    };
    let raw_nz = nz(&r1cs);
    // `minimize` is the guarded default (fill cap `MAX_FILL_DEFAULT`) — the SAME pass
    // production's `maybe_minimize` runs, so the fixture matches what `xark prove`
    // produces. The low cap keeps the circuit at raw sparsity (the prover's real cost
    // is nonzeros, not constraints), and never OOMs on the large flat circuits.
    let r1cs = xark_ir::minimize::minimize(&r1cs);
    eprintln!(
        "  [timing] minimize: {:.1}s ({} constraints, {} nonzeros, raw was {})",
        t.elapsed().as_secs_f64(),
        r1cs.constraints.len(),
        nz(&r1cs),
        raw_nz,
    );

    let t = std::time::Instant::now();
    let keys = setup(&r1cs);
    eprintln!("  [timing] setup: {:.1}s", t.elapsed().as_secs_f64());

    let circ = XarkCircuit::for_proving_preminimized(r1cs.clone(), assign);
    let pi = circ.public_inputs();
    assert_eq!(
        pi.len(),
        spec.n,
        "circuit `{}` produced {} public inputs, expected {}",
        spec.name,
        pi.len(),
        spec.n
    );

    let mut rng = xark_backend::test_rng();
    let t = std::time::Instant::now();
    let proof = Groth16::<Bn254>::prove(&keys.proving_key, circ, &mut rng).expect("prove");
    eprintln!("  [timing] prove: {:.1}s", t.elapsed().as_secs_f64());
    assert!(
        xark_backend::verify(&keys.verifying_key, &proof, &pi).expect("verify"),
        "regenerated `{}` proof failed to verify before writing",
        spec.name
    );

    let vk_bytes = assemble_vk_bytes_le(&keys.verifying_key);
    let proof_bytes = assemble_proof_bytes_le(&proof);
    let pi_bytes = assemble_public_inputs_bytes_le(&pi);
    let mut ix = proof_bytes.clone();
    ix.extend_from_slice(&pi_bytes);

    let dir = manifest_dir()
        .join("fixtures")
        .join("groth16")
        .join(spec.name);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("verifying_key.solana.bin"), &vk_bytes).unwrap();
    std::fs::write(dir.join("proof.solana.bin"), &proof_bytes).unwrap();
    std::fs::write(dir.join("public_inputs.solana.bin"), &pi_bytes).unwrap();
    std::fs::write(dir.join("instruction_data.bin"), &ix).unwrap();
    eprintln!(
        "  wrote {} (vk {} B, proof {} B, pi {} B)",
        dir.display(),
        vk_bytes.len(),
        proof_bytes.len(),
        pi_bytes.len()
    );
}

#[test]
#[ignore = "fixture regeneration; run explicitly with REGEN_FIXTURES=1"]
fn regenerate_all_groth16_fixtures() {
    if std::env::var("REGEN_FIXTURES").as_deref() != Ok("1") {
        eprintln!("set REGEN_FIXTURES=1 to run; skipping");
        return;
    }
    let work = manifest_dir().join("target").join("regen-work");
    std::fs::create_dir_all(&work).unwrap();

    // Optional filter: REGEN_ONLY=<name>[,<name>...].
    let only: Option<Vec<String>> = std::env::var("REGEN_ONLY")
        .ok()
        .map(|s| s.split(',').map(|x| x.trim().to_string()).collect());
    for spec in specs() {
        if let Some(list) = &only {
            if !list.iter().any(|n| n == spec.name) {
                continue;
            }
        }
        regen_one(&spec, &work);
    }
    eprintln!("done");
}
