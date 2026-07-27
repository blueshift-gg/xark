//! Verify the `grumpkin_ipa` deferred-MSM accumulator circuit against an
//! independent `ark-grumpkin` reference vector (`Q = Σⱼ sⱼ·Gⱼ`, full-width
//! ~253-bit scalars split into 127-bit limbs). Confirms: (1) the emitted R1CS is
//! satisfiable on the honest vector, (2) it is analyzer-clean (no forgeable
//! derived vars), (3) a wrong claimed `Q` is rejected, and (4) reports the
//! minimized constraint count — the efficiency evidence.

use std::collections::BTreeMap;
use std::path::Path;
use xark_ir::{primitive, solver};

fn src() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("src/lib.rs")
}

fn load() -> primitive::PrimitiveProgram {
    let c = xark_test_harness::compile_file(&src(), "grumpkin_ipa", "bn254");
    assert!(c.status_success, "compiling grumpkin_ipa failed:\n{}", c.stderr);
    c.program()
}

// --- ark-grumpkin reference vector (validated: same routine reproduces the
//     gadget's corr₁₂₈ exactly). Q = Σⱼ sⱼ·Gⱼ, sⱼ = loⱼ + hiⱼ·2^127. ---
const G0X: &str = "3078034153852398078128400807926804309327113743808504829582559963737223069694";
const G0Y: &str = "12696890884641142049456609402511852099066095483298083855939691685001536962732";
const S0LO: &str = "60084397167073555162083361513403522487";
const S0HI: &str = "36088648481254637903101376313178913327";
const G1X: &str = "18660890509582237958343981571981920822503400000196279471655180441138020044621";
const G1Y: &str = "8902249110305491597038405103722863701255802573786510474664632793109847672620";
const S1LO: &str = "97605276812866110489057805785336271852";
const S1HI: &str = "69103295295569534943010654047256774201";
const G2X: &str = "763947558912359675602353050994051190166418588022888764656343140671310115434";
const G2Y: &str = "1244893704640049169462398469384866579396698880516857177429128873187668729859";
const S2LO: &str = "44598705996698807541652267929952945441";
const S2HI: &str = "4463001242034982868263207590522768002";
const G3X: &str = "12229279139087521908560794489267966517139449915173592433539394009359081620359";
const G3Y: &str = "12096995292699515952722386974733884667125946823386040531322131902193094989869";
const S3LO: &str = "167338704812101959590156073396584628054";
const S3HI: &str = "35439497807825386909150426018507431884";
const QX: &str = "20903080311600324333489123549926276227734645934862144969632742816704833802883";
const QY: &str = "21415318633544108147494823273278274647092448118324172091757610792088028377648";

fn honest_inputs(program: &primitive::PrimitiveProgram) -> BTreeMap<u32, String> {
    let id = |name: &str| {
        program
            .vars
            .iter()
            .find(|v| v.name == name)
            .unwrap_or_else(|| panic!("missing circuit var `{name}`"))
            .id
    };
    let mut m = BTreeMap::new();
    for (n, v) in [
        ("g0.x", G0X), ("g0.y", G0Y), ("g1.x", G1X), ("g1.y", G1Y),
        ("g2.x", G2X), ("g2.y", G2Y), ("g3.x", G3X), ("g3.y", G3Y),
        ("s0_lo", S0LO), ("s0_hi", S0HI), ("s1_lo", S1LO), ("s1_hi", S1HI),
        ("s2_lo", S2LO), ("s2_hi", S2HI), ("s3_lo", S3LO), ("s3_hi", S3HI),
        ("q.x", QX), ("q.y", QY),
    ] {
        m.insert(id(n), v.to_string());
    }
    m
}

#[test]
fn deferred_msm_accumulator_verifies() {
    let program = load();
    let mut inputs = honest_inputs(&program);

    // (1) satisfiable on the honest vector.
    let assign = solver::solve_and_check(&program, &inputs)
        .expect("grumpkin_ipa must verify on the reference accumulator vector");

    // (2) analyzer-clean: no under-constrained (forgeable) derived variables.
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(holes.is_empty(), "under-constrained: {holes:?}");

    // (3) a wrong claimed accumulated point is rejected.
    let qx_id = program.vars.iter().find(|v| v.name == "q.x").unwrap().id;
    inputs.insert(qx_id, "123".to_string());
    assert!(
        solver::solve_and_check(&program, &inputs).is_err(),
        "a wrong claimed Q must be rejected"
    );
}

#[test]
fn report_constraint_count() {
    let c = xark_test_harness::compile_file(&src(), "grumpkin_ipa", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let n = c.minimized_r1cs_len();
    println!("grumpkin_ipa (n=4 deferred MSM, 254-bit scalars): {n} minimized R1CS constraints");
    // sanity envelope: native Grumpkin keeps this in the low tens of thousands.
    assert!(n < 60_000, "unexpectedly large: {n}");
}

#[test]
fn groth16_setup_prove_verify() {
    // The full BN254 Groth16 pipeline on the accumulator vector: setup → prove
    // → verify (dev-mode fixed-seed setup — see `prove_and_verify`).
    let c = xark_test_harness::compile_file(&src(), "grumpkin_ipa", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let xbc = std::fs::read(c.out_dir.join("circuit.xbc")).expect("read circuit.xbc");
    let cp = xark_ir::function_decode::expand_function_blob(&xbc).expect("expand circuit.xbc");
    let r1cs = cp.to_r1cs();
    let prim = cp.to_primitive();
    let inputs = honest_inputs(&prim);
    let ok = xark_prover::prove_and_verify(&r1cs, &prim, &inputs)
        .expect("groth16 setup/prove/verify");
    assert!(ok, "the Groth16 proof of the accumulator claim must verify");
}
