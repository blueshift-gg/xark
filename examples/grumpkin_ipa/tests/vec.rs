//! Verify the `grumpkin_ipa` deferred-MSM accumulator circuit against an
//! independent `ark-grumpkin` reference vector (`Q = Σⱼ sⱼ·Gⱼ`, full-width
//! ~253-bit scalars). Confirms: (1) the emitted R1CS is
//! satisfiable on the honest vector, (2) it is analyzer-clean (no forgeable
//! derived vars), (3) a wrong claimed `Q` is rejected, and (4) reports the
//! minimized constraint count — the efficiency evidence.

use std::path::Path;

use grumpkin_ipa::GrumpkinIpaInputs;

fn src() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("src/lib.rs")
}

// --- ark-grumpkin reference vector (validated: same routine reproduces the
//     gadget's corr₁₂₈ exactly). Q = Σⱼ sⱼ·Gⱼ, full-width sⱼ. ---
const G0X: &str = "3078034153852398078128400807926804309327113743808504829582559963737223069694";
const G0Y: &str = "12696890884641142049456609402511852099066095483298083855939691685001536962732";
const S0: &str = "6140165362089529657468554467276523978638382820158559440551558470479619759543";
const G1X: &str = "18660890509582237958343981571981920822503400000196279471655180441138020044621";
const G1Y: &str = "8902249110305491597038405103722863701255802573786510474664632793109847672620";
const S1: &str = "11757316442606476628842495536137561788309419658909348721695527359258242995180";
const G2X: &str = "763947558912359675602353050994051190166418588022888764656343140671310115434";
const G2Y: &str = "1244893704640049169462398469384866579396698880516857177429128873187668729859";
const S2: &str = "759340313105376065728450076538675340688684591446184547485944253064936260897";
const G3X: &str = "12229279139087521908560794489267966517139449915173592433539394009359081620359";
const G3Y: &str = "12096995292699515952722386974733884667125946823386040531322131902193094989869";
const S3: &str = "6029718098268116314681739296129540725359801146837944794739741376995798859606";
const QX: &str = "20903080311600324333489123549926276227734645934862144969632742816704833802883";
const QY: &str = "21415318633544108147494823273278274647092448118324172091757610792088028377648";

fn honest() -> GrumpkinIpaInputs {
    GrumpkinIpaInputs {
        g: [(G0X, G0Y), (G1X, G1Y), (G2X, G2Y), (G3X, G3Y)].map(Into::into),
        s: [S0, S1, S2, S3].map(Into::into),
        q: (QX, QY).into(),
    }
}

#[test]
fn deferred_msm_accumulator_verifies() {
    let circuit = xark::prover::circuit("grumpkin_ipa");
    // satisfiable on the honest vector, with no under-constrained (forgeable)
    // witness variable.
    circuit.check_constrained(honest()).expect("grumpkin_ipa must verify on the reference accumulator vector");

    let mut bad = honest();
    bad.q.x = 123.into();
    assert!(circuit.check(bad).is_err(), "a wrong claimed Q must be rejected");
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
    // solve → dev-mode Groth16 setup → prove → verify, on the built circuit.
    xark::prover::circuit("grumpkin_ipa")
        .prove_dev(honest())
        .expect("the Groth16 proof must verify");
}
