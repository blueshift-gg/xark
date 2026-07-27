//! Verify the 2-step `grumpkin_ivc` circuit against a host reference
//! (`ark-grumpkin` + host `poseidon2`, KAT-matched to the in-circuit gadget).
//! Accept / analyzer-clean / tamper-reject (both the computation and the
//! accumulator) / Groth16.

use std::collections::BTreeMap;
use std::path::Path;
use xark_ir::{primitive, solver};

fn src() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("src/lib.rs")
}
fn load() -> primitive::PrimitiveProgram {
    let c = xark_test_harness::compile_file(&src(), "grumpkin_ivc", "bn254");
    assert!(c.status_success, "compiling grumpkin_ivc failed:\n{}", c.stderr);
    c.program()
}

// --- host reference (scratchpad `ivc.rs`), z0=3 → z1=14 → z2=201 ---
const U0_CWX: &str = "5541057644303065254198978319021299963813613025890967735191946958170803635963";
const U0_CWY: &str = "1090039197710617384995251408449123883585777313183467283953051925104608545894";
const U0_CEX: &str = "4850035816089662575584531767234751057843073514516729038085564438359968988824";
const U0_CEY: &str = "14505663385114841392403642611656212825504921992342703259189393607313084956304";
const U0_U: &str = "7";
const U0_X: &str = "13";
const S0_CWX: &str = "2689464466883345466870406516192131206798867494563174663401373503616308486522";
const S0_CWY: &str = "14284470724459285329583671672346501634471412747554954445898157584469342023256";
const S0_CEX: &str = "17139003749319088366501156891546301999505258967247129491939947605044679468675";
const S0_CEY: &str = "16801526290712393585817395843048980845538227969954237825544784234576984878296";
const S0_U: &str = "1";
const S0_X: &str = "5";
const T0X: &str = "17379784669106027629420386012926013711889290282791045264368570596918799018333";
const T0Y: &str = "5261888182127316643551963109191000327408457967043340449287656632743840125850";
const S1_CWX: &str = "10546973163938834992057655941714093117541054866525233410122825616206515416586";
const S1_CWY: &str = "21561590198562987952940102976120074479991444644168640911055334956453223816010";
const S1_CEX: &str = "2952528264734602862153950046340290171762558417203905093173981344010936695347";
const S1_CEY: &str = "17188152024687562778396633295778759667136661460956133253669780314451638526096";
const S1_U: &str = "1";
const S1_X: &str = "9";
const T1X: &str = "1218999359690073819972466332590110033693734717026603225231520977389534931051";
const T1Y: &str = "10403522540305464146599112152415459333198500139273690429765211515850334941903";
const U2_CWX: &str = "5517910283929585245960604916688028556908236266601450164031198941768767433393";
const U2_CWY: &str = "8677672583706613780392132267934536901742249072692126691181314097884258637947";
const U2_CEX: &str = "13198611912042078670715485350075275321890792826202362129103149857101579204264";
const U2_CEY: &str = "3727998360742946830544156845412383767579468750950238383828341782378959373330";
const U2_U: &str = "431805324872636791672518448936304316288";
const U2_X: &str = "2800240808433720351539188551067984909022";
const Z0: &str = "3";
const Z2: &str = "201";

fn honest(program: &primitive::PrimitiveProgram) -> BTreeMap<u32, String> {
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
        ("u0_cw.x", U0_CWX), ("u0_cw.y", U0_CWY), ("u0_ce.x", U0_CEX), ("u0_ce.y", U0_CEY),
        ("u0_u", U0_U), ("u0_x", U0_X),
        ("s0_cw.x", S0_CWX), ("s0_cw.y", S0_CWY), ("s0_ce.x", S0_CEX), ("s0_ce.y", S0_CEY),
        ("s0_u", S0_U), ("s0_x", S0_X),
        ("t0.x", T0X), ("t0.y", T0Y),
        ("s1_cw.x", S1_CWX), ("s1_cw.y", S1_CWY), ("s1_ce.x", S1_CEX), ("s1_ce.y", S1_CEY),
        ("s1_u", S1_U), ("s1_x", S1_X),
        ("t1.x", T1X), ("t1.y", T1Y),
        ("u2_cw.x", U2_CWX), ("u2_cw.y", U2_CWY), ("u2_ce.x", U2_CEX), ("u2_ce.y", U2_CEY),
        ("u2_u", U2_U), ("u2_x", U2_X),
        ("z0", Z0), ("z2", Z2),
    ] {
        m.insert(id(n), v.to_string());
    }
    m
}

#[test]
fn ivc_2step_verifies() {
    let program = load();
    let base = honest(&program);

    let assign = solver::solve_and_check(&program, &base)
        .expect("grumpkin_ivc must verify the honest 2-step run");
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(holes.is_empty(), "under-constrained: {holes:?}");

    let id = |name: &str| program.vars.iter().find(|v| v.name == name).unwrap().id;

    // tamper the computation output → rejected (z2 must equal F(F(z0))).
    let mut bad_z = base.clone();
    bad_z.insert(id("z2"), "202".to_string());
    assert!(solver::solve_and_check(&program, &bad_z).is_err(), "wrong z2 must reject");

    // tamper the final accumulator → rejected (fold chain is FS-bound).
    let mut bad_u = base.clone();
    bad_u.insert(id("u2_u"), "123".to_string());
    assert!(solver::solve_and_check(&program, &bad_u).is_err(), "wrong U2 must reject");
}

#[test]
fn report_constraint_count() {
    let c = xark_test_harness::compile_file(&src(), "grumpkin_ivc", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let n = c.minimized_r1cs_len();
    println!("grumpkin_ivc (2-step folding IVC, in-circuit Poseidon2 FS): {n} minimized R1CS constraints");
    assert!(n < 60_000, "unexpectedly large: {n}");
}

#[test]
fn groth16_setup_prove_verify() {
    let c = xark_test_harness::compile_file(&src(), "grumpkin_ivc", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let xbc = std::fs::read(c.out_dir.join("circuit.xbc")).expect("read circuit.xbc");
    let cp = xark_ir::function_decode::expand_function_blob(&xbc).expect("expand circuit.xbc");
    let r1cs = cp.to_r1cs();
    let prim = cp.to_primitive();
    let inputs = honest(&prim);
    let ok = xark_prover::prove_and_verify(&r1cs, &prim, &inputs)
        .expect("groth16 setup/prove/verify");
    assert!(ok, "the Groth16 proof of the 2-step IVC must verify");
}
