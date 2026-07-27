//! Verify the `grumpkin_nova_fold` folding-step circuit against a host reference
//! (`ark-grumpkin` + the host `poseidon2` crate, KAT-identical to the in-circuit
//! gadget). The circuit derives the same challenge `r` in-circuit and checks the
//! four fold equations. Accept / analyzer-clean / tamper-reject / Groth16.

use std::collections::BTreeMap;
use std::path::Path;
use xark_ir::{primitive, solver};

fn src() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("src/lib.rs")
}
fn load() -> primitive::PrimitiveProgram {
    let c = xark_test_harness::compile_file(&src(), "grumpkin_nova_fold", "bn254");
    assert!(c.status_success, "compiling grumpkin_nova_fold failed:\n{}", c.stderr);
    c.program()
}

// --- host reference (scratchpad `nova.rs`) ---
const CW1X: &str = "5541057644303065254198978319021299963813613025890967735191946958170803635963";
const CW1Y: &str = "1090039197710617384995251408449123883585777313183467283953051925104608545894";
const CE1X: &str = "4850035816089662575584531767234751057843073514516729038085564438359968988824";
const CE1Y: &str = "14505663385114841392403642611656212825504921992342703259189393607313084956304";
const CW2X: &str = "6982833205550972504727268126882606935220856388520904389511767633707517216416";
const CW2Y: &str = "6846488345837025410915261940728431962441959903332367673748066118690135566243";
const CE2X: &str = "21857931111933940468507803821200242221118073884443263221803745163710245639690";
const CE2Y: &str = "21554679576078403979715883448980535010025920061050455524556521921544833368903";
const CTX: &str = "19826114093127959134809215198372575684659709447080224615903207975214865157084";
const CTY: &str = "5219752020355850107317638392714924038361734037020523596663258827219519877797";
const U1: &str = "7";
const X1: &str = "13";
const U2: &str = "3";
const X2: &str = "17";
const CWX: &str = "11966079537070335829016394407448679634087413681692693621123236353324809158961";
const CWY: &str = "15895146621981423838113273342929641609665537647423234487987005383700022996107";
const CEX: &str = "16744414445147054234428029429180798717426580708476429620568182013505882040441";
const CEY: &str = "6279653759954346604701321765885825095226249735961974659357923588266810191122";
const U: &str = "320783020589613664432541343672636501592";
const X: &str = "1817770450007810765117734280811606842328";

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
        ("cw1.x", CW1X), ("cw1.y", CW1Y), ("ce1.x", CE1X), ("ce1.y", CE1Y),
        ("cw2.x", CW2X), ("cw2.y", CW2Y), ("ce2.x", CE2X), ("ce2.y", CE2Y),
        ("ct.x", CTX), ("ct.y", CTY),
        ("u1", U1), ("x1", X1), ("u2", U2), ("x2", X2),
        ("cw.x", CWX), ("cw.y", CWY), ("ce.x", CEX), ("ce.y", CEY),
        ("u", U), ("x", X),
    ] {
        m.insert(id(n), v.to_string());
    }
    m
}

#[test]
fn nova_fold_verifies() {
    let program = load();
    let mut inputs = honest(&program);

    let assign = solver::solve_and_check(&program, &inputs)
        .expect("grumpkin_nova_fold must verify the honest fold");
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(holes.is_empty(), "under-constrained: {holes:?}");

    // tamper the claimed folded comm_W → rejected (FS-bound).
    let cwx = program.vars.iter().find(|v| v.name == "cw.x").unwrap().id;
    inputs.insert(cwx, "123".to_string());
    assert!(
        solver::solve_and_check(&program, &inputs).is_err(),
        "a wrong folded instance must be rejected"
    );
}

#[test]
fn report_constraint_count() {
    let c = xark_test_harness::compile_file(&src(), "grumpkin_nova_fold", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let n = c.minimized_r1cs_len();
    println!("grumpkin_nova_fold (Nova folding step, in-circuit Poseidon2 FS): {n} minimized R1CS constraints");
    assert!(n < 40_000, "unexpectedly large: {n}");
}

#[test]
fn groth16_setup_prove_verify() {
    let c = xark_test_harness::compile_file(&src(), "grumpkin_nova_fold", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let xbc = std::fs::read(c.out_dir.join("circuit.xbc")).expect("read circuit.xbc");
    let cp = xark_ir::function_decode::expand_function_blob(&xbc).expect("expand circuit.xbc");
    let r1cs = cp.to_r1cs();
    let prim = cp.to_primitive();
    let inputs = honest(&prim);
    let ok = xark_prover::prove_and_verify(&r1cs, &prim, &inputs)
        .expect("groth16 setup/prove/verify");
    assert!(ok, "the Groth16 proof of the folding step must verify");
}
