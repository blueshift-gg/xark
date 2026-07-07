//! Solve-and-check the Ed25519 gadget examples against an independent Python
//! reference (scratchpad `ed25519_ref.py`) implementing the SAME complete
//! twisted-Edwards addition (`a = −1`) and 256-bit MSB→LSB double-and-add.
//!
//! Confirms: (1) `[k]·P` matches the reference — including the hard-coded `[5]·B`
//! cross-check that pins the limb order and bit order; (2) the emitted R1CS is
//! analyzer-clean; (3) tampered outputs / signatures are rejected. The EdDSA
//! vector is algebraic (`[S]·B == R + [k]·A` by construction — no hashing).
//!
//! Examples are compiled on demand via the shared `xark-test-harness` crate.

use std::collections::BTreeMap;
use xark_ir::{primitive, solver};

fn load(example: &str, out: &str) -> primitive::PrimitiveProgram {
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples")
        .join(example)
        .join("src/lib.rs");
    let c = xark_test_harness::compile_file(&src, out, "bn254");
    assert!(c.status_success, "compiling examples/{example} failed: {}", c.stderr);
    c.program()
}

fn id_of<'a>(program: &'a primitive::PrimitiveProgram, name: &str) -> u32 {
    program
        .vars
        .iter()
        .find(|v| v.name == name)
        .unwrap_or_else(|| panic!("missing circuit var `{name}`"))
        .id
}

/// Insert `name[0]/name[1]/name[2]` = the three limbs of a value (the flattened
/// aggregate-input names, where `name` is the leaf array path, e.g. `k` or
/// `p.x.limbs`).
fn put3(inputs: &mut BTreeMap<u32, String>, program: &primitive::PrimitiveProgram, name: &str, limbs: [&str; 3]) {
    for (i, l) in limbs.iter().enumerate() {
        inputs.insert(id_of(program, &format!("{name}[{i}]")), (*l).to_string());
    }
}

// ---- reference vectors (ed25519_ref.py) ------------------------------------

// [5]·B == the 5B vector from the prompt (hard cross-check of limb/bit order).
const K5: [&str; 3] = ["5", "0", "0"];
const BX: [&str; 3] = ["45522188556658772877366554", "10615720421966981067801172", "2524463244633754693274190"];
const BY: [&str; 3] = ["46422751473201760308717144", "30948500982134506872478105", "7737125245533626718119526"];
const R5X: [&str; 3] = ["33706583767550703264789043", "62709572061741392062833912", "5590589292175639374188279"];
const R5Y: [&str; 3] = ["3680440249420209425139949", "68087786193698555118168613", "7199291165562692104487622"];

// [987654321]·(2B).
const KC: [&str; 3] = ["987654321", "0", "0"];
const P2X: [&str; 3] = ["28581523890186841676303886", "55555705152498246977393751", "4130659841666215982649411"];
const P2Y: [&str; 3] = ["68083945039146168318731209", "72097079905362190700201360", "2597539009022204787677733"];
const RCX: [&str; 3] = ["3084110821577783849686387", "25780125767275144119022374", "9172652562761513664972756"];
const RCY: [&str; 3] = ["23640053870041257343179867", "49522744475693505503098409", "2614569823037288618006964"];

// EdDSA algebraic vector: [S]·B == R + [k]·A.
const AX: [&str; 3] = ["67250461738013543997724937", "51258435392452215962235818", "8070370278740851033482836"];
const AY: [&str; 3] = ["40262224518264561256855272", "71970329806110551259469126", "8107826934435358735261814"];
const RX: [&str; 3] = ["7457783715957646980183917", "73723665576411286276411539", "3192658075497919851334904"];
const RY: [&str; 3] = ["2356521577147883102564275", "62301682795876274981280083", "7896457351406948862476721"];
const S: [&str; 3] = ["67014997723193888983369096", "35374200410649094219429019", "721811"];
const K: [&str; 3] = ["19669060164829260676537457", "1005", "0"];
const S_TAMPERED: [&str; 3] = ["67014997723193888983369097", "35374200410649094219429019", "721811"];

fn smul_inputs(
    program: &primitive::PrimitiveProgram,
    k: [&str; 3],
    px: [&str; 3],
    py: [&str; 3],
    rx: [&str; 3],
    ry: [&str; 3],
) -> BTreeMap<u32, String> {
    let mut inputs = BTreeMap::new();
    put3(&mut inputs, program, "k", k);
    put3(&mut inputs, program, "p.x.limbs", px);
    put3(&mut inputs, program, "p.y.limbs", py);
    put3(&mut inputs, program, "r.x.limbs", rx);
    put3(&mut inputs, program, "r.y.limbs", ry);
    inputs
}

#[test]
fn smul_5b_crosscheck_and_analyzer_clean() {
    let program = load("ed25519_smul", "ed25519_smul");
    // Constraint-count bridge (pinned invariant). The twisted-Edwards ops this
    // exercises are proven sound sorry-free in `formal/Formal/Edwards.lean`
    // (`edwards_add_on_curve`, `edwards_add_closure`). The dedicated affine
    // doubling (curve identity `d·x²y² = y²−x²−1`, 5 muls + 2 inv) set this count.
    let n = program.constraints.len();
    eprintln!("ed25519 scalar_mul: {n} constraints");
    // This count includes the input-point coordinate range checks `scalar_mul`
    // runs before the non-native group law (2 coords × 3 × 86-bit limbs), which
    // pin every `mod_mul` operand < 2^86. If it changes, confirm the change is
    // intended before re-pinning.
    assert_eq!(n, 3_731_576, "ed25519 scalar_mul constraint count changed");

    // (1) [5]·B == the hard-coded 5B vector — pins limb order + bit order.
    let inputs = smul_inputs(&program, K5, BX, BY, R5X, R5Y);
    let assign = solver::solve_and_check(&program, &inputs).expect("[5]·B must match the 5B reference vector");

    // (2) analyzer-clean: no under-constrained (forgeable) derived variables.
    let holes = solver::analyze_underconstrained(&program, &assign);
    assert!(holes.is_empty(), "ed25519 scalar_mul under-constrained: {holes:?}");

    // (3) a wrong claimed output x-limb is rejected.
    let mut bad = inputs.clone();
    bad.insert(id_of(&program, "r.x.limbs[0]"), "123".to_string());
    assert!(solver::solve_and_check(&program, &bad).is_err(), "wrong [5]·B output must be rejected");
}

#[test]
fn smul_on_doubled_base_vector() {
    let program = load("ed25519_smul", "ed25519_smul_c");
    // [987654321]·(2B) matches the reference.
    let inputs = smul_inputs(&program, KC, P2X, P2Y, RCX, RCY);
    solver::solve_and_check(&program, &inputs).expect("[987654321]·(2B) must match the reference vector");
}

#[test]
fn eddsa_verify_honest_and_tamper() {
    let program = load("ed25519_verify", "ed25519_verify");
    // Constraint-count bridge (pinned). The EdDSA verify relation and the
    // scalar-mul composition are proven in `formal/Formal/Edwards.lean`
    // (`eddsa_verify_sound`, `eddsa_verify_compose`).
    let n = program.constraints.len();
    eprintln!("ed25519 eddsa_verify: {n} constraints");
    // This count reflects the full verification relation:
    //  * `enforce_on_curve` on `a_pub` and `r_sig` (range-checks the coordinates
    //    AND binds each point to `−x² + y² = 1 + d·x²·y²`) before the group law;
    //  * `double_scalar_mul` range-checks its two input points;
    //  * `S < L` canonical-scalar check (recompose bits → Fq limbs, assert < L);
    //  * cofactored equation `[8]·t == [8]·R` (6 `ec_double`s) clearing any
    //    small-order component of `A`/`R`.
    assert_eq!(n, 4_662_466, "ed25519 eddsa_verify constraint count changed");

    let mut inputs = BTreeMap::new();
    put3(&mut inputs, &program, "a.x.limbs", AX);
    put3(&mut inputs, &program, "a.y.limbs", AY);
    put3(&mut inputs, &program, "r.x.limbs", RX);
    put3(&mut inputs, &program, "r.y.limbs", RY);
    put3(&mut inputs, &program, "s", S);
    put3(&mut inputs, &program, "k", K);

    // (1) honest signature verifies: [S]·B == R + [k]·A.
    solver::solve_and_check(&program, &inputs).expect("honest Ed25519 signature must verify");

    // (2) a tampered signature scalar S is rejected.
    let mut bad = inputs.clone();
    put3(&mut bad, &program, "s", S_TAMPERED);
    assert!(solver::solve_and_check(&program, &bad).is_err(), "tampered S must be rejected");

    // (3) a tampered challenge k is rejected.
    let mut bad2 = inputs.clone();
    bad2.insert(id_of(&program, "k[0]"), "123456".to_string());
    assert!(solver::solve_and_check(&program, &bad2).is_err(), "tampered k must be rejected");
}
