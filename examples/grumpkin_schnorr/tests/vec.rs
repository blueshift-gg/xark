//! The circuit accepts a signature from the host signer (`xark_grumpkin::schnorr::host`)
//! with no under-constrained variable, and rejects it on another message or key.

use grumpkin_schnorr::GrumpkinSchnorrInputs;
use xark_grumpkin::schnorr::host::{Base, SigningKey};

fn inputs(seed: u8, msg: [u64; 2], signed: [u64; 2]) -> GrumpkinSchnorrInputs {
    let sk = SigningKey::from_seed(&[seed; 32]).unwrap();
    GrumpkinSchnorrInputs {
        pubkey: sk.public_key().into(),
        msg: msg.map(Into::into),
        sig: sk.sign(&signed.map(Base::from)).into(),
    }
}

#[test]
fn verifies_a_host_signature() {
    let circuit = xark::prover::circuit("grumpkin_schnorr");
    circuit
        .check_constrained(inputs(7, [1, 2], [1, 2]))
        .expect("a host signature verifies");
    assert!(
        circuit.check(inputs(7, [1, 3], [1, 2])).is_err(),
        "a signature on another message"
    );
    let mut other_key = inputs(7, [1, 2], [1, 2]);
    other_key.pubkey = inputs(8, [1, 2], [1, 2]).pubkey;
    assert!(circuit.check(other_key).is_err(), "another key");
}

#[test]
fn report_constraint_count() {
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/lib.rs");
    let c = xark_test_harness::compile_file(&src, "grumpkin_schnorr", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let n = c.minimized_r1cs_len();
    println!("grumpkin_schnorr: {n} minimized R1CS constraints");
    assert!(n < 10_000, "unexpectedly large: {n}");
}
