//! The template-reduced R1CS (what `xark setup` keys) must stay as sound as the full
//! circuit. Regression: the per-scope minimizer used to treat a template call's
//! output as a free internal variable in the *caller*, eliminate it there and drop
//! the row tying it to a public output — leaving the output unconstrained, so a proof
//! could claim any value.
//!
//! Fixture: `examples/poseidon2_sponge`'s `circuit.xbc` (`xark build`; its rounds
//! are templated). Regenerate it after a container-format change.

use std::collections::BTreeMap;

use xark_ir::function_decode::{expand_function_blob, expand_function_blob_reduced};
use xark_ir::solver::{check_cp, solve_cp};

const XBC: &[u8] = include_bytes!("fixtures/poseidon2_sponge.xbc");
/// `poseidon2_sponge(1, 2, 3, 4, 5)`.
const HASH: &str = "8828141863764826539393608139805007447022200187560478202710690249571019683634";

fn witness(h: &str) -> BTreeMap<u32, xark_ir::solver::Fp> {
    let full = expand_function_blob(XBC).unwrap();
    let id = |n: &str| full.vars.iter().find(|v| v.name == n).unwrap().id;
    let inputs: BTreeMap<u32, String> = [
        ("a", "1"),
        ("b", "2"),
        ("c", "3"),
        ("d", "4"),
        ("e", "5"),
        ("out", h),
    ]
    .into_iter()
    .map(|(n, v)| (id(n), v.to_string()))
    .collect();
    solve_cp(&full, &inputs).unwrap()
}

#[test]
fn fixture_is_templated() {
    // Otherwise the tests below check a flat circuit and prove nothing about the
    // per-template minimizer.
    assert!(xark_ir::function_decode::count_templates(XBC) > 0);
}

#[test]
fn reduced_circuit_rejects_a_wrong_public_output() {
    let full = expand_function_blob(XBC).unwrap();
    let reduced = expand_function_blob_reduced(XBC).unwrap();
    let honest = witness(HASH);
    assert!(
        check_cp(&full, &honest).is_ok(),
        "the full circuit accepts the hash"
    );
    assert!(
        check_cp(&reduced, &honest).is_ok(),
        "so does the keyed (reduced) one"
    );
    let forged = witness("12345");
    assert!(
        check_cp(&full, &forged).is_err(),
        "the full circuit rejects out = 12345"
    );
    assert!(
        check_cp(&reduced, &forged).is_err(),
        "the keyed (reduced) circuit must reject it too"
    );
}

#[test]
fn reduced_circuit_references_every_public_input() {
    let reduced = expand_function_blob_reduced(XBC).unwrap();
    for v in reduced
        .vars
        .iter()
        .filter(|v| v.role == xark_ir::primitive::VarRole::PublicInput)
    {
        assert!(
            reduced
                .constraints
                .iter()
                .flat_map(|r| [&r.a, &r.b, &r.c])
                .any(|lc| lc.terms.iter().any(|t| t.var == v.id)),
            "public input `{}` is unconstrained in the keyed circuit",
            v.name
        );
    }
}
