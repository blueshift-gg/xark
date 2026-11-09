//! The rows a proving key is made for (template-reduced from `circuit.xbc`, or
//! boundary-minimized into `r1cs.stream`) must reject every one-variable witness
//! change the flat, unoptimized R1CS rejects: an optimizer that cuts a variable
//! loose accepts a forged witness the circuit rejects. One variable at a time
//! can't see a dropped row that only another row's change would expose (a
//! booleanity row beside a packing row): this checks no kept variable lost its
//! constraints, not that every row survived.
//!
//! For each example: `xark build` + `xark setup` (`auto`, or the form it asks for),
//! then the
//! honest witness from the example's inputs (`fixtures/inputs/<name>.json`).
//! Every variable the keyed rows still use is changed in turn (a bit flips, any
//! other value gets `+1`), all others kept, and the keyed rows must reject the
//! changed witness exactly when the flat, unoptimized R1CS does. Variables the
//! optimizer eliminated aren't compared: they're functions of the ones kept.

use std::collections::BTreeMap;

use crate::common::{tempdir, xark_build, xark_setup};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use xark_groth16::r1cs::RowChunk;
use xark_groth16::{ConstraintSource, PkSource};
use xark_ir::VarId;
use xark_ir::primitive::VarRole;

/// For each variable of `src`: whether changing it (by `delta[id]`, all else as
/// in `w`) breaks a row. Panics if the honest witness `w` breaks one.
fn rejects(
    src: &dyn ConstraintSource,
    w: &BTreeMap<VarId, Fr>,
    delta: &BTreeMap<VarId, Fr>,
) -> BTreeMap<VarId, bool> {
    let layout = src.layout();
    let z = layout.assignment(|id| w.get(&id).copied());
    // Position → (id, change); position 0 is the constant 1.
    let mut ids = vec![None; z.len()];
    for (&id, &d) in delta {
        if let Some(p) = layout.position(id) {
            ids[p] = Some((id, d));
        }
    }
    let mut broken = vec![false; z.len()];
    let mut chunk = RowChunk::default();
    for win in src.windows(1 << 14) {
        src.expand(&win, &mut chunk);
        for i in 0..chunk.rows() {
            let [a, b, c] = [0, 1, 2].map(|m| chunk.eval(i, m, &z));
            assert_eq!(
                a * b,
                c,
                "the honest witness breaks row {}",
                win.rows.start + i
            );
            // Each column's coefficient in A, B and C (a column may repeat).
            let mut coeffs: BTreeMap<u32, [Fr; 3]> = BTreeMap::new();
            for m in 0..3 {
                let (cols, ks) = chunk.terms(i, m);
                for (&col, k) in cols.iter().zip(ks) {
                    coeffs.entry(col).or_insert([Fr::zero(); 3])[m] += k;
                }
            }
            for (col, [ka, kb, kc]) in coeffs {
                let Some((_, d)) = ids[col as usize] else {
                    continue;
                };
                if (a + ka * d) * (b + kb * d) != c + kc * d {
                    broken[col as usize] = true;
                }
            }
        }
    }
    ids.iter()
        .zip(&broken)
        .filter_map(|(id, &bad)| id.map(|(id, _)| (id, bad)))
        .collect()
}

/// `form`: the key form for `name`, so both row sources stay covered: the one `auto`
/// picks, or with `request` the one asked for (`auto` minimizes no example now: the
/// frontend's folds and its `n`-row decompositions leave the global minimize under
/// 1% to save).
fn keyed_rows_reject_what_the_flat_circuit_rejects(name: &str, form: &str, request: bool) {
    let tmp = tempdir();
    let (out, target) = (tmp.path().join("out"), tmp.path().join("target"));
    let (ok, err) = xark_build(name, &out, &target);
    assert!(ok, "build failed: {err}");
    if request {
        let o = std::process::Command::new(crate::common::xark_bin())
            .arg("setup")
            .arg(&out)
            .args(["--deterministic-rng", "1", "--r1cs-form", form])
            .output()
            .unwrap();
        assert!(
            o.status.success(),
            "setup failed: {}",
            String::from_utf8_lossy(&o.stderr)
        );
    } else {
        let (ok, err) = xark_setup(&out);
        assert!(ok, "setup failed: {err}");
    }

    let xbc = std::fs::read(out.join("circuit.xbc")).unwrap();
    let flat = xark_ir::function_decode::expand_function_blob(&xbc).unwrap();
    let prim = flat.to_primitive();
    let fixture = crate::common::fixture_dir().join(format!("inputs/{name}.json"));
    let given: BTreeMap<String, String> =
        serde_json::from_str(&std::fs::read_to_string(fixture).unwrap()).unwrap();
    let inputs: BTreeMap<VarId, String> = prim
        .vars
        .iter()
        .filter(|v| matches!(v.role, VarRole::PublicInput | VarRole::PrivateInput))
        .map(|v| (v.id, given[&v.name].clone()))
        .collect();
    let w: BTreeMap<VarId, Fr> = xark_ir::solver::solve_and_check(&prim, &inputs)
        .expect("the fixture's inputs satisfy the circuit")
        .into_iter()
        .map(|(id, v)| (id, v.as_bn254_fr().unwrap()))
        .collect();
    let delta: BTreeMap<VarId, Fr> = w
        .iter()
        .map(|(&id, &v)| (id, if v.is_one() { -Fr::one() } else { Fr::one() }))
        .collect();

    // The rows `xark prove` / `Circuit::prove` pick for this key.
    let a_len = xark_groth16::SerializedPk::open(&out.join("pk.bin"))
        .unwrap()
        .header()
        .a_len;
    let meta: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(out.join("metadata.json")).unwrap()).unwrap();
    assert_eq!(meta["r1cs_form"], form, "{name}: key form");
    let cached = std::fs::read(out.join("r1cs.stream")).ok();
    assert_eq!(cached.is_some(), form == "minimized", "{name}: r1cs.stream");
    let keyed = xark_prover::rows_for_key(&xbc, a_len, cached).unwrap();
    let flat_r1cs = flat.to_r1cs();
    let flat_rows = xark_groth16::ProgramSource::new(&flat_r1cs);

    let keyed = rejects(&*keyed, &w, &delta);
    let flat = rejects(&flat_rows, &w, &delta);
    let mut differ = Vec::new();
    for (id, k) in &keyed {
        let f = flat
            .get(id)
            .unwrap_or_else(|| panic!("keyed rows use v{id}, which the flat R1CS doesn't"));
        if k != f {
            differ.push((*id, *k, *f));
        }
    }
    let rejected = keyed.values().filter(|&&r| r).count();
    eprintln!(
        "{name}: {} of {} variables kept; {rejected} changes rejected by both, {} differ",
        keyed.len(),
        flat.len(),
        differ.len()
    );
    assert!(
        differ.is_empty(),
        "{name}: (var, keyed rejects, flat rejects): {:?}",
        &differ[..differ.len().min(8)]
    );
}

#[test]
fn cube_keyed_rows_reject_every_change_the_flat_r1cs_rejects() {
    keyed_rows_reject_what_the_flat_circuit_rejects("cube", "reduced", false);
}

#[test]
fn sha256_keyed_rows_reject_every_change_the_flat_r1cs_rejects() {
    keyed_rows_reject_what_the_flat_circuit_rejects("sha256", "minimized", true);
}

#[test]
fn aes256_gcm_keyed_rows_reject_every_change_the_flat_r1cs_rejects() {
    keyed_rows_reject_what_the_flat_circuit_rejects("aes256_gcm", "reduced", false);
}
