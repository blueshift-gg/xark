//! Ordering contract, QAP, and whole-proof oracles against arkworks.
//!
//! * The streamed assignment and every streamed row equal arkworks' `gr1cs`
//!   allocation and matrices (the ordering contract).
//! * `h` is bit-identical to `LibsnarkReduction::witness_map`.
//! * For the same `(r, s)` the proof is byte-identical to `Groth16::prove`, and it
//!   verifies under the ordinary verifier — from an in-memory key and from
//!   serialized keys (compressed, uncompressed, legacy).
//! * Breaking the order (consistently relabelling two variables) makes the proof
//!   fail — the contract has teeth.

use std::collections::{BTreeMap, BTreeSet};

use ark_bn254::{Bn254, Fr};
use ark_ff::{UniformRand, Zero};
use ark_groth16::r1cs_to_qap::{LibsnarkReduction, R1CSToQAP};
use ark_poly::GeneralEvaluationDomain;
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, OptimizationGoal,
    R1CS_PREDICATE_LABEL, SynthesisMode,
};
use ark_serialize::{CanonicalSerialize, Compress};
use ark_snark::SNARK;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use xark_groth16::r1cs::{RowChunk, eval_rows, first_unsatisfied};
use xark_groth16::{
    BytecodeSource, ConstraintSource, DomainKind, FftConfig, InMemoryPk, ProgramSource, ProveError,
    ProverConfig, SerializedPk, prove, qap,
};
use xark_groth16::{Proof, ProvingKey, VerifyingKey};
use xark_ir::r1cs::{FieldSpec, R1csConstraint, R1csProgram, Variable, Visibility};
use xark_ir::{FieldConst, LinearCombination, Term, VarId};
use xark_prover::XarkCircuit;

#[path = "support/ark.rs"]
mod ark;
#[path = "support/phase2_ark.rs"]
mod phase2_ark;
use ark::{ArkCircuit, convert};

/// arkworks' Groth16 as the reference oracle, with `xark-groth16`'s key and proof
/// types (converted through their bytes) and the `Groth16` call shapes.
struct ArkG16;

impl ArkG16 {
    fn circuit_specific_setup<R: rand::RngCore + rand::CryptoRng>(
        c: XarkCircuit,
        rng: &mut R,
    ) -> Result<(ProvingKey<Bn254>, VerifyingKey<Bn254>), ark_relations::gr1cs::SynthesisError>
    {
        let (pk, vk) =
            ark_groth16::Groth16::<Bn254>::circuit_specific_setup(ArkCircuit::of(&c), rng)?;
        Ok((convert(&pk), convert(&vk)))
    }

    fn prove<R: rand::RngCore + rand::CryptoRng>(
        pk: &ProvingKey<Bn254>,
        c: XarkCircuit,
        rng: &mut R,
    ) -> Result<Proof<Bn254>, ark_relations::gr1cs::SynthesisError> {
        let pk: ark_groth16::ProvingKey<Bn254> = convert(pk);
        let proof = ark_groth16::Groth16::<Bn254>::prove(&pk, ArkCircuit::of(&c), rng)?;
        Ok(convert(&proof))
    }

    fn verify(
        vk: &VerifyingKey<Bn254>,
        x: &[Fr],
        proof: &Proof<Bn254>,
    ) -> Result<bool, ark_relations::gr1cs::SynthesisError> {
        let vk: ark_groth16::VerifyingKey<Bn254> = convert(vk);
        ark_groth16::Groth16::<Bn254>::verify(&vk, x, &convert(proof))
    }
}

/// A random satisfiable R1CS with public/private/internal ids interleaved, some
/// unreferenced variables, constants, duplicate terms, and big coefficients.
fn random_program(seed: u64, n_cons: usize) -> (R1csProgram, BTreeMap<VarId, Fr>) {
    let mut r = ChaCha20Rng::seed_from_u64(seed);
    let fc_of = |f: Fr| FieldConst::from_decimal(&f.to_string()).unwrap();
    let mut variables = Vec::new();
    let mut assign = BTreeMap::new();
    let mut live: Vec<VarId> = Vec::new();
    let mut next_id: VarId = 0;
    let mut fresh = |vis: Visibility, variables: &mut Vec<Variable>| {
        let id = next_id;
        next_id += 1 + (id % 3 == 2) as u32; // leave id gaps
        variables.push(Variable {
            id,
            name: format!("v{id}"),
            visibility: vis,
        });
        id
    };
    for k in 0..6 {
        let vis = if k % 2 == 0 {
            Visibility::Public
        } else {
            Visibility::Private
        };
        let id = fresh(vis, &mut variables);
        assign.insert(id, Fr::from(r.gen_range(0..1000u64)));
        live.push(id);
    }
    let mut constraints = Vec::new();
    let rand_coeff = |r: &mut ChaCha20Rng| -> FieldConst {
        match r.gen_range(0..4) {
            0 => FieldConst::from_i64(1),
            1 => FieldConst::from_i64(-(r.gen_range(1..5i64))),
            2 => FieldConst::from_i64(r.gen_range(2..100i64)),
            _ => fc_of(Fr::rand(r)),
        }
    };
    let lc = |r: &mut ChaCha20Rng, live: &[VarId]| -> LinearCombination {
        let mut terms = Vec::new();
        for _ in 0..r.gen_range(1..4) {
            terms.push(Term {
                coeff: rand_coeff(r),
                var: live[r.gen_range(0..live.len())],
            });
        }
        let constant = if r.gen_bool(0.3) {
            rand_coeff(r)
        } else {
            FieldConst::zero()
        };
        LinearCombination { constant, terms } // deliberately not simplified
    };
    let eval = |lc: &LinearCombination, assign: &BTreeMap<VarId, Fr>| -> Fr {
        let f = |c: &FieldConst| xark_prover::fr_from_fieldconst(c);
        lc.terms
            .iter()
            .fold(f(&lc.constant), |acc, t| acc + f(&t.coeff) * assign[&t.var])
    };
    for i in 0..n_cons {
        let a = lc(&mut r, &live);
        let b = lc(&mut r, &live);
        // A late public input / an unreferenced var, interleaved with internals.
        if i % 7 == 3 {
            let id = fresh(Visibility::Public, &mut variables);
            assign.insert(id, Fr::from(i as u64 + 11));
            live.push(id);
        }
        if i % 11 == 5 {
            let id = fresh(Visibility::Internal, &mut variables);
            assign.insert(id, Fr::from(99u64));
        }
        let t = fresh(Visibility::Internal, &mut variables);
        // c = k·t + (other) with t solved so the row holds.
        let other = lc(&mut r, &live);
        let k = Fr::from(r.gen_range(1..9u64));
        let tv = (eval(&a, &assign) * eval(&b, &assign) - eval(&other, &assign)) / k;
        assign.insert(t, tv);
        let mut c = other;
        c.terms.push(Term {
            coeff: fc_of(k),
            var: t,
        });
        constraints.push(R1csConstraint::general(i as u32, a, b, c, ""));
        live.push(t);
    }
    (
        R1csProgram {
            field: FieldSpec::bn254(),
            variables,
            constraints,
        },
        assign,
    )
}

fn ark_cs(prog: &R1csProgram, assign: &BTreeMap<VarId, Fr>) -> ConstraintSystemRef<Fr> {
    let cs = ConstraintSystem::<Fr>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    cs.set_mode(SynthesisMode::Prove {
        construct_matrices: true,
        generate_lc_assignments: false,
    });
    ArkCircuit::of(&XarkCircuit::for_proving_preminimized(
        prog.clone(),
        assign.clone(),
    ))
    .generate_constraints(cs.clone())
    .unwrap();
    cs.finalize();
    cs
}

/// A row as a canonical sparse map (duplicates merged, zeros dropped).
fn canon(terms: impl IntoIterator<Item = (usize, Fr)>) -> BTreeMap<usize, Fr> {
    let mut m = BTreeMap::new();
    for (c, k) in terms {
        *m.entry(c).or_insert_with(Fr::zero) += k;
    }
    m.retain(|_, v| !v.is_zero());
    m
}

fn assert_same_matrices<S: ConstraintSource>(src: &S, cs: &ConstraintSystemRef<Fr>) {
    let mats = &cs.to_matrices().unwrap()[R1CS_PREDICATE_LABEL];
    assert_eq!(src.num_constraints(), cs.num_constraints());
    let mut chunk = RowChunk::default();
    let mut seen = 0;
    for w in src.windows(5) {
        src.expand(&w, &mut chunk);
        assert_eq!(chunk.first_row, w.rows.start);
        for i in 0..chunk.rows() {
            let row = w.rows.start + i;
            for (m, mat) in mats.iter().enumerate() {
                let (cols, ks) = chunk.terms(i, m);
                let ours = canon(cols.iter().map(|&c| c as usize).zip(ks.iter().copied()));
                let theirs = canon(mat[row].iter().map(|(k, c)| (*c, *k)));
                assert_eq!(ours, theirs, "row {row} matrix {m}");
            }
            seen += 1;
        }
    }
    assert_eq!(seen, src.num_constraints());
}

fn full_assignment(cs: &ConstraintSystemRef<Fr>) -> Vec<Fr> {
    let mut z = cs.instance_assignment().unwrap().to_vec();
    z.extend(cs.witness_assignment().unwrap().iter().copied());
    z
}

#[test]
fn ordering_contract_matches_arkworks_allocation() {
    for seed in 0..6 {
        let (prog, assign) = random_program(seed, 40 + seed as usize * 17);
        let cs = ark_cs(&prog, &assign);
        let src = ProgramSource::new(&prog);
        let l = src.layout();
        assert_eq!(l.num_instance(), cs.num_instance_variables());
        assert_eq!(l.num_witness(), cs.num_witness_variables());
        assert_eq!(
            l.assignment_from_map(&assign),
            full_assignment(&cs),
            "seed {seed}"
        );
        assert_same_matrices(&src, &cs);
    }
}

#[test]
fn h_is_bit_identical_to_arkworks_witness_map() {
    for seed in 10..16 {
        let (prog, assign) = random_program(seed, 30 + 41 * (seed as usize - 10));
        let cs = ark_cs(&prog, &assign);
        let want = LibsnarkReduction::witness_map::<Fr, GeneralEvaluationDomain<Fr>>(cs).unwrap();
        let src = ProgramSource::new(&prog);
        let z = src.layout().assignment_from_map(&assign);
        for (cfg, rows) in [
            (FftConfig::default(), 1 << 14),
            (
                FftConfig {
                    tile: 3,
                    min_blocked_log: 1,
                },
                7,
            ),
            (
                FftConfig {
                    tile: 16,
                    min_blocked_log: 4,
                },
                1,
            ),
        ] {
            assert_eq!(
                qap::witness_map(&src, &z, cfg, rows),
                want,
                "seed {seed} {cfg:?}"
            );
        }
    }
}

fn pk_bytes(pk: &ProvingKey<Bn254>, compress: Compress, header: bool) -> Vec<u8> {
    let mut out = Vec::new();
    if header {
        // v2: the QAP domain size follows the mode byte.
        out.extend_from_slice(b"XKPK");
        out.push(2);
        out.push(matches!(compress, Compress::No) as u8);
        out.extend_from_slice(&(pk.h_query.len() as u64 + 1).to_le_bytes());
    }
    pk.serialize_with_mode(&mut out, compress).unwrap();
    out
}

#[test]
fn proof_is_byte_identical_to_arkworks_and_verifies() {
    for seed in 20..24u64 {
        let (prog, assign) = random_program(seed, 60 + 33 * (seed as usize - 20));
        let circ = XarkCircuit::for_proving_preminimized(prog.clone(), assign.clone());
        let public = circ.public_inputs();
        let (pk, vk) =
            ArkG16::circuit_specific_setup(circ.clone(), &mut ChaCha20Rng::seed_from_u64(seed))
                .unwrap();
        let want = ArkG16::prove(&pk, circ, &mut ChaCha20Rng::seed_from_u64(seed + 1)).unwrap();

        let src = ProgramSource::new(&prog);
        let z = src.layout().assignment_from_map(&assign);
        let cfgs = [
            ProverConfig::default(),
            ProverConfig {
                rows_per_window: 3,
                msm_chunk: 5,
                fft: FftConfig {
                    tile: 2,
                    min_blocked_log: 1,
                },
                self_check: true,
                spill_dir: None,
                domain: None,
            },
        ];
        for cfg in &cfgs {
            let got = prove(
                &src,
                &z,
                &mut InMemoryPk::new(&pk),
                &mut ChaCha20Rng::seed_from_u64(seed + 1),
                cfg,
            )
            .unwrap();
            assert_eq!(got, want, "seed {seed} in-memory {cfg:?}");
            for (compress, header) in [
                (Compress::Yes, true),
                (Compress::No, true),
                (Compress::Yes, false),
            ] {
                let bytes = pk_bytes(&pk, compress, header);
                let mut spk = SerializedPk::from_bytes(&bytes).unwrap();
                let got = prove(
                    &src,
                    &z,
                    &mut spk,
                    &mut ChaCha20Rng::seed_from_u64(seed + 1),
                    cfg,
                )
                .unwrap();
                assert_eq!(
                    got,
                    want,
                    "seed {seed} serialized compressed={} header={header}",
                    matches!(compress, Compress::Yes)
                );
            }
        }
        assert!(ArkG16::verify(&vk, &public, &want).unwrap());
    }
}

#[test]
fn reordering_variables_breaks_the_proof() {
    let (prog, assign) = random_program(30, 80);
    let circ = XarkCircuit::for_proving_preminimized(prog.clone(), assign.clone());
    let (pk, _) = ArkG16::circuit_specific_setup(circ, &mut ChaCha20Rng::seed_from_u64(1)).unwrap();

    // Swap the ids of two internal variables everywhere (rows + witness): the
    // relabelled system is still satisfied, but positions no longer match the key.
    let internals: Vec<VarId> = prog
        .variables
        .iter()
        .filter(|v| v.visibility == Visibility::Internal)
        .map(|v| v.id)
        .collect();
    let (x, y) = (internals[3], internals[internals.len() - 2]);
    let swap = |v: VarId| {
        if v == x {
            y
        } else if v == y {
            x
        } else {
            v
        }
    };
    let mut bad = prog.clone();
    for c in &mut bad.constraints {
        for lc in [&mut c.a, &mut c.b, &mut c.c] {
            for t in &mut lc.terms {
                t.var = swap(t.var);
            }
        }
    }
    let bad_assign: BTreeMap<VarId, Fr> = assign.iter().map(|(&k, &v)| (swap(k), v)).collect();
    let src = ProgramSource::new(&bad);
    let z = src.layout().assignment_from_map(&bad_assign);
    // Rows still hold under the relabelled witness …
    let m = src.num_constraints();
    let (mut a, mut b, mut c) = (
        vec![Fr::zero(); m],
        vec![Fr::zero(); m],
        vec![Fr::zero(); m],
    );
    eval_rows(&src, &z, 16, [Some(&mut a), Some(&mut b), Some(&mut c)]);
    assert!((0..m).all(|i| a[i] * b[i] == c[i]));
    // … but the proof against the original key fails.
    let res = prove(
        &src,
        &z,
        &mut InMemoryPk::new(&pk),
        &mut ChaCha20Rng::seed_from_u64(2),
        &ProverConfig::default(),
    );
    assert!(matches!(res, Err(ProveError::SelfCheckFailed)), "{res:?}");
    // Which `first_unsatisfied` tells apart from a bad witness.
    assert_eq!(first_unsatisfied(&src, &z), None);
}

#[test]
fn first_unsatisfied_finds_the_failing_row() {
    let (prog, assign) = random_program(32, 60);
    let src = ProgramSource::new(&prog);
    let mut z = src.layout().assignment_from_map(&assign);
    assert_eq!(first_unsatisfied(&src, &z), None);
    // Break one value: the first row reading it is reported.
    let pos = z.len() - 1;
    z[pos] += Fr::from(1u64);
    let row = first_unsatisfied(&src, &z).expect("a row must fail");
    let mut chunk = RowChunk::default();
    let mut found = None;
    for w in src.windows(1 << 14) {
        src.expand(&w, &mut chunk);
        for i in 0..chunk.rows() {
            if found.is_none()
                && chunk.eval(i, 0, &z) * chunk.eval(i, 1, &z) != chunk.eval(i, 2, &z)
            {
                found = Some(w.rows.start + i);
            }
        }
    }
    assert_eq!(Some(row), found);

    // The prover reports that row, rather than blaming the key.
    let circ = XarkCircuit::for_proving_preminimized(prog.clone(), assign.clone());
    let (pk, _) = ArkG16::circuit_specific_setup(circ, &mut ChaCha20Rng::seed_from_u64(1)).unwrap();
    let res = prove(
        &src,
        &z,
        &mut InMemoryPk::new(&pk),
        &mut ChaCha20Rng::seed_from_u64(2),
        &ProverConfig::default(),
    );
    assert!(
        matches!(res, Err(ProveError::Unsatisfied { row: r }) if r == row),
        "{res:?}"
    );
}

#[test]
fn key_shape_mismatch_is_reported() {
    let (p1, a1) = random_program(40, 30);
    let (p2, _) = random_program(41, 90);
    let (pk, _) = ArkG16::circuit_specific_setup(
        XarkCircuit::for_proving_preminimized(p2, BTreeMap::new()),
        &mut ChaCha20Rng::seed_from_u64(1),
    )
    .unwrap();
    let src = ProgramSource::new(&p1);
    let z = src.layout().assignment_from_map(&a1);
    let res = prove(
        &src,
        &z,
        &mut InMemoryPk::new(&pk),
        &mut ChaCha20Rng::seed_from_u64(2),
        &ProverConfig::default(),
    );
    assert!(matches!(res, Err(ProveError::KeyMismatch(_))), "{res:?}");
}

// ---- real circuit: the zkyc bytecode -------------------------------------------

const KYC_XBC: &[u8] = include_bytes!("fixtures/zkyc.xbc");
const KYC_INPUTS: &[(&str, &str)] = &[
    ("user.id", "3762531230650282305"),
    ("user.dob", "19900101"),
    ("user.country", "21333"),
    (
        "user.nonce",
        "19936779879691237274002660607916719351584240970753106546067638544925981619983",
    ),
    ("max_dob", "20200101"),
    (
        "commitment",
        "12878865688106088761792099203939159416017581602557940089653423899691492680101",
    ),
];

fn kyc_witness() -> BTreeMap<VarId, Fr> {
    let cp = xark_ir::function_decode::expand_function_blob(KYC_XBC).unwrap();
    let prim = cp.to_primitive();
    let names: BTreeMap<String, String> = KYC_INPUTS
        .iter()
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .collect();
    let ids = xark_prover::resolve_input_ids(&prim.vars, &names).unwrap();
    let fp = xark_ir::solver::solve_and_check(&prim, &ids).unwrap();
    xark_prover::lower_witness(&fp)
}

#[test]
fn bytecode_rows_equal_the_reduced_expansion() {
    let reduced = xark_ir::function_decode::expand_function_blob_reduced(KYC_XBC)
        .unwrap()
        .into_r1cs();
    let src = BytecodeSource::new(KYC_XBC).unwrap();
    let flat = ProgramSource::new(&reduced);
    assert_eq!(src.num_constraints(), reduced.constraints.len());
    let assign = kyc_witness();
    assert_eq!(
        src.layout().assignment_from_map(&assign),
        flat.layout().assignment_from_map(&assign)
    );
    let cs = ark_cs(&reduced, &assign);
    assert_same_matrices(&src, &cs);
    let stream = xark_ir::function_decode::ReducedRowStream::new(KYC_XBC).unwrap();
    let ids: BTreeSet<VarId> = stream.vars().iter().map(|v| v.0).collect();
    let want: BTreeSet<VarId> = reduced.variables.iter().map(|v| v.id).collect();
    assert_eq!(ids, want);
}

#[test]
fn bytecode_streamed_proof_matches_arkworks() {
    let assign = kyc_witness();
    let reduced = xark_ir::function_decode::expand_function_blob_reduced(KYC_XBC)
        .unwrap()
        .into_r1cs();
    // (a) keyed to the template-reduced circuit: streamed straight from bytecode.
    // (b) keyed to the boundary-minimized circuit (today's `xark setup`).
    let minimized = XarkCircuit::for_setup(reduced.clone()).prog().clone();
    for (label, prog) in [("reduced", &reduced), ("minimized", &minimized)] {
        let circ = XarkCircuit::for_proving_preminimized(prog.clone(), assign.clone());
        let (pk, vk) =
            ArkG16::circuit_specific_setup(circ.clone(), &mut ChaCha20Rng::seed_from_u64(9))
                .unwrap();
        let want = ArkG16::prove(&pk, circ.clone(), &mut ChaCha20Rng::seed_from_u64(10)).unwrap();
        assert!(ArkG16::verify(&vk, &circ.public_inputs(), &want).unwrap());
        let got = if label == "reduced" {
            let src = BytecodeSource::new(KYC_XBC).unwrap();
            let z = src.layout().assignment_from_map(&assign);
            prove(
                &src,
                &z,
                &mut InMemoryPk::new(&pk),
                &mut ChaCha20Rng::seed_from_u64(10),
                &ProverConfig::default(),
            )
        } else {
            let src = ProgramSource::new(prog);
            let z = src.layout().assignment_from_map(&assign);
            prove(
                &src,
                &z,
                &mut InMemoryPk::new(&pk),
                &mut ChaCha20Rng::seed_from_u64(10),
                &ProverConfig::default(),
            )
        }
        .unwrap();
        assert_eq!(got, want, "{label}");
    }
}

// ---- the worker decomposition, natively -------------------------------------------

/// Mimics the JS worker pool step-for-step: column passes as gathered row-major
/// tiles through `kernel_cols`, row passes as row blocks through `kernel_rows`
/// (barriers between), MSM chunks split into `parts` sub-MSMs via `kernel_msm`
/// over raw bytes, partial sums concatenated.
struct FakePool {
    tile: usize,
    rows_per_job: usize,
    parts: usize,
    calls: usize,
    /// FFT chains run (to_coset + from_coset_to_t): 4 per quotient.
    ffts: usize,
}

impl FakePool {
    fn cols(&self, dom: &xark_groth16::Domain, buf: &mut [Fr], op: xark_groth16::fft::ColOp) {
        let (n1, n2) = (dom.n1, dom.n2);
        let mut c0 = 0;
        while c0 < n2 {
            let b = self.tile.min(n2 - c0);
            let mut block: Vec<Fr> = (0..n1)
                .flat_map(|r| buf[r * n2 + c0..r * n2 + c0 + b].to_vec())
                .collect();
            xark_groth16::accel::kernel_cols(dom, &mut block, c0, op);
            for r in 0..n1 {
                buf[r * n2 + c0..r * n2 + c0 + b].copy_from_slice(&block[r * b..(r + 1) * b]);
            }
            c0 += b;
        }
    }
    fn rows(&self, dom: &xark_groth16::Domain, buf: &mut [Fr], to_coset: bool) {
        for (i, rows) in buf.chunks_mut(dom.n2 * self.rows_per_job).enumerate() {
            xark_groth16::accel::kernel_rows(dom, rows, i * self.rows_per_job, to_coset);
        }
    }
}

impl xark_groth16::Accelerator for FakePool {
    fn to_coset(&mut self, dom: &xark_groth16::Domain, buf: &mut [Fr]) -> bool {
        use xark_groth16::fft::ColOp;
        if !dom.is_blocked() {
            return false;
        }
        self.calls += 1;
        self.ffts += 1;
        self.cols(dom, buf, ColOp::InversePost);
        self.rows(dom, buf, true);
        self.cols(dom, buf, ColOp::ForwardPre);
        true
    }
    fn from_coset_to_t(&mut self, dom: &xark_groth16::Domain, buf: &mut [Fr]) -> bool {
        if !dom.is_blocked() {
            return false;
        }
        self.calls += 1;
        self.ffts += 1;
        self.cols(dom, buf, xark_groth16::fft::ColOp::InversePost);
        self.rows(dom, buf, false);
        true
    }
    fn wants_msm(&self) -> bool {
        true
    }
    fn msm(
        &mut self,
        g2: bool,
        points: &[u8],
        compressed: bool,
        scalars: &[xark_groth16::msm::Scalar],
    ) -> Option<Vec<u8>> {
        self.calls += 1;
        let n = scalars.len();
        let sz = points.len() / n;
        let per = n.div_ceil(self.parts);
        let mut out = Vec::new();
        for (k, sc) in scalars.chunks(per).enumerate() {
            let pts = &points[k * per * sz..(k * per + sc.len()) * sz];
            out.extend(xark_groth16::accel::kernel_msm(
                g2,
                pts,
                compressed,
                &xark_groth16::accel::scalars_to_bytes(sc),
            ));
        }
        Some(out)
    }
}

#[test]
fn worker_decomposition_is_byte_identical() {
    let (prog, assign) = random_program(50, 700);
    let circ = XarkCircuit::for_proving_preminimized(prog.clone(), assign.clone());
    let (pk, _) =
        ArkG16::circuit_specific_setup(circ.clone(), &mut ChaCha20Rng::seed_from_u64(3)).unwrap();
    let want = ArkG16::prove(&pk, circ, &mut ChaCha20Rng::seed_from_u64(4)).unwrap();
    let src = ProgramSource::new(&prog);
    let z = src.layout().assignment_from_map(&assign);
    let mut rng = ChaCha20Rng::seed_from_u64(4);
    let (r, s) = (Fr::rand(&mut rng), Fr::rand(&mut rng));
    for compress in [Compress::Yes, Compress::No] {
        let bytes = pk_bytes(&pk, compress, true);
        let cfg = ProverConfig {
            msm_chunk: 97,
            fft: FftConfig {
                tile: 5,
                min_blocked_log: 4,
            },
            ..ProverConfig::default()
        };
        let mut pool = FakePool {
            tile: 6,
            rows_per_job: 3,
            parts: 4,
            calls: 0,
            ffts: 0,
        };
        let got = xark_groth16::prove_accelerated(
            &src,
            &z,
            &mut SerializedPk::from_bytes(&bytes).unwrap(),
            r,
            s,
            &cfg,
            &mut (),
            &mut pool,
        )
        .unwrap();
        assert_eq!(got, want);
        assert!(
            pool.calls > 10,
            "accelerator was not exercised ({} calls)",
            pool.calls
        );
    }
}

#[test]
fn row_file_source_matches_arkworks_and_proves() {
    // The minimized KYC circuit (what a plain `xark setup` keys) via r1cs.stream,
    // plus a random program spanning several file windows.
    let reduced = xark_ir::function_decode::expand_function_blob_reduced(KYC_XBC)
        .unwrap()
        .into_r1cs();
    let minimized = XarkCircuit::for_setup(reduced).prog().clone();
    let (rand_prog, rand_assign) = random_program(60, 9000);
    for (prog, assign) in [(minimized, kyc_witness()), (rand_prog, rand_assign)] {
        let src =
            xark_groth16::RowFileSource::new(xark_ir::r1cs_stream::encode("fp", &prog)).unwrap();
        let cs = ark_cs(&prog, &assign);
        assert_eq!(
            src.layout().assignment_from_map(&assign),
            full_assignment(&cs)
        );
        assert_same_matrices(&src, &cs);
        let circ = XarkCircuit::for_proving_preminimized(prog.clone(), assign.clone());
        let (pk, _) =
            ArkG16::circuit_specific_setup(circ.clone(), &mut ChaCha20Rng::seed_from_u64(1))
                .unwrap();
        let want = ArkG16::prove(&pk, circ, &mut ChaCha20Rng::seed_from_u64(2)).unwrap();
        let z = src.layout().assignment_from_map(&assign);
        let got = prove(
            &src,
            &z,
            &mut InMemoryPk::new(&pk),
            &mut ChaCha20Rng::seed_from_u64(2),
            &ProverConfig::default(),
        )
        .unwrap();
        assert_eq!(got, want);
    }
}

#[test]
fn push_prover_any_chunking_matches_arkworks() {
    let (prog, assign) = random_program(70, 900);
    let circ = XarkCircuit::for_proving_preminimized(prog.clone(), assign.clone());
    let (pk, _) =
        ArkG16::circuit_specific_setup(circ.clone(), &mut ChaCha20Rng::seed_from_u64(1)).unwrap();
    let want = ArkG16::prove(&pk, circ, &mut ChaCha20Rng::seed_from_u64(2)).unwrap();
    let src = ProgramSource::new(&prog);
    let z = src.layout().assignment_from_map(&assign);
    let mut rng = ChaCha20Rng::seed_from_u64(2);
    let (r, s) = (Fr::rand(&mut rng), Fr::rand(&mut rng));
    let mut chop = ChaCha20Rng::seed_from_u64(3);
    for (compress, header) in [
        (Compress::Yes, true),
        (Compress::No, true),
        (Compress::Yes, false),
    ] {
        let bytes = pk_bytes(&pk, compress, header);
        for (max_piece, msm_chunk) in [
            (1usize, 7usize),
            (13, 1 << 20),
            (4096, 64),
            (bytes.len(), 1 << 20),
        ] {
            let cfg = ProverConfig {
                msm_chunk,
                ..ProverConfig::default()
            };
            let mut pp =
                xark_groth16::PushProver::new(&src, z.clone(), r, s, cfg, &mut xark_groth16::Local)
                    .unwrap();
            let mut i = 0;
            while i < bytes.len() {
                let n = chop.gen_range(1..=max_piece).min(bytes.len() - i);
                pp.push(&bytes[i..i + n], &mut xark_groth16::Local).unwrap();
                i += n;
            }
            assert!(pp.is_complete());
            assert_eq!(
                pp.finish().unwrap(),
                want,
                "pieces ≤ {max_piece}, chunk {msm_chunk}"
            );
        }
        // Truncated key → clear error, not a bad proof.
        let mut pp = xark_groth16::PushProver::new(
            &src,
            z.clone(),
            r,
            s,
            ProverConfig::default(),
            &mut xark_groth16::Local,
        )
        .unwrap();
        pp.push(&bytes[..bytes.len() - 5], &mut xark_groth16::Local)
            .unwrap();
        assert!(matches!(pp.finish(), Err(ProveError::KeyMismatch(_))));
    }
    // Through the worker decomposition too.
    let bytes = pk_bytes(&pk, Compress::Yes, true);
    let mut pool = FakePool {
        tile: 4,
        rows_per_job: 2,
        parts: 3,
        calls: 0,
        ffts: 0,
    };
    let cfg = ProverConfig {
        msm_chunk: 50,
        fft: FftConfig {
            tile: 4,
            min_blocked_log: 4,
        },
        ..ProverConfig::default()
    };
    let mut pp = xark_groth16::PushProver::new(&src, z.clone(), r, s, cfg, &mut pool).unwrap();
    for piece in bytes.chunks(777) {
        pp.push(piece, &mut pool).unwrap();
    }
    assert_eq!(pp.finish().unwrap(), want);
}

#[test]
fn spilled_quotient_and_proof_are_identical() {
    let (prog, assign) = random_program(80, 1500);
    let src = ProgramSource::new(&prog);
    let z = src.layout().assignment_from_map(&assign);
    let cfg = FftConfig {
        tile: 4,
        min_blocked_log: 4,
    };
    let want = qap::witness_map(&src, &z, cfg, 64);
    let mut mem = xark_groth16::spill::MemSpill::default();
    assert_eq!(qap::witness_map_spilled(&src, &z, cfg, 64, &mut mem), want);
    let dir = std::env::temp_dir();
    let mut file = xark_groth16::spill::FileSpill::new_in(&dir).unwrap();
    assert_eq!(qap::witness_map_spilled(&src, &z, cfg, 64, &mut file), want);

    let circ = XarkCircuit::for_proving_preminimized(prog.clone(), assign.clone());
    let (pk, _) =
        ArkG16::circuit_specific_setup(circ.clone(), &mut ChaCha20Rng::seed_from_u64(1)).unwrap();
    let proof = ArkG16::prove(&pk, circ, &mut ChaCha20Rng::seed_from_u64(2)).unwrap();
    let cfg = ProverConfig {
        spill_dir: Some(dir),
        ..ProverConfig::default()
    };
    let got = prove(
        &src,
        &z,
        &mut InMemoryPk::new(&pk),
        &mut ChaCha20Rng::seed_from_u64(2),
        &cfg,
    )
    .unwrap();
    assert_eq!(got, proof);
}

#[test]
fn compiled_template_evaluation_equals_expansion() {
    let assign = kyc_witness();
    let mut src = BytecodeSource::new(KYC_XBC).unwrap();
    let z = src.layout().assignment_from_map(&assign);
    let m = src.num_constraints();
    let run = |src: &BytecodeSource, rows: usize| {
        let (mut a, mut b, mut c) = (
            vec![Fr::zero(); m],
            vec![Fr::zero(); m],
            vec![Fr::zero(); m],
        );
        eval_rows(src, &z, rows, [Some(&mut a), Some(&mut b), Some(&mut c)]);
        (a, b, c)
    };
    let compiled = run(&src, 37);
    src.set_compiled(false);
    let expanded = run(&src, 37);
    assert_eq!(compiled, expanded);
    // And partial requests (only C) agree.
    src.set_compiled(true);
    let mut c_only = vec![Fr::zero(); m];
    eval_rows(&src, &z, 1 << 14, [None, None, Some(&mut c_only)]);
    assert_eq!(c_only, expanded.2);
}

// ---- streaming setup ---------------------------------------------------------------

fn ark_pk_bytes(prog: &R1csProgram, seed: u64, compress: Compress) -> Vec<u8> {
    let circ = XarkCircuit::for_setup_preminimized(prog.clone());
    let (pk, _) =
        ArkG16::circuit_specific_setup(circ, &mut ChaCha20Rng::seed_from_u64(seed)).unwrap();
    pk_bytes(&pk, compress, true)
}

#[test]
fn dev_setup_is_byte_identical_to_arkworks() {
    // Expansion-based transpose (program source) …
    let (prog, _) = random_program(90, 700);
    for compress in [Compress::Yes, Compress::No] {
        let mut ours = Vec::new();
        let vk = xark_groth16::setup::dev_setup(
            &ProgramSource::new(&prog),
            &mut ChaCha20Rng::seed_from_u64(5),
            &mut ours,
            compress,
            DomainKind::Radix2,
        )
        .unwrap();
        assert_eq!(ours, ark_pk_bytes(&prog, 5, compress));
        let pk = xark_groth16::SerializedPk::from_bytes(&ours).unwrap();
        assert_eq!(xark_groth16::PkSource::header(&pk).vk, vk);
    }
    // … and the compiled-template transpose straight from bytecode.
    let reduced = xark_ir::function_decode::expand_function_blob_reduced(KYC_XBC)
        .unwrap()
        .into_r1cs();
    let src = BytecodeSource::new(KYC_XBC).unwrap();
    let mut ours = Vec::new();
    xark_groth16::setup::dev_setup(
        &src,
        &mut ChaCha20Rng::seed_from_u64(6),
        &mut ours,
        Compress::Yes,
        DomainKind::Radix2,
    )
    .unwrap();
    assert_eq!(ours, ark_pk_bytes(&reduced, 6, Compress::Yes));
    // The streamed key proves.
    let assign = kyc_witness();
    let z = src.layout().assignment_from_map(&assign);
    prove(
        &src,
        &z,
        &mut SerializedPk::from_bytes(&ours).unwrap(),
        &mut ChaCha20Rng::seed_from_u64(7),
        &ProverConfig::default(),
    )
    .unwrap();
}

/// A consistent Powers-of-Tau transcript for 2^power from known (τ, α, β).
fn test_ptau(power: u32) -> xark_backend::ptau::PtauFile {
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::Field;
    let mut r = ChaCha20Rng::seed_from_u64(99);
    let (tau, alpha, beta) = (Fr::rand(&mut r), Fr::rand(&mut r), Fr::rand(&mut r));
    let n = 1usize << power;
    let pows = |k: usize| -> Vec<Fr> { (0..k).map(|i| tau.pow([i as u64])).collect() };
    let g1 = ark_bn254::G1Affine::generator();
    let g2 = ark_bn254::G2Affine::generator();
    let g1s = |s: Vec<Fr>| s.iter().map(|x| (g1 * x).into_affine()).collect::<Vec<_>>();
    xark_backend::ptau::PtauFile {
        power,
        tau_g1: g1s(pows(2 * n - 1)),
        tau_g2: pows(n).iter().map(|x| (g2 * x).into_affine()).collect(),
        alpha_tau_g1: g1s(pows(n).iter().map(|x| *x * alpha).collect()),
        beta_tau_g1: g1s(pows(n).iter().map(|x| *x * beta).collect()),
        beta_g2: (g2 * beta).into_affine(),
    }
}

#[test]
fn phase2_setup_is_byte_identical_to_the_backend() {
    let (prog, _) = random_program(91, 400);
    let src = ProgramSource::new(&prog);
    let n = (prog.constraints.len() + src.layout().num_instance()).next_power_of_two();
    let ptau = test_ptau(n.trailing_zeros());
    let seed = [7u8; 32];
    let (pk, vk) = phase2_ark::setup_from_ptau(
        ArkCircuit::of(&XarkCircuit::for_setup_preminimized(prog.clone())),
        &ptau,
        &seed,
    )
    .unwrap();
    let keys = xark_backend::Groth16Keys {
        proving_key: convert(&pk),
        verifying_key: convert(&vk),
    };
    let dir = std::env::temp_dir().join(format!("xark-phase2-{}", std::process::id()));
    keys.write_proving_key_mode(&dir, Compress::Yes).unwrap();
    let want = std::fs::read(&dir).unwrap();
    let _ = std::fs::remove_file(&dir);
    let powers = xark_groth16::setup::PtauPowers {
        tau_g1: &ptau.tau_g1,
        tau_g2: &ptau.tau_g2,
        alpha_tau_g1: &ptau.alpha_tau_g1,
        beta_tau_g1: &ptau.beta_tau_g1,
        beta_g2: ptau.beta_g2,
    };
    let mut ours = Vec::new();
    let vk =
        xark_groth16::setup::phase2_setup(&src, &powers, &seed, &mut ours, Compress::Yes).unwrap();
    assert_eq!(vk, keys.verifying_key);
    assert_eq!(ours, want);
}

// ---- decoded-key cache -------------------------------------------------------------

/// A `Write` into a shared buffer (so a test can read back a `Box<dyn Write>`).
#[derive(Clone, Default)]
struct SharedBuf(std::sync::Arc<std::sync::Mutex<Vec<u8>>>);
impl std::io::Write for SharedBuf {
    fn write(&mut self, b: &[u8]) -> std::io::Result<usize> {
        self.0.lock().unwrap().extend_from_slice(b);
        Ok(b.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

#[test]
fn transcoding_and_tee_produce_the_uncompressed_key() {
    let (prog, assign) = random_program(100, 500);
    let circ = XarkCircuit::for_proving_preminimized(prog.clone(), assign.clone());
    let (pk, _) = ArkG16::circuit_specific_setup(circ, &mut ChaCha20Rng::seed_from_u64(1)).unwrap();
    let want = pk_bytes(&pk, Compress::No, true);
    let mut chop = ChaCha20Rng::seed_from_u64(5);
    for (input, label) in [
        (pk_bytes(&pk, Compress::Yes, true), "compressed"),
        (pk_bytes(&pk, Compress::Yes, false), "legacy"),
        (want.clone(), "already uncompressed"),
    ] {
        let mut t = xark_groth16::transcode::KeyTranscoder::new(37);
        let mut out = Vec::new();
        let mut i = 0;
        while i < input.len() {
            let n = chop.gen_range(1..=999).min(input.len() - i);
            t.push(&input[i..i + n], &mut xark_groth16::Local).unwrap();
            out.extend(t.take_output());
            i += n;
        }
        assert!(t.is_complete());
        if label == "legacy" {
            // No header, so no stated domain: the output carries a v1 header.
            assert_eq!(&out[..6], b"XKPK\x01\x01", "{label}");
            assert_eq!(out[6..], want[14..], "{label}");
        } else {
            assert_eq!(out, want, "{label}");
        }
    }
    // Through the worker decomposition's decompress hook too.
    let mut t = xark_groth16::transcode::KeyTranscoder::new(64);
    t.push(
        &pk_bytes(&pk, Compress::Yes, true),
        &mut FakePool {
            tile: 4,
            rows_per_job: 2,
            parts: 3,
            calls: 0,
            ffts: 0,
        },
    )
    .unwrap();
    assert_eq!(t.take_output(), want);

    // The tee: proving from the compressed key writes the same uncompressed key.
    let src = ProgramSource::new(&prog);
    let z = src.layout().assignment_from_map(&assign);
    let compressed = pk_bytes(&pk, Compress::Yes, true);
    let mut spk = SerializedPk::from_bytes(&compressed).unwrap();
    let buf = SharedBuf::default();
    spk.tee_uncompressed(Box::new(buf.clone())).unwrap();
    let cfg = ProverConfig {
        msm_chunk: 50,
        ..ProverConfig::default()
    };
    prove(&src, &z, &mut spk, &mut ChaCha20Rng::seed_from_u64(2), &cfg).unwrap();
    assert!(spk.finish_tee().unwrap());
    assert_eq!(*buf.0.lock().unwrap(), want);
}

// ---- smooth (3·2^k / 9·2^k) domains -----------------------------------------------

/// Arkworks' libsnark reduction over a mixed-radix domain — the oracle for keys
/// and proofs made with [`DomainKind::Smooth`].
struct MixedReduction;

impl R1CSToQAP for MixedReduction {
    fn instance_map_with_evaluation<F: ark_ff::PrimeField, D: ark_poly::EvaluationDomain<F>>(
        cs: ConstraintSystemRef<F>,
        t: &F,
    ) -> Result<(Vec<F>, Vec<F>, Vec<F>, F, usize, usize), ark_relations::gr1cs::SynthesisError>
    {
        LibsnarkReduction::instance_map_with_evaluation::<F, ark_poly::MixedRadixEvaluationDomain<F>>(
            cs, t,
        )
    }
    fn witness_map_from_matrices<F: ark_ff::PrimeField, D: ark_poly::EvaluationDomain<F>>(
        matrices: &[ark_relations::gr1cs::Matrix<F>],
        num_inputs: usize,
        num_constraints: usize,
        full_assignment: &[F],
    ) -> ark_relations::gr1cs::Result<Vec<F>> {
        LibsnarkReduction::witness_map_from_matrices::<F, ark_poly::MixedRadixEvaluationDomain<F>>(
            matrices,
            num_inputs,
            num_constraints,
            full_assignment,
        )
    }
    fn h_query_scalars<F: ark_ff::PrimeField, D: ark_poly::EvaluationDomain<F>>(
        max_power: usize,
        t: F,
        zt: F,
        delta_inverse: F,
    ) -> Result<Vec<F>, ark_relations::gr1cs::SynthesisError> {
        LibsnarkReduction::h_query_scalars::<F, D>(max_power, t, zt, delta_inverse)
    }
}

#[test]
fn smooth_domain_keys_and_proofs_match_arkworks_mixed_radix() {
    type Mixed = ark_groth16::Groth16<Bn254, MixedReduction>;
    // One domain of each shape: 3·2^k, 9·2^k, and 2^k.
    let mut shapes = BTreeSet::new();
    for (seed, n_cons) in [(80u64, 600usize), (81, 950), (82, 1700)] {
        let (prog, assign) = random_program(seed, n_cons);
        let src = ProgramSource::new(&prog);
        let want_n = DomainKind::Smooth.size(src.num_constraints() + src.layout().num_instance());
        shapes.insert(want_n >> want_n.trailing_zeros());
        let z = src.layout().assignment_from_map(&assign);
        let circ = XarkCircuit::for_proving_preminimized(prog.clone(), assign.clone());
        let public = circ.public_inputs();

        let mut ours = Vec::new();
        let vk = xark_groth16::setup::dev_setup(
            &src,
            &mut ChaCha20Rng::seed_from_u64(seed),
            &mut ours,
            Compress::Yes,
            DomainKind::Smooth,
        )
        .unwrap();
        let (ark_pk, ark_vk) = Mixed::circuit_specific_setup(
            ArkCircuit::of(&XarkCircuit::for_setup_preminimized(prog.clone())),
            &mut ChaCha20Rng::seed_from_u64(seed),
        )
        .unwrap();
        let (pk, ark_vk): (ProvingKey<Bn254>, VerifyingKey<Bn254>) =
            (convert(&ark_pk), convert(&ark_vk));
        assert_eq!(pk.h_query.len() + 1, want_n, "seed {seed}");
        assert_eq!(
            ours,
            pk_bytes(&pk, Compress::Yes, true),
            "setup bytes, seed {seed}"
        );
        assert_eq!(vk, ark_vk);

        let want: Proof<Bn254> = convert(
            &Mixed::prove(
                &ark_pk,
                ArkCircuit::of(&circ),
                &mut ChaCha20Rng::seed_from_u64(seed + 1),
            )
            .unwrap(),
        );
        assert!(ArkG16::verify(&vk, &public, &want).unwrap());
        let blocked = ProverConfig {
            fft: FftConfig {
                tile: 3,
                min_blocked_log: 2,
            },
            msm_chunk: 97,
            ..ProverConfig::default()
        };
        for cfg in [ProverConfig::default(), blocked.clone()] {
            let got = prove(
                &src,
                &z,
                &mut SerializedPk::from_bytes(&ours).unwrap(),
                &mut ChaCha20Rng::seed_from_u64(seed + 1),
                &cfg,
            )
            .unwrap();
            assert_eq!(got, want, "seed {seed} {cfg:?}");
        }

        // Push proving: with a domain hint; with none (the v2 header states the
        // domain, so `h` is computed once, when it arrives); and from a v1 header
        // (no domain: a radix-2 guess, recomputed when the H length disagrees).
        // `h`'s FFT chains are counted through the fake worker pool.
        let v1: Vec<u8> = [&b"XKPK\x01\x00"[..], &ours[14..]].concat();
        let mut rng = ChaCha20Rng::seed_from_u64(seed + 1);
        let (r, s) = (Fr::rand(&mut rng), Fr::rand(&mut rng));
        let recompute = if want_n.is_power_of_two() { 4 } else { 8 };
        for (hint, pool, key, ffts) in [
            (Some(want_n), false, &ours, 0),
            (None, false, &ours, 0),
            (Some(want_n), true, &ours, 4),
            (None, true, &ours, 4),
            (None, true, &v1, recompute),
        ] {
            let cfg = ProverConfig {
                domain: hint,
                ..blocked.clone()
            };
            let mut fake = FakePool {
                tile: 4,
                rows_per_job: 3,
                parts: 2,
                calls: 0,
                ffts: 0,
            };
            let accel: &mut dyn xark_groth16::Accelerator = if pool {
                &mut fake
            } else {
                &mut xark_groth16::Local
            };
            let mut pp = xark_groth16::PushProver::new(&src, z.clone(), r, s, cfg, accel).unwrap();
            for piece in key.chunks(1000) {
                pp.push(piece, accel).unwrap();
            }
            let tag = format!("push seed {seed} hint {hint:?} pool {pool} v{}", key[4]);
            assert_eq!(pp.finish().unwrap(), want, "{tag}");
            assert_eq!(fake.ffts, ffts, "{tag}: quotient FFT chains");
        }

        // h itself, against arkworks' mixed-radix witness map.
        let cs = ark_cs(&prog, &assign);
        let want_h = MixedReduction::witness_map::<Fr, GeneralEvaluationDomain<Fr>>(cs).unwrap();
        let dom = qap::key_domain(&src, want_n - 1, FftConfig::default()).unwrap();
        let h = qap::quotient(
            &src,
            &z,
            &dom,
            1 << 14,
            &mut xark_groth16::Local,
            None,
            &mut (),
        )
        .unwrap();
        assert_eq!(h.gather(0, h.len(), |x| *x), want_h, "h seed {seed}");
    }
    assert_eq!(shapes, BTreeSet::from([1, 3, 9]));
}

#[test]
fn key_header_versions_parse() {
    use xark_groth16::pk::KeyFormat;
    let v2 = KeyFormat::header(true, Some(9 << 18));
    assert_eq!(v2.len(), 14);
    let f = KeyFormat::parse(&v2, false).unwrap().unwrap();
    assert_eq!(
        (f.compressed, f.domain, f.header_len),
        (true, Some(9 << 18), 14)
    );
    // Partial v2 header: wait for more bytes (or fail at EOF).
    assert!(KeyFormat::parse(&v2[..9], false).unwrap().is_none());
    assert!(KeyFormat::parse(&v2[..9], true).is_err());
    let v1 = KeyFormat::header(false, None);
    let f = KeyFormat::parse(&v1, false).unwrap().unwrap();
    assert_eq!((f.compressed, f.domain, f.header_len), (false, None, 6));
    // Legacy (no magic): compressed, body from byte 0.
    let f = KeyFormat::parse(&[7u8; 20], false).unwrap().unwrap();
    assert_eq!((f.compressed, f.header_len), (true, 0));
    // A future version is refused, not misparsed.
    assert!(KeyFormat::parse(b"XKPK\x03\x00........", false).is_err());
}

/// An `r1cs.stream` holds rows for a `circuit.xbc` it names by file hash (how row
/// files were first marked) or by circuit digest (how setup marks them now, so
/// another build of the circuit, from another Rust version, keeps its rows).
#[test]
fn a_row_file_fits_by_file_hash_or_digest() {
    use xark_ir::function_decode::{row_file_fits, stream_digest_hex};
    let digest = stream_digest_hex(KYC_XBC);
    assert!(row_file_fits(
        "hash-of-this-file",
        "hash-of-this-file",
        KYC_XBC
    ));
    assert!(row_file_fits(&digest, "hash-of-another-build", KYC_XBC));
    assert!(!row_file_fits(
        "hash-of-another-circuit",
        "hash-of-this-file",
        KYC_XBC
    ));
    assert!(!row_file_fits(
        &"0".repeat(32),
        "hash-of-this-file",
        KYC_XBC
    ));
}
