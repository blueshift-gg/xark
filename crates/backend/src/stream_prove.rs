//! **Streaming Groth16 prover** — proves without materializing the proving key.
//!
//! Reproduces ark-groth16's `create_proof_with_reduction`, but runs the five
//! proving-key MSMs (`a`, `b_g1`, `b_g2`, `h`, `l`) by **streaming each query
//! vector from the `pk.bin` file in ~1M-point chunks**, so the multi-GB proving
//! key never fully enters RAM. The h-poly FFT reuses arkworks' `witness_map`
//! unchanged. Peak = witness + h-poly + one chunk, instead of + the whole pk.
//!
//! Correctness is self-guarded: the streamed proof is verified against the
//! embedded `vk` before returning (a bug can only *fail* verification, never
//! forge). Validated end-to-end by `gadgets/tests/tests/end_to_end.rs`
//! (`streaming_prove_verifies`, `uncompressed_key_proves_and_verifies`);
//! measured ~2× lower peak RSS than the full-load path on a 3M-constraint circuit.

use std::fs::File;
use std::io::{Read, Seek, SeekFrom};
use std::path::Path;

use ark_bn254::{Bn254, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{AffineRepr, CurveGroup, scalar_mul::variable_base::VariableBaseMSM};
use ark_ff::{PrimeField, UniformRand, Zero};
use ark_groth16::{
    Proof, VerifyingKey,
    r1cs_to_qap::{LibsnarkReduction, R1CSToQAP},
};
use ark_poly::GeneralEvaluationDomain;
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystem, OptimizationGoal, SynthesisError, SynthesisMode,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
use rand::{CryptoRng, RngCore};
use rayon::prelude::*;

type Bi = <Fr as PrimeField>::BigInt;

/// Errors from [`stream_prove`].
#[derive(Debug)]
pub enum StreamProveError {
    Io(std::io::Error),
    Deserialize(ark_serialize::SerializationError),
    Synthesis(SynthesisError),
    /// The streamed proof did not verify against the key's own `vk` — a bug in
    /// the streaming path or an unsatisfied witness. Never a forgeable state.
    SelfCheckFailed,
}

impl std::fmt::Display for StreamProveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(e) => write!(f, "reading proving key: {e}"),
            Self::Deserialize(e) => write!(f, "parsing proving key: {e}"),
            Self::Synthesis(e) => write!(f, "circuit synthesis: {e}"),
            Self::SelfCheckFailed => write!(f, "streamed proof failed self-verification"),
        }
    }
}
impl std::error::Error for StreamProveError {}

const V: Validate = Validate::No;

fn g1sz(c: Compress) -> usize {
    G1Affine::generator().serialized_size(c)
}
fn g2sz(c: Compress) -> usize {
    G2Affine::generator().serialized_size(c)
}

/// The pk file's on-disk layout: the point-compression mode, the small header
/// points, and the `(offset, len)` of each of the five point vectors. Matches
/// `keys::read_proving_key`'s order (`vk, beta_g1, delta_g1, a, b_g1, b_g2, h,
/// l`), after the optional 6-byte `XKPK` mode header.
struct PkLayout {
    compress: Compress,
    vk: VerifyingKey<Bn254>,
    beta_g1: G1Affine,
    delta_g1: G1Affine,
    a: (u64, usize),
    b_g1: (u64, usize),
    b_g2: (u64, usize),
    h: (u64, usize),
    l: (u64, usize),
}

/// Parse the mode header + record each vector's byte range using seeks — the
/// point data itself is never read here (only lengths), so this is O(1) memory.
fn parse_pk(f: &mut File) -> Result<PkLayout, StreamProveError> {
    let flen = f.metadata().map_err(StreamProveError::Io)?.len();
    let hn = flen.min(1 << 20) as usize;
    let mut hdr = vec![0u8; hn];
    f.read_exact(&mut hdr).map_err(StreamProveError::Io)?;
    // Honor the `XKPK` mode header; a legacy key (no magic) is compressed.
    let (compress, base) = crate::keys::pk_compression(&hdr);
    let base_off = (hn - base.len()) as u64;
    let mut cur: &[u8] = base;
    let de = StreamProveError::Deserialize;
    let vk = VerifyingKey::<Bn254>::deserialize_with_mode(&mut cur, compress, V).map_err(de)?;
    let beta_g1 = G1Affine::deserialize_with_mode(&mut cur, compress, V).map_err(de)?;
    let delta_g1 = G1Affine::deserialize_with_mode(&mut cur, compress, V).map_err(de)?;
    let mut pos = base_off + (base.len() - cur.len()) as u64;
    let mut read_vec = |f: &mut File, is_g2: bool| -> Result<(u64, usize), StreamProveError> {
        f.seek(SeekFrom::Start(pos)).map_err(StreamProveError::Io)?;
        let mut lb = [0u8; 8];
        f.read_exact(&mut lb).map_err(StreamProveError::Io)?;
        let len = u64::from_le_bytes(lb) as usize;
        let data_off = pos + 8;
        pos = data_off
            + (len
                * if is_g2 {
                    g2sz(compress)
                } else {
                    g1sz(compress)
                }) as u64;
        Ok((data_off, len))
    };
    let a = read_vec(f, false)?;
    let b_g1 = read_vec(f, false)?;
    let b_g2 = read_vec(f, true)?;
    let h = read_vec(f, false)?;
    let l = read_vec(f, false)?;
    Ok(PkLayout {
        compress,
        vk,
        beta_g1,
        delta_g1,
        a,
        b_g1,
        b_g2,
        h,
        l,
    })
}

fn read_g1(f: &mut File, off: u64, c: Compress) -> Result<G1Affine, StreamProveError> {
    f.seek(SeekFrom::Start(off)).map_err(StreamProveError::Io)?;
    let mut b = vec![0u8; g1sz(c)];
    f.read_exact(&mut b).map_err(StreamProveError::Io)?;
    G1Affine::deserialize_with_mode(&b[..], c, V).map_err(StreamProveError::Deserialize)
}

fn read_g2(f: &mut File, off: u64, c: Compress) -> Result<G2Affine, StreamProveError> {
    f.seek(SeekFrom::Start(off)).map_err(StreamProveError::Io)?;
    let mut b = vec![0u8; g2sz(c)];
    f.read_exact(&mut b).map_err(StreamProveError::Io)?;
    G2Affine::deserialize_with_mode(&b[..], c, V).map_err(StreamProveError::Deserialize)
}

/// Streamed MSM over `len` G1 points at byte `off` and scalars `sc`. Reads the
/// vector in 2²⁰-point chunks, decompresses each chunk in parallel, MSMs it, and
/// accumulates — peak bases in RAM is one chunk, not the whole vector.
fn stream_msm_g1(
    f: &mut File,
    off: u64,
    len: usize,
    sc: &[Bi],
    c: Compress,
) -> Result<G1Projective, StreamProveError> {
    let sz = g1sz(c);
    f.seek(SeekFrom::Start(off)).map_err(StreamProveError::Io)?;
    let step = 1usize << 20;
    let mut buf = vec![0u8; step * sz];
    let mut acc = G1Projective::zero();
    let mut i = 0;
    while i < len {
        let this = step.min(len - i);
        f.read_exact(&mut buf[..this * sz])
            .map_err(StreamProveError::Io)?;
        let bases: Vec<G1Affine> = buf[..this * sz]
            .par_chunks(sz)
            .map(|b| G1Affine::deserialize_with_mode(b, c, V).unwrap())
            .collect();
        acc += G1Projective::msm_bigint(&bases, &sc[i..i + this]);
        i += this;
    }
    Ok(acc)
}

fn stream_msm_g2(
    f: &mut File,
    off: u64,
    len: usize,
    sc: &[Bi],
    c: Compress,
) -> Result<G2Projective, StreamProveError> {
    let sz = g2sz(c);
    f.seek(SeekFrom::Start(off)).map_err(StreamProveError::Io)?;
    let step = 1usize << 20;
    let mut buf = vec![0u8; step * sz];
    let mut acc = G2Projective::zero();
    let mut i = 0;
    while i < len {
        let this = step.min(len - i);
        f.read_exact(&mut buf[..this * sz])
            .map_err(StreamProveError::Io)?;
        let bases: Vec<G2Affine> = buf[..this * sz]
            .par_chunks(sz)
            .map(|b| G2Affine::deserialize_with_mode(b, c, V).unwrap())
            .collect();
        acc += G2Projective::msm_bigint(&bases, &sc[i..i + this]);
        i += this;
    }
    Ok(acc)
}

/// Prove `circuit` against the proving key at `pk_path`, streaming the key from
/// disk. `public_inputs` is the public portion of the witness. The proof is
/// self-verified before returning (same guard as [`crate::prove`]).
pub fn stream_prove<Circ, R>(
    pk_path: &Path,
    circuit: Circ,
    public_inputs: &[Fr],
    rng: &mut R,
) -> Result<Proof<Bn254>, StreamProveError>
where
    Circ: ConstraintSynthesizer<Fr>,
    R: RngCore + CryptoRng,
{
    // 1) Synthesize (exactly as ark-groth16's prover) → h-poly + witness.
    let cs = ConstraintSystem::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    cs.set_mode(SynthesisMode::Prove {
        construct_matrices: true,
        generate_lc_assignments: false,
    });
    circuit
        .generate_constraints(cs.clone())
        .map_err(StreamProveError::Synthesis)?;
    cs.finalize();

    let h = LibsnarkReduction::witness_map::<Fr, GeneralEvaluationDomain<Fr>>(cs.clone())
        .map_err(StreamProveError::Synthesis)?;
    let instance = cs
        .instance_assignment()
        .map_err(StreamProveError::Synthesis)?;
    let aux = cs
        .witness_assignment()
        .map_err(StreamProveError::Synthesis)?;

    // Scalars as bigints (the only O(n) `Fr` data kept past this point).
    let h_bi: Vec<Bi> = h.iter().map(|x| x.into_bigint()).collect();
    let aux_bi: Vec<Bi> = aux.iter().map(|x| x.into_bigint()).collect();
    // `assignment` matches `query[1..]`: all vars except the constant `1`.
    let assign_bi: Vec<Bi> = instance[1..]
        .iter()
        .chain(aux.iter())
        .map(|x| x.into_bigint())
        .collect();
    drop(h);
    drop(instance);
    drop(aux);

    let r = Fr::rand(rng);
    let s = Fr::rand(rng);

    // 2) The five MSMs, streamed from the pk file (at the key's compression mode).
    let mut f = File::open(pk_path).map_err(StreamProveError::Io)?;
    let pk = parse_pk(&mut f)?;
    let c = pk.compress;

    let h_acc = stream_msm_g1(&mut f, pk.h.0, pk.h.1, &h_bi, c)?;
    let l_aux_acc = stream_msm_g1(&mut f, pk.l.0, pk.l.1, &aux_bi, c)?;

    // calculate_coeff(initial, query, vk_param) = initial + query[0] + msm(query[1..]) + vk_param
    let coeff_g1 = |f: &mut File,
                    initial: G1Projective,
                    q: (u64, usize),
                    vkp: G1Affine|
     -> Result<G1Projective, StreamProveError> {
        let el = read_g1(f, q.0, c)?;
        let acc = stream_msm_g1(f, q.0 + g1sz(c) as u64, q.1 - 1, &assign_bi, c)?;
        Ok(initial + el + acc + vkp)
    };

    let r_g1 = pk.delta_g1 * r;
    let g_a = coeff_g1(&mut f, r_g1, pk.a, pk.vk.alpha_g1)?;
    let s_g_a = g_a * s;

    let g1_b = if !r.is_zero() {
        let s_g1 = pk.delta_g1 * s;
        coeff_g1(&mut f, s_g1, pk.b_g1, pk.beta_g1)?
    } else {
        G1Projective::zero()
    };

    // B in G2.
    let s_g2 = pk.vk.delta_g2 * s;
    let b_g2_0 = read_g2(&mut f, pk.b_g2.0, c)?;
    let b_g2_acc = stream_msm_g2(
        &mut f,
        pk.b_g2.0 + g2sz(c) as u64,
        pk.b_g2.1 - 1,
        &assign_bi,
        c,
    )?;
    let g2_b = s_g2 + b_g2_0 + b_g2_acc + pk.vk.beta_g2;

    let r_g1_b = g1_b * r;
    let r_s_delta_g1 = pk.delta_g1 * (r * s);
    let mut g_c = s_g_a;
    g_c += r_g1_b;
    g_c -= r_s_delta_g1;
    g_c += l_aux_acc;
    g_c += h_acc;

    let proof = Proof {
        a: g_a.into_affine(),
        b: g2_b.into_affine(),
        c: g_c.into_affine(),
    };

    // 3) Self-check against the embedded vk (correctness guard, see `prove`).
    if !crate::verify::verify(&pk.vk, &proof, public_inputs).map_err(StreamProveError::Synthesis)? {
        return Err(StreamProveError::SelfCheckFailed);
    }
    Ok(proof)
}
