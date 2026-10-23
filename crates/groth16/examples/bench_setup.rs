//! Setup benchmark: the old (synthesize-everything) path vs streaming keygen.
//!
//! ```text
//! bench_setup old-dev|new-dev   <circuit.xbc> <out pk.bin>            # reduced form, seed 7
//! bench_setup old-ptau|new-ptau <circuit.xbc> <out pk.bin> <file.ptau>
//! ```
//! Run each mode in its own process (e.g. under `/usr/bin/time -l`) so peak
//! memory is per path.

use std::io::BufWriter;
use std::time::Instant;

use ark_bn254::Bn254;
use ark_groth16::Groth16;
use ark_serialize::Compress;
use ark_snark::SNARK;

#[path = "../tests/support/ark.rs"]
mod ark;
#[path = "../tests/support/phase2_ark.rs"]
mod phase2_ark;
use ark::{ArkCircuit, convert};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use xark_groth16::BytecodeSource;
use xark_prover::XarkCircuit;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (mode, xbc, out) = (args[1].as_str(), std::fs::read(&args[2]).unwrap(), &args[3]);
    let seed = [11u8; 32];
    let t = Instant::now();
    match mode {
        "old-dev" => {
            let prog = xark_ir::function_decode::expand_function_blob_reduced(&xbc)
                .unwrap()
                .into_r1cs();
            let circ = XarkCircuit::for_setup_preminimized(prog);
            let (pk, vk) = Groth16::<Bn254>::circuit_specific_setup(
                ArkCircuit::of(&circ),
                &mut ChaCha20Rng::seed_from_u64(7),
            )
            .unwrap();
            xark_backend::Groth16Keys {
                proving_key: convert(&pk),
                verifying_key: convert(&vk),
            }
            .write_proving_key_mode(out.as_ref(), Compress::Yes)
            .unwrap();
        }
        "new-dev" => {
            let src = BytecodeSource::new(&xbc).unwrap();
            let f = BufWriter::new(std::fs::File::create(out).unwrap());
            xark_groth16::setup::dev_setup(
                &src,
                &mut ChaCha20Rng::seed_from_u64(7),
                f,
                Compress::Yes,
                if std::env::var("SMOOTH").is_ok() {
                    xark_groth16::DomainKind::Smooth
                } else {
                    xark_groth16::DomainKind::Radix2
                },
            )
            .unwrap();
        }
        "old-ptau" | "new-ptau" => {
            let ptau = xark_backend::ptau::parse_ptau(&std::fs::read(&args[4]).unwrap()).unwrap();
            if mode == "old-ptau" {
                let prog = xark_ir::function_decode::expand_function_blob_reduced(&xbc)
                    .unwrap()
                    .into_r1cs();
                let (pk, vk) = phase2_ark::setup_from_ptau(
                    ArkCircuit::of(&XarkCircuit::for_setup_preminimized(prog)),
                    &ptau,
                    &seed,
                )
                .unwrap();
                let keys = xark_backend::Groth16Keys {
                    proving_key: convert(&pk),
                    verifying_key: convert(&vk),
                };
                keys.write_proving_key_mode(out.as_ref(), Compress::Yes)
                    .unwrap();
            } else {
                let src = BytecodeSource::new(&xbc).unwrap();
                let lay = xark_groth16::ConstraintSource::layout(&src);
                xark_backend::ptau::validate_for_circuit(
                    &ptau,
                    xark_groth16::ConstraintSource::num_constraints(&src),
                    lay.num_instance(),
                )
                .unwrap();
                let powers = xark_groth16::setup::PtauPowers {
                    tau_g1: &ptau.tau_g1,
                    tau_g2: &ptau.tau_g2,
                    alpha_tau_g1: &ptau.alpha_tau_g1,
                    beta_tau_g1: &ptau.beta_tau_g1,
                    beta_g2: ptau.beta_g2,
                };
                let f = BufWriter::new(std::fs::File::create(out).unwrap());
                xark_groth16::setup::phase2_setup(&src, &powers, &seed, f, Compress::Yes).unwrap();
            }
        }
        m => panic!("unknown mode {m}"),
    }
    eprintln!("{mode}: {:.2}s", t.elapsed().as_secs_f64());
}
