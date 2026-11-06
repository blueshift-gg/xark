//! `xark-groth16` — a streaming Groth16 (BN254) prover.
//!
//! Proves against the **same** proving keys and produces proofs verified by the
//! **same** verifier as the arkworks path, but never materializes the constraint
//! system or the proving key:
//!
//! * [`r1cs`] — the variable-ordering contract ([`r1cs::VarLayout`]) and chunked
//!   row sources: straight from `circuit.xbc` bytecode ([`r1cs::BytecodeSource`])
//!   or from an in-memory program ([`r1cs::ProgramSource`]).
//! * [`msm`] — naive oracle, our Pippenger, and the streaming accumulator.
//! * [`pk`] — chunked proving-key readers (file, bytes, or loaded key).
//! * [`fft`] — blocked four-step FFT with tiled gathers/transposes.
//! * [`qap`] — the quotient polynomial `h`, bit-identical to arkworks'.
//! * [`prover`] — assembles the proof.
//! * [`accel`] — hooks + worker kernels to offload FFT sweeps and MSM chunks.

pub mod accel;
pub mod decode;
pub mod fft;
pub mod keystream;
pub mod msm;
pub mod pk;
pub mod prover;
pub mod push;
pub mod qap;
pub mod r1cs;
pub mod setup;
pub mod solana;
pub mod spill;
pub mod transcode;
pub mod types;

pub use accel::{Accelerator, Local};
pub use fft::{Domain, DomainKind, FftConfig};
pub use pk::{InMemoryPk, PkSource, SerializedPk};
pub use prover::{
    Probe, ProveError, ProverConfig, prove, prove_accelerated, prove_with_randomness,
};
pub use push::PushProver;
pub use r1cs::{
    BytecodeSource, ConstraintSource, ProgramSource, RowFileSource, VarLayout, first_unsatisfied,
};
pub use types::{Proof, ProvingKey, VerifyError, VerifyingKey, verify};
