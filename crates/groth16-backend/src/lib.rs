//! Arkworks Groth16 (BN254) backend driving the lowered ACIR circuit.

pub mod ceremony;
pub mod circuit;
pub mod evm;
pub mod keys;
pub mod proof;
pub mod prove;
pub mod ptau;
pub mod serialization;
pub mod setup;
pub mod setup_phase2;
pub mod solana;
pub mod verify;

pub use circuit::NoirGroth16Circuit;
pub use keys::{Groth16Keys, KeyMetadata};
pub use proof::ProofBundle;
pub use prove::prove;
pub use ptau::{parse_ptau, PtauError, PtauFile};
pub use setup::setup;
pub use verify::verify;

#[cfg(feature = "test-deterministic")]
pub use rand_chacha::ChaCha20Rng;

#[cfg(feature = "test-deterministic")]
pub fn test_rng() -> ChaCha20Rng {
    use rand::SeedableRng;
    ChaCha20Rng::seed_from_u64(0xC0FFEE)
}
