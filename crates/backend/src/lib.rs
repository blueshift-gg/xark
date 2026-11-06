//! Groth16 (BN254) keys, the trusted-setup ceremony (`.ptau` + phase 2), key and
//! proof serialization (including the Solana encoding) and verification for xark
//! circuits. Setup and proving are `xark-groth16`.

pub mod ceremony;
pub mod keys;
pub mod proof;
pub mod ptau;
pub mod serialization;
pub mod solana;
pub mod verify;

pub use keys::{Groth16Keys, KeyMetadata};
pub use proof::ProofBundle;
pub use ptau::{PtauError, PtauFile, parse_ptau};
pub use verify::verify;

#[cfg(feature = "test-deterministic")]
pub use rand_chacha::ChaCha20Rng;

#[cfg(feature = "test-deterministic")]
pub fn test_rng() -> ChaCha20Rng {
    use rand::SeedableRng;
    ChaCha20Rng::seed_from_u64(0xC0FFEE)
}
