//! A Schnorr signature over Grumpkin, verified natively: "the holder of `pubkey`
//! signed `msg`". Grumpkin's coordinates are this circuit's field, so the check is
//! two full-width scalar multiplications and a Poseidon2 challenge
//! (`xark_grumpkin::schnorr`), where an Ed25519 signature (`examples/ed25519`) costs
//! ~397k constraints. The signature is private: the proof shows one exists without
//! revealing it.

use xark_grumpkin::prelude::*;
use xark_grumpkin::schnorr::{self, Signature};

#[circuit]
pub fn grumpkin_schnorr(pubkey: Public<Affine>, msg: Public<[Field; 2]>, sig: Private<Signature>) {
    schnorr::verify(pubkey, sig, msg);
}
