#![no_std]

use xark::Public;
use xark_secp256k1::{ecdsa_verify, Fq4, Point4};

// ecdsa_basic: a succinct ZK proof that a **public** secp256k1 ECDSA signature
// verifies. The public key `q`, signature `(r, s)`, and message scalar `e` are all
// public inputs; the Groth16 proof attests they satisfy `R.x mod n == r`, so a
// verifier checks one short proof instead of the full EC verification.
//
// Uses secp256k1's single `ecdsa_verify` (the GLV gadget). Inputs are aggregate
// `Point4`/`Fq4` (4×64-bit-limb field elements), flattening to `q.x.limbs[i]` /
// `q.y.limbs[i]` / `r.limbs[i]` / `s.limbs[i]` / `e.limbs[i]`.
pub fn circuit(q: Public<Point4>, r: Public<Fq4>, s: Public<Fq4>, e: Public<Fq4>) {
    ecdsa_verify(q.x.limbs, q.y.limbs, r.limbs, s.limbs, e.limbs);
}
