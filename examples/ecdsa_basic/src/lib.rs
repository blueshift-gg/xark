#![no_std]

use xark::Public;
use xark_secp256k1::{ecdsa_verify, Fq, Point};

// ecdsa_basic: a succinct ZK proof that a **public** secp256k1 ECDSA signature
// verifies. The public key `q`, signature `(r, s)`, and message scalar `e` are all
// public inputs; the Groth16 proof attests they satisfy `R.x mod n == r`, so a
// verifier checks one short proof instead of the full EC verification. Inputs are
// aggregate `Point`/`Fq` (3×86-bit-limb field elements), flattening to
// `q.x.limbs[i]` / `q.y.limbs[i]` / `r.limbs[i]` / `s.limbs[i]` / `e.limbs[i]`.
pub fn circuit(q: Public<Point>, r: Public<Fq>, s: Public<Fq>, e: Public<Fq>) {
    ecdsa_verify(q, r, s, e);
}
