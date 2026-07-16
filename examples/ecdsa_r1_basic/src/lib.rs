#![no_std]

use xark::Public;
use xark_secp256r1::{ecdsa_verify, Fq, Point};

// ecdsa_r1_basic: a succinct ZK proof that a **public** secp256r1 (P-256) ECDSA
// signature verifies. The public key `q`, signature `(r, s)`, and message scalar
// `e` are all public inputs. Inputs are aggregate `Point`/`Fq` (3×86-bit-limb
// field elements), flattening to `q.x.limbs[i]` / `r.limbs[i]` / … .
pub fn circuit(q: Public<Point>, r: Public<Fq>, s: Public<Fq>, e: Public<Fq>) {
    ecdsa_verify(q, r, s, e);
}
