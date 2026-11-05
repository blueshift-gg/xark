//! Writes `$OUT_DIR/comb.rs`: the offset points `O` and `H`, `−2^256·(O + H)` (the
//! witness ladders' correction), and the fixed-base comb tables for
//! `2C·G − 2^130·O` (`ecdsa_verify`), from `p256`. Window `j` reads byte `j` of `C`; its
//! entry `v` is `2v·2^{8j}·G + 2^j·H` (with `−2^130·O − (2^32 − 2)·H` added at `j = 0`), so
//! the 32 entries sum to `2C·G − 2^130·O`. `O` and `H` are hash-derived (nobody knows their
//! discrete logs): the first `x = SHA-256(seed ‖ u32be(i)) mod p` on the curve, with even
//! `y`.

use num_bigint::BigUint;
use p256::elliptic_curve::point::DecompressPoint;
use p256::elliptic_curve::sec1::ToEncodedPoint;
use p256::{AffinePoint, ProjectivePoint, Scalar};
use sha2::{Digest, Sha256};
use std::fmt::Write as _;

fn hash_point(seed: &[u8]) -> ProjectivePoint {
    let p = BigUint::parse_bytes(
        b"ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
        16,
    )
    .unwrap();
    for i in 0u32.. {
        let h = Sha256::new()
            .chain_update(seed)
            .chain_update(i.to_be_bytes())
            .finalize();
        let x = BigUint::from_bytes_be(&h) % &p;
        let mut be = [0u8; 32];
        let xb = x.to_bytes_be();
        be[32 - xb.len()..].copy_from_slice(&xb);
        let pt = AffinePoint::decompress(&be.into(), 0u8.into());
        if bool::from(pt.is_some()) {
            return pt.unwrap().into();
        }
    }
    unreachable!()
}

/// `x ‖ y` as sixteen little-endian 32-bit limbs.
fn limbs(p: &ProjectivePoint) -> [u32; 16] {
    let e = p.to_affine().to_encoded_point(false);
    let mut out = [0u32; 16];
    for (k, c) in [e.x().unwrap(), e.y().unwrap()].iter().enumerate() {
        for l in 0..8 {
            out[8 * k + l] = u32::from_be_bytes(c[28 - 4 * l..32 - 4 * l].try_into().unwrap());
        }
    }
    out
}

fn pow2(e: u64) -> Scalar {
    let mut s = Scalar::ONE;
    for _ in 0..e {
        s += s;
    }
    s
}

fn main() {
    let o = hash_point(b"xark secp256r1 offset point");
    let h = hash_point(b"xark secp256r1 comb offset point");
    let mut src = String::new();
    writeln!(src, "/// The offset `O` (`x ‖ y`, 8 × 32-bit limbs each).").unwrap();
    writeln!(src, "pub(crate) const OH: [u32; 16] = {:?};", limbs(&o)).unwrap();
    writeln!(src, "/// The comb offset `H`.").unwrap();
    writeln!(src, "pub(crate) const HH: [u32; 16] = {:?};", limbs(&h)).unwrap();
    writeln!(src, "/// `−2^256·(O + H)`.").unwrap();
    writeln!(
        src,
        "pub(crate) const OFF256N: [u32; 16] = {:?};",
        limbs(&-((o + h) * pow2(256)))
    )
    .unwrap();
    writeln!(src, "/// The comb tables (see `build.rs`).").unwrap();
    writeln!(src, "pub(crate) static COMB: [[[u32; 16]; 256]; 32] = [").unwrap();
    for j in 0..32u64 {
        let base = ProjectivePoint::GENERATOR * pow2(8 * j + 1);
        let mut t = if j == 0 {
            -(o * pow2(130)) - h * (pow2(32) - Scalar::from(2u64))
        } else {
            h * pow2(j)
        };
        src.push('[');
        for _ in 0..256 {
            write!(src, "{:?},", limbs(&t)).unwrap();
            t += base;
        }
        src.push_str("],\n");
    }
    src.push_str("];\n");
    let out = std::path::Path::new(&std::env::var("OUT_DIR").unwrap()).join("comb.rs");
    std::fs::write(out, src).unwrap();
    println!("cargo:rerun-if-changed=build.rs");
}
