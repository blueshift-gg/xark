//! Schnorr signatures over Grumpkin, verified natively.
//!
//! Grumpkin's coordinates are circuit `Field`s, so "this key authorised this message"
//! is two full-width scalar multiplications, one Poseidon2 sponge and a few hundred
//! comparison rows: 5,051 constraints for a two-element message
//! (`examples/grumpkin_schnorr`), where an Ed25519 signature costs ~397k.
//!
//! ## The scheme
//!
//! A key is a scalar `x` in `[1, n)` and its point `P = x·G`, with `n` Grumpkin's
//! group order (BN254's base-field prime, which exceeds the circuit field `r`) and
//! `G = (1, √−16)`, arkworks' generator. A signature on the field elements
//! `m₀ … m_{N−1}` is a point `R` and a scalar `s < n`, and verifies when
//!
//! ```text
//!   s·G = R + e·P,   e = Poseidon2-sponge(IV; R.x, R.y, P.x, P.y, m₀, …, m_{N−1})
//! ```
//!
//! The sponge is `xark_poseidon2`'s (rate 2, capacity 1, absorb by adding, squeeze
//! the first lane) with the capacity lane seeded with
//! `IV = "grumpkin-schnorr"·2⁶⁴ + (4 + N)` (the 16 ASCII bytes read big-endian):
//! `xark_poseidon2::hash` seeds it with the bare length, below 2⁶⁴, so no challenge is
//! a plain hash of the same elements, and the length keeps messages of different `N`
//! apart. Hashing `P` binds the challenge to the key (no key-substitution), hashing
//! `R` is the Fiat–Shamir commitment.
//!
//! ## From a field element to a scalar
//!
//! The digest `e` is a field element, its value in `[0, r)`. Since `r < n`, that
//! integer is already a canonical scalar: the challenge is the digest itself, never
//! reduced, so it ranges over `r` of the `n` scalars (`n − r < 2¹²⁸`, a negligible
//! slice). The circuit has to prove the 254-bit scalar it multiplies by *is* that
//! integer: `wide_scalar_mul` reads two 127-bit limbs, and `lo + hi·2¹²⁷` reaches
//! `2²⁵⁴ > r`, so both `e` and `e + r` would recompose to the digest mod `r`. The
//! limbs are therefore pinned by `lo + hi·2¹²⁷ = e` in the field *and*
//! `lo + hi·2¹²⁷ ≤ r − 1` as an integer, which leaves exactly one pair.
//!
//! ## What the circuit checks
//!
//! * `R` on the curve. Grumpkin has cofactor 1, so every affine point on it is in
//!   the prime-order group: no small-subgroup check is needed, and the identity has
//!   no affine form, so neither `R` nor `P` can be it.
//! * `P` on the curve (inside `wide_scalar_mul`).
//! * `s ≤ n − 1`: otherwise `s` and `s + n` would both verify (malleability).
//! * The challenge limbs as above, then `s·G = R + e·P` with the proven
//!   [`wide_scalar_mul`] and the incomplete [`ec_add`].
//!
//! The incomplete edges refuse, never accept: `s = 0`, `e = 0`, or `R = ±e·P`
//! leave no proof. For an honest signer each has probability about `2⁻²⁵³`.
//!
//! The comparison with `n − 1` and `r − 1` is glue around the proven gadgets (no Lean
//! template); the tests reject `s = n` and `s = n + s'` with otherwise valid
//! signatures.

use crate::{Affine, WideScalar, ec_add, enforce_on_curve, wide_scalar_mul};
use xark::{Field, input, require_eq, witness_begin, witness_end};

/// A Schnorr signature over Grumpkin: the nonce point `R` and the response `s`
/// (a full-width scalar, `< n`). Flattens to `r.x`, `r.y`, `s.limbs`.
#[input]
pub struct Signature {
    pub r: Affine,
    pub s: WideScalar,
}

/// `n − 1`, Grumpkin's group order (BN254's base-field prime) less one, as
/// little-endian 64-bit limbs.
const N1: [u64; 4] = [
    0x3c20_8c16_d87c_fd46,
    0x9781_6a91_6871_ca8d,
    0xb850_45b6_8181_585d,
    0x3064_4e72_e131_a029,
];

/// `r − 1`, the circuit field's prime less one (`Field::to_bits_canonical`'s `R1`).
const R1: [u64; 4] = [
    0x43e1_f593_f000_0000,
    0x2833_e848_79b9_7091,
    0xb850_45b6_8181_585d,
    0x3064_4e72_e131_a029,
];

/// The challenge sponge's capacity seed less the length: the ASCII bytes
/// `grumpkin-schnorr` read big-endian, times `2⁶⁴`.
const CHALLENGE_TAG: &str = "2536515616918176431312993633982807549125869704034432057344";

/// `2¹²⁷`, the weight of a wide scalar's high limb.
const TWO127: &str = "170141183460469231731687303715884105728";

/// Grumpkin's generator `G = (1, √−16)` (arkworks' `G_GENERATOR_X/Y`).
pub fn generator() -> Affine {
    Affine {
        x: Field::from(1u8),
        y: Field::from("17631683881184975370165255887551781615748388533673675138860"),
    }
}

/// The challenge `e` for the nonce point `r`, the key `pubkey` and the message `msg`
/// (see the module docs for the sponge and its seed): `N + 4` elements absorbed two at
/// a time, so `⌈N/2⌉ + 2` permutations.
pub fn challenge<const N: usize>(r: Affine, pubkey: Affine, msg: [Field; N]) -> Field {
    let iv = Field::from(CHALLENGE_TAG) + Field::from((N + 4) as u64);
    let mut state = [r.x, r.y, iv];
    state = xark_poseidon2::poseidon2_perm(state);
    state[0] = state[0] + pubkey.x;
    state[1] = state[1] + pubkey.y;
    state = xark_poseidon2::poseidon2_perm(state);
    let mut i = 0usize;
    while i < N {
        state[0] = state[0] + msg[i];
        if i + 1 < N {
            state[1] = state[1] + msg[i + 1];
        }
        state = xark_poseidon2::poseidon2_perm(state);
        i += 2;
    }
    state[0]
}

/// Require `pubkey`'s Schnorr signature `sig` on `msg`: `s·G = R + e·P` with `e` the
/// [`challenge`], `R` and `P` on the curve and `s` canonical. See the module docs.
pub fn verify<const N: usize>(pubkey: Affine, sig: Signature, msg: [Field; N]) {
    enforce_on_curve([sig.r.x, sig.r.y]);
    let e = challenge(sig.r, pubkey, msg);
    // `wide_scalar_mul` decomposes each limb to 127 bits; the comparisons below read
    // those bits again (the decomposition is shared, no new rows), so they come
    // after it.
    let sg = wide_scalar_mul(sig.s, pinned(generator()));
    require_canonical(sig.s);
    let ew = WideScalar {
        limbs: {
            let [hi, lo] = Field::hint_div_rem(e, Field::from(TWO127));
            [lo, hi]
        },
    };
    let ep = wide_scalar_mul(ew, pubkey);
    require_le_const(ew.limbs, R1);
    require_eq(ew.limbs[0] + ew.limbs[1] * Field::from(TWO127), e);
    let rhs = ec_add([sig.r.x, sig.r.y], [ep.x, ep.y]);
    require_eq(sg.x, rhs[0]);
    require_eq(sg.y, rhs[1]);
}

/// `p` as two witnesses pinned to its coordinates by a linear row each. Passing the
/// constant itself would let the frontend fold `wide_scalar_mul`'s first step (and its
/// on-curve check) into other rows than the proven template's, which `lean-export
/// --coverage` can't match; on witnesses the call is the template on plain plugs. Two
/// rows, which the minimizer removes again.
fn pinned(p: Affine) -> Affine {
    // `1/(1/c)` is a hint of `c`: a fresh witness, where `c` itself would stay a
    // constant (as `mul_add` names a value; the inner inverse is scratch).
    let witness = |c: Field| {
        witness_begin();
        let inv = Field::hint_inverse(c);
        witness_end();
        let w = Field::hint_inverse(inv);
        require_eq(w, c);
        w
    };
    Affine {
        x: witness(p.x),
        y: witness(p.y),
    }
}

/// Require `s < n`, Grumpkin's group order: one encoding per scalar. About 250 rows;
/// none for the bits when `s` went through [`wide_scalar_mul`] first, which made them.
pub fn require_canonical(s: WideScalar) {
    require_le_const(s.limbs, N1);
}

/// Require `lo + hi·2¹²⁷ ≤ c` for limbs below `2¹²⁷`, as integers. MSB first,
/// `all` says the bits so far equal `c`'s (it starts as the constant 1, so the leading
/// steps fold): where `c` has a one, `all` becomes `all·b`; where it has a zero, a set
/// bit under an equal prefix would make the number exceed `c`, so `all·b = 0`. The
/// same walk as `Field::to_bits_canonical` (bellman's `into_bits_le_strict`), over
/// bits that are already boolean. About one row per bit.
fn require_le_const(limbs: [Field; 2], c: [u64; 4]) {
    let lo = limbs[0].to_bits::<127>();
    let hi = limbs[1].to_bits::<127>();
    let mut all = Field::from(1u8);
    let mut i = 254usize;
    while i > 0 {
        i -= 1;
        let b = if i < 127 { lo[i] } else { hi[i - 127] };
        if c[i / 64] >> (i % 64) & 1 == 1 {
            all = all * b;
        } else {
            require_eq(all * b, Field::from(0u8));
        }
    }
}

/// Host side: keys, signing and verification over `ark-grumpkin`, producing the
/// circuit's inputs.
///
/// The nonce is deterministic (as in EdDSA and RFC 6979, so a signer needs no
/// randomness and never repeats a nonce across messages): two lanes squeezed from a
/// Poseidon2 sponge seeded with `"grumpkin-schnorr-nonce"·2⁶⁴ + (4 + N)` over the
/// secret's 127-bit limbs, `P` and the message, `k = (h₀·r + h₁) mod n`. Over
/// `[0, r²)` the reduction's bias is below `n/r² < 2⁻²⁵³`. Poseidon2 keyed by the
/// secret is the PRF; the secret's two limbs make every secret a distinct key.
#[cfg(not(xark))]
pub mod host {
    extern crate std;
    use std::vec;

    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::{BigInteger, PrimeField, Zero};
    pub use ark_grumpkin::{Affine as Point, Fq as Base, Fr as Scalar};
    use xark_poseidon2::native::poseidon2_perm;

    /// The ASCII bytes `grumpkin-schnorr-nonce` read big-endian, times `2⁶⁴`.
    const NONCE_TAG: &str =
        "713965674198258947224194121584630343255430535570141128880906665239511040";

    fn base(decimal: &str) -> Base {
        decimal
            .parse()
            .unwrap_or_else(|_| unreachable!("a canonical constant"))
    }

    /// Absorb `items` two at a time into a sponge whose capacity is `tag + len`.
    fn sponge(tag: &str, items: &[Base]) -> [Base; 3] {
        let mut state = [
            Base::zero(),
            Base::zero(),
            base(tag) + Base::from(items.len() as u64),
        ];
        for pair in items.chunks(2) {
            state[0] += pair[0];
            if let Some(b) = pair.get(1) {
                state[1] += b;
            }
            state = poseidon2_perm(state);
        }
        state
    }

    /// The challenge, natively: [`super::challenge`] on `R`, `P` and `msg`.
    pub fn challenge(r: &Point, pubkey: &Point, msg: &[Base]) -> Base {
        let mut items = vec![r.x, r.y, pubkey.x, pubkey.y];
        items.extend_from_slice(msg);
        sponge(super::CHALLENGE_TAG, &items)[0]
    }

    /// A field element (`< r < n`) as the scalar with the same integer value.
    fn to_scalar(e: Base) -> Scalar {
        Scalar::from_bigint(e.into_bigint()).expect("r < n: every field value is a scalar")
    }

    /// A signature, natively: `(R, s)`.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Signature {
        pub r: Point,
        pub s: Scalar,
    }

    /// A secret key `x ∈ [1, n)` and its public key `x·G`.
    #[derive(Clone, Copy, Debug)]
    pub struct SigningKey {
        secret: Scalar,
        public: Point,
    }

    impl SigningKey {
        /// The key for the secret `x`; `None` for `x = 0`.
        pub fn from_scalar(secret: Scalar) -> Option<SigningKey> {
            if secret.is_zero() {
                return None;
            }
            let public = (Point::generator() * secret).into_affine();
            Some(SigningKey { secret, public })
        }

        /// The key for 32 seed bytes, read big-endian and reduced mod `n`; `None` when
        /// that is 0. `2²⁵⁶ ≈ 5.3·n`, so each key comes from 5 or 6 seeds: uniform
        /// seeds give slightly non-uniform keys (under a bit of entropy lost). Draw a
        /// uniform scalar for [`SigningKey::from_scalar`] where that matters.
        pub fn from_seed(seed: &[u8; 32]) -> Option<SigningKey> {
            SigningKey::from_scalar(Scalar::from_be_bytes_mod_order(seed))
        }

        /// The public key `P = x·G`.
        pub fn public_key(&self) -> Point {
            self.public
        }

        /// Sign `msg` with the deterministic nonce (module docs).
        pub fn sign(&self, msg: &[Base]) -> Signature {
            let be: [u8; 32] = self
                .secret
                .into_bigint()
                .to_bytes_be()
                .try_into()
                .expect("a 32-byte scalar");
            let limb = |lo| Base::from_be_bytes_mod_order(&num_split(&be, lo));
            let mut items = vec![limb(true), limb(false), self.public.x, self.public.y];
            items.extend_from_slice(msg);
            let st = sponge(NONCE_TAG, &items);
            let r = Scalar::from(Base::MODULUS);
            let k = to_scalar(st[0]) * r + to_scalar(st[1]);
            assert!(!k.is_zero(), "a zero nonce (probability 2⁻²⁵³)");
            self.sign_with_nonce(msg, k)
        }

        /// Sign with the nonce `k`. Reusing `k` for two messages reveals the secret,
        /// so only [`SigningKey::sign`] calls it.
        fn sign_with_nonce(&self, msg: &[Base], k: Scalar) -> Signature {
            let r = (Point::generator() * k).into_affine();
            let e = to_scalar(challenge(&r, &self.public, msg));
            Signature {
                r,
                s: k + e * self.secret,
            }
        }
    }

    /// The low (`lo`) or high 127 bits of a 254-bit big-endian number, big-endian.
    fn num_split(be: &[u8; 32], lo: bool) -> [u8; 32] {
        let mut out = [0u8; 32];
        // As a 256-bit number: shift right by 127 for the high half, mask for the low.
        let mut v = [0u64; 4];
        for (i, chunk) in be.rchunks(8).enumerate() {
            v[i] = u64::from_be_bytes(chunk.try_into().expect("8 bytes"));
        }
        let w = if lo {
            [v[0], v[1] & (u64::MAX >> 1), 0, 0]
        } else {
            [
                (v[1] >> 63) | (v[2] << 1),
                (v[2] >> 63) | (v[3] << 1),
                v[3] >> 63,
                0,
            ]
        };
        for (i, limb) in w.iter().enumerate() {
            out[24 - 8 * i..32 - 8 * i].copy_from_slice(&limb.to_be_bytes());
        }
        out
    }

    /// Whether `sig` is `pubkey`'s signature on `msg`: `s·G = R + e·P` with both
    /// points on the curve and not the identity (an arkworks `Scalar` is always
    /// canonical, `< n`).
    pub fn verify(pubkey: &Point, msg: &[Base], sig: &Signature) -> bool {
        let on = |p: &Point| !p.is_zero() && p.is_on_curve();
        if !on(pubkey) || !on(&sig.r) {
            return false;
        }
        let e = to_scalar(challenge(&sig.r, pubkey, msg));
        Point::generator() * sig.s == *pubkey * e + sig.r
    }

    impl From<Point> for crate::Affine {
        fn from(p: Point) -> crate::Affine {
            crate::Affine {
                x: p.x.into(),
                y: p.y.into(),
            }
        }
    }

    /// A scalar as the circuit's [`WideScalar`](crate::WideScalar) (its 127-bit limbs).
    pub fn wide(s: Scalar) -> crate::WideScalar {
        let be: [u8; 32] = s
            .into_bigint()
            .to_bytes_be()
            .try_into()
            .expect("a 32-byte scalar");
        crate::WideScalar::from(be)
    }

    impl From<Signature> for super::Signature {
        fn from(sig: Signature) -> super::Signature {
            super::Signature {
                r: sig.r.into(),
                s: wide(sig.s),
            }
        }
    }
}
