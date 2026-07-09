//! `xark-curve`: the shared short-Weierstrass ECDSA gadget, emitted by one
//! `macro_rules!` so `secp256k1` (a = 0) and `secp256r1` (a = −3) are a single
//! source of truth. The two curves differ only in their moduli, the doubling
//! slope numerator (`3x²` vs `3x² − 3`), and the precomputed constant tables.
//!
//! This crate has **no dependencies**: the macro emits absolute `xark_bignum::…` /
//! `xark::…` paths that resolve in the *caller* crate (which must depend on
//! both). Every op the macro emits is token-for-token what the two hand-written,
//! solver-validated gadgets used to contain, so the emitted R1CS is unchanged.

#![no_std]

/// Emit a full short-Weierstrass ECDSA gadget (base/scalar fields, `Point`, the
/// incomplete affine group law, Strauss–Shamir double-scalar-mul, and
/// `ecdsa_verify`) for one curve.
///
/// ```ignore
/// xark_curve::weierstrass! {
///     base = "0x…",              // base field modulus p
///     scalar = "0x…",            // scalar field modulus n
///     a = 0,                     // curve `a` coefficient: `0` or `-3`
///     generators = [             // the four incremental-generator points…
///         [x0, x1, x2, y0, y1, y2],
///         [x0, x1, x2, y0, y1, y2],
///         [x0, x1, x2, y0, y1, y2],
///         [x0, x1, x2, y0, y1, y2],
///     ],
///     correction = [x0, x1, x2, y0, y1, y2],   // the offset-accumulator correction
/// }
/// ```
#[macro_export]
macro_rules! weierstrass {
    // ---- public entry: a = 0 (no `a` term in the doubling numerator) ----
    (
        base = $base:literal,
        scalar = $scalar:literal,
        a = 0,
        b = [ $b0:literal, $b1:literal, $b2:literal ],
        generators = [ $( [ $gx0:literal, $gx1:literal, $gx2:literal, $gy0:literal, $gy1:literal, $gy2:literal ] ),* $(,)? ],
        correction = [ $cx0:literal, $cx1:literal, $cx2:literal, $cy0:literal, $cy1:literal, $cy2:literal $(,)? ] $(,)?
    ) => {
        $crate::weierstrass! { @build
            base = $base,
            scalar = $scalar,
            // a = 0: numerator is exactly `3x²` (NO subtraction).
            numerator_sub = { },
            // On-curve RHS is `x³ + a·x + b` with `a = 0`.
            curve_b = [ $b0, $b1, $b2 ],
            curve_a_coeff = { Fp::new([xark::Field::from(0u8), xark::Field::from(0u8), xark::Field::from(0u8)]) },
            generators = [ $( [ $gx0, $gx1, $gx2, $gy0, $gy1, $gy2 ] ),* ],
            correction = [ $cx0, $cx1, $cx2, $cy0, $cy1, $cy2 ]
        }
    };
    // ---- public entry: a = -3 (numerator gains a `- 3`) ----
    (
        base = $base:literal,
        scalar = $scalar:literal,
        a = -3,
        b = [ $b0:literal, $b1:literal, $b2:literal ],
        generators = [ $( [ $gx0:literal, $gx1:literal, $gx2:literal, $gy0:literal, $gy1:literal, $gy2:literal ] ),* $(,)? ],
        correction = [ $cx0:literal, $cx1:literal, $cx2:literal, $cy0:literal, $cy1:literal, $cy2:literal $(,)? ] $(,)?
    ) => {
        $crate::weierstrass! { @build
            base = $base,
            scalar = $scalar,
            // a = -3: numerator is `3x² - 3` (`Fp` resolves to the type generated
            // below — items are non-hygienic, so this splices in cleanly).
            numerator_sub = { - Fp::new([xark::Field::from(3u8), xark::Field::from(0u8), xark::Field::from(0u8)]) },
            // On-curve RHS is `x³ + a·x + b` with `a = −3` (`−3 = p − 3` via Neg).
            curve_b = [ $b0, $b1, $b2 ],
            curve_a_coeff = { - Fp::new([xark::Field::from(3u8), xark::Field::from(0u8), xark::Field::from(0u8)]) },
            generators = [ $( [ $gx0, $gx1, $gx2, $gy0, $gy1, $gy2 ] ),* ],
            correction = [ $cx0, $cx1, $cx2, $cy0, $cy1, $cy2 ]
        }
    };

    // ---- internal builder: one expansion, so `Point` exists before use ----
    (@build
        base = $base:literal,
        scalar = $scalar:literal,
        numerator_sub = { $($nsub:tt)* },
        curve_b = [ $b0:literal, $b1:literal, $b2:literal ],
        curve_a_coeff = { $($acoeff:tt)* },
        generators = [ $( [ $gx0:literal, $gx1:literal, $gx2:literal, $gy0:literal, $gy1:literal, $gy2:literal ] ),* ],
        correction = [ $cx0:literal, $cx1:literal, $cx2:literal, $cy0:literal, $cy1:literal, $cy2:literal ]
    ) => {
        // Base field `Fp` (mod p) and scalar field `Fq` (mod n), 3 × 86-bit limbs.
        // Only the modulus is written; limbs, `m − 1`, and the complement derive.
        xark_bignum::fp!(pub Fp, $base);
        xark_bignum::fp!(pub Fq, $scalar);

        /// An affine curve point: two base-field (`Fp`) coordinates.
        #[derive(Clone, Copy)]
        pub struct Point {
            pub x: Fp,
            pub y: Fp,
        }
        /// A scalar-field (`Fq`) element — an ECDSA multiplier `u1`/`u2`, `r`, `s`, `e`.
        pub type Scalar = Fq;

        impl Point {
            /// An affine point from its two coordinates.
            pub fn new(x: Fp, y: Fp) -> Self {
                Point { x, y }
            }
            /// A point from six little-endian 86-bit limbs (`x`, then `y`).
            fn from_limbs(x: [xark::Field; 3], y: [xark::Field; 3]) -> Self {
                Point { x: Fp::new(x), y: Fp::new(y) }
            }
            /// Incomplete affine addition, as a `Point` method.
            pub fn add_incomplete(self, q: Point) -> Point {
                ec_add_incomplete(self, q)
            }
            /// Incomplete affine doubling, as a `Point` method.
            pub fn double_incomplete(self) -> Point {
                ec_double_incomplete(self)
            }
        }

        /// Build an `Fp` coordinate from three little-endian 86-bit limbs.
        fn fp(a: u128, b: u128, c: u128) -> Fp {
            Fp::new([xark::Field::from(a), xark::Field::from(b), xark::Field::from(c)])
        }

        /// Pin `p` to the curve `y² = x³ + a·x + b` (range-checks limbs, then the
        /// equation). Required before the incomplete group law.
        pub fn enforce_on_curve(p: Point) {
            p.x.range_check();
            p.y.range_check();
            let b = fp($b0, $b1, $b2);
            let a_coeff = $($acoeff)*;
            // y² == x³ + a·x + b, reduced for an exact per-limb compare
            let lhs = (p.y * p.y).reduce();
            let rhs = (p.x * p.x * p.x + a_coeff * p.x + b).reduce();
            let mut i = 0usize;
            while i < 3usize {
                xark::assert_eq(lhs.limbs[i], rhs.limbs[i]);
                i += 1;
            }
        }

        /// Incomplete affine addition, 3-limb (slope-based, `a`-independent).
        pub fn ec_add_incomplete(p: Point, q: Point) -> Point {
            let dx = q.x - p.x;
            let dy = q.y - p.y;
            let lambda = dy * dx.inverse();
            let lambda_sq = lambda * lambda;
            let x3 = lambda_sq.sub2(p.x, q.x);
            let y3 = lambda * (p.x - x3) - p.y;
            Point::new(x3, y3)
        }

        /// Incomplete affine doubling, 3-limb: `λ = (3x² + a)/(2y)`.
        pub fn ec_double_incomplete(p: Point) -> Point {
            let x_sq = p.x * p.x;
            let three_x_sq = x_sq.triple();
            let num = three_x_sq $($nsub)*;
            let two_y = p.y + p.y;
            let lambda = num * two_y.inverse();
            let lambda_sq = lambda * lambda;
            let x3 = lambda_sq.sub2(p.x, p.x);
            let y3 = lambda * (p.x - x3) - p.y;
            Point::new(x3, y3)
        }

        fn ig1() -> [Point; 4] {
            [
                $( Point::new(fp($gx0, $gx1, $gx2), fp($gy0, $gy1, $gy2)), )*
            ]
        }
        fn neg_k_g() -> Point {
            Point::new(fp($cx0, $cx1, $cx2), fp($cy0, $cy1, $cy2))
        }

        /// Table lookup over 16 affine points by 4 selector bits. Thin `Point`-native
        /// wrapper over `select16_affine` (unwrapping/rewrapping `Fp` is a no-op).
        fn select16(table: [Point; 16], b3: xark::Field, b2: xark::Field, b1: xark::Field, b0: xark::Field) -> Point {
            let mut raw = [[[xark::Field::from(0u8); 3]; 2]; 16];
            let mut i = 0usize;
            while i < 16usize {
                raw[i] = [table[i].x.limbs, table[i].y.limbs];
                i += 1;
            }
            let r = xark_bignum::select16_affine(raw, b3, b2, b1, b0);
            Point::from_limbs(r[0], r[1])
        }

        /// Strauss–Shamir `u1·G + u2·Q`, incomplete-affine offset accumulator, 3-limb.
        pub fn double_scalar_mul_incomplete(u1_bits: [xark::Field; 256], u2_bits: [xark::Field; 256], q: Point) -> Point {
            // pin `q` to the curve (also range-checks its limbs)
            enforce_on_curve(q);
            let ig1 = ig1();
            let q2 = q.double_incomplete();
            let jq = [q, q2, q2.add_incomplete(q)];
            let mut table = [Point::new(fp(0, 0, 0), fp(0, 0, 0)); 16];
            let mut i = 0usize;
            while i < 4usize {
                let mut j = 0usize;
                while j < 4usize {
                    table[i * 4 + j] = if j == 0 { ig1[i] } else { ig1[i].add_incomplete(jq[j - 1]) };
                    j += 1;
                }
                i += 1;
            }
            let mut acc = ig1[0];
            let mut win = 0usize;
            while win < 128usize {
                acc = acc.double_incomplete();
                acc = acc.double_incomplete();
                let top = 255 - win * 2;
                let sel = select16(table, u1_bits[top], u1_bits[top - 1], u2_bits[top], u2_bits[top - 1]);
                acc = acc.add_incomplete(sel);
                win += 1;
            }
            acc.add_incomplete(neg_k_g())
        }

        /// ECDSA verification, 3-limb (86-bit) path.
        pub fn ecdsa_verify(q: Point, r: Scalar, s: Scalar, e: Scalar) {
            // canonical `< n`, not just limb-bounded — a non-canonical `s` is
            // signature malleability
            r.assert_canonical();
            s.assert_canonical();
            e.assert_canonical();
            // r ≠ 0 (s ≠ 0 already enforced by `s.inverse()` below)
            r.assert_nonzero();
            let s_inv = s.inverse();
            let u1 = e * s_inv;
            let u2 = r * s_inv;
            let rr = double_scalar_mul_incomplete(xark_bignum::scalar_to_bits(u1.limbs), xark_bignum::scalar_to_bits(u2.limbs), q);
            let rx_mod_n = Fq::new(rr.x.limbs).reduce();
            let mut i = 0usize;
            while i < 3usize {
                xark::assert_eq(rx_mod_n.limbs[i], r.limbs[i]);
                i += 1;
            }
        }
    };
}

/// Emit a full twisted-Edwards curve gadget (base/scalar fields, `Point`, the
/// **complete** group law, and a branchless double-and-add `scalar_mul`) for a
/// twisted-Edwards curve with `a = −1`:
///
/// ```text
///   −x² + y² = 1 + d·x²·y²          identity = (0, 1)
/// ```
///
/// Unlike the short-Weierstrass [`weierstrass!`] law, this addition is **complete**
/// (no exceptional cases): it correctly handles the identity and doubling with the
/// exact same formula, so no offset accumulator is needed. `d` must be a
/// non-square (true for Ed25519), which guarantees the denominators `1 ± E` are
/// never zero.
///
/// ```ignore
/// xark_curve::edwards! {
///     base   = "…",   // base field modulus p
///     scalar = "…",   // scalar (group order) L
///     d      = "…",   // the curve constant d
/// }
/// ```
///
/// 256-bit field elements use the standard 3 × 86-bit limb layout (same as the
/// Weierstrass gadgets). Emits: `Fp`, `Fq`, `Point` (with `identity`, `add`,
/// `double`), `Scalar = Fq`, `ec_add`, `ec_double`, and
/// `scalar_mul(bits, p)` — a branchless MSB→LSB double-and-add.
#[macro_export]
macro_rules! edwards {
    (
        base = $base:literal,
        scalar = $scalar:literal,
        d = $d:literal $(,)?
    ) => {
        // Base field `Fp` (mod p) and scalar field `Fq` (mod L), 3 × 86-bit limbs.
        xark_bignum::fp!(pub Fp, $base);
        xark_bignum::fp!(pub Fq, $scalar);

        /// An affine twisted-Edwards point: two base-field (`Fp`) coordinates.
        #[derive(Clone, Copy)]
        pub struct Point {
            pub x: Fp,
            pub y: Fp,
        }
        /// A scalar-field (`Fq`) element.
        pub type Scalar = Fq;

        impl Point {
            /// An affine point from its two coordinates.
            pub fn new(x: Fp, y: Fp) -> Self {
                Point { x, y }
            }
            /// A point from six little-endian 86-bit limbs (`x`, then `y`).
            fn from_limbs(x: [xark::Field; 3], y: [xark::Field; 3]) -> Self {
                Point { x: Fp::new(x), y: Fp::new(y) }
            }
            /// The identity element `(0, 1)`.
            pub fn identity() -> Point {
                identity()
            }
            /// Complete affine addition, as a `Point` method.
            pub fn add(self, q: Point) -> Point {
                ec_add(self, q)
            }
            /// Doubling `2·self` via the dedicated affine doubling (cheaper than
            /// the unified `self + self`).
            pub fn double(self) -> Point {
                ec_double(self)
            }
        }

        /// Build an `Fp` coordinate from three little-endian 86-bit limbs.
        fn fp(a: u128, b: u128, c: u128) -> Fp {
            Fp::new([xark::Field::from(a), xark::Field::from(b), xark::Field::from(c)])
        }

        /// The curve constant `d` as compile-time 86-bit limbs (only the `&str`
        /// literal `$d` is parsed here, in `const`-eval — never in circuit MIR).
        const D_LIMBS: [xark::Field; 3] = xark_bignum::modulus_limbs::<3, 86>($d);
        /// The curve constant `d` as an `Fp` (its limbs are the compile-time const).
        fn d_const() -> Fp {
            Fp::new(D_LIMBS)
        }

        /// Pin `p` to the twisted-Edwards curve `−x² + y² = 1 + d·x²·y²`
        /// (range-checks limbs, then the equation).
        pub fn enforce_on_curve(p: Point) {
            p.x.range_check();
            p.y.range_check();
            let x2 = p.x * p.x;
            let y2 = p.y * p.y;
            // y² − x² == 1 + d·x²·y², reduced for an exact per-limb compare
            let lhs = (y2 - x2).reduce();
            let rhs = (fp(1, 0, 0) + d_const() * (x2 * y2)).reduce();
            let mut i = 0usize;
            while i < 3usize {
                xark::assert_eq(lhs.limbs[i], rhs.limbs[i]);
                i += 1;
            }
        }

        /// The identity element `(0, 1)`.
        pub fn identity() -> Point {
            Point::new(fp(0, 0, 0), fp(1, 0, 0))
        }

        /// Complete twisted-Edwards addition (`a = −1`), 3-limb non-native:
        /// ```text
        ///   A = x1·y2 ; B = y1·x2 ; C = x1·x2 ; D = y1·y2 ; E = d·C·D
        ///   x3 = (A + B) / (1 + E) ; y3 = (D + C) / (1 − E)
        /// ```
        pub fn ec_add(p: Point, q: Point) -> Point {
            let one = fp(1, 0, 0);
            let a = p.x * q.y;
            let b = p.y * q.x;
            let c = p.x * q.x;
            let dd = p.y * q.y;
            let e = d_const() * (c * dd);
            let x3 = (a + b) * (one + e).inverse();
            let y3 = (dd + c) * (one - e).inverse();
            Point::new(x3, y3)
        }

        /// Dedicated affine doubling `2·P` for twisted Edwards `a = −1`. The
        /// unified law would compute `ec_add(p, p)` at 8 non-native muls + 2
        /// inverses; substituting the curve identity `d·x²y² = y² − x² − 1`
        /// eliminates `d` and the cross products, collapsing doubling to just
        /// **5 muls + 2 inverses**:
        /// ```text
        ///   x3 = 2·x·y / (y² − x²)
        ///   y3 = (x² + y²) / (2 + x² − y²)
        /// ```
        /// The doublings dominate a scalar-mul (≈256 per call vs ≈64 adds), so
        /// dropping 3 muls each is the main constraint saving. Still **complete**:
        /// for a non-square `d` both denominators (`1 + d·x²y²` and `1 − d·x²y²`)
        /// are never zero, and it correctly doubles the identity `(0, 1)`.
        pub fn ec_double(p: Point) -> Point {
            let two = fp(2, 0, 0);
            let xy = p.x * p.y;
            let x_sq = p.x * p.x;
            let y_sq = p.y * p.y;
            let num_x = xy + xy; // 2·x·y
            let den_x = y_sq - x_sq; // y² − x²
            let num_y = x_sq + y_sq; // x² + y²
            let den_y = (two + x_sq) - y_sq; // 2 + x² − y²
            let x3 = num_x * den_x.inverse();
            let y3 = num_y * den_y.inverse();
            Point::new(x3, y3)
        }

        /// Table lookup over 16 affine points by 4 selector bits (`b3` MSB). Thin
        /// `Point`-native wrapper over `select16_affine` (unwrap/rewrap `Fp` is a
        /// no-op). Table index reconstructed as `b3·8 + b2·4 + b1·2 + b0`.
        fn select16(table: [Point; 16], b3: xark::Field, b2: xark::Field, b1: xark::Field, b0: xark::Field) -> Point {
            let mut raw = [[[xark::Field::from(0u8); 3]; 2]; 16];
            let mut i = 0usize;
            while i < 16usize {
                raw[i] = [table[i].x.limbs, table[i].y.limbs];
                i += 1;
            }
            let r = xark_bignum::select16_affine(raw, b3, b2, b1, b0);
            Point::from_limbs(r[0], r[1])
        }

        /// Windowed `[k]·P` over 256 little-endian scalar `bits` (MSB→LSB, 64 nibbles
        /// of 4 bits). Precomputes `table[i] = [i]·P` for `i ∈ 0..16` (`table[0]` is
        /// the identity), then per window does 4 doublings and one 16-way select+add.
        /// The complete law means the running `acc` (starting at the identity) is
        /// always valid — no offset accumulator needed.
        pub fn scalar_mul(bits: [xark::Field; 256], p: Point) -> Point {
            // pin coordinates to < 2^BITS before the non-native group law
            // (`mod_mul` assumes in-range operand limbs, else products wrap `Fr`)
            p.x.range_check();
            p.y.range_check();
            let mut table = [identity(); 16];
            let mut i = 1usize;
            while i < 16usize {
                table[i] = table[i - 1].add(p);
                i += 1;
            }
            let mut acc = identity();
            let mut win = 0usize;
            while win < 64usize {
                acc = acc.double().double().double().double();
                let top = 255 - win * 4;
                let sel = select16(table, bits[top], bits[top - 1], bits[top - 2], bits[top - 3]);
                acc = acc.add(sel);
                win += 1;
            }
            acc
        }

        /// Windowed Strauss–Shamir `[k1]·P1 + [k2]·P2` over two 256-bit little-endian
        /// scalars (MSB→LSB, 128 windows of 2+2 bits). Precomputes the 16-entry
        /// combined table `T[i·4 + j] = [i]·P1 + [j]·P2` (`i, j ∈ 0..4`, `T[0]` the
        /// identity), then per window does 2 doublings and one 16-way select+add.
        /// Complete law → offset-free (no correction term).
        pub fn double_scalar_mul(bits1: [xark::Field; 256], p1: Point, bits2: [xark::Field; 256], p2: Point) -> Point {
            // pin coordinates to < 2^BITS before the non-native group law (see `scalar_mul`)
            p1.x.range_check();
            p1.y.range_check();
            p2.x.range_check();
            p2.y.range_check();
            let jp1 = [p1, p1.double(), p1.double().add(p1)];
            let jp2 = [p2, p2.double(), p2.double().add(p2)];
            let mut table = [identity(); 16];
            let mut i = 0usize;
            while i < 4usize {
                let mut j = 0usize;
                while j < 4usize {
                    table[i * 4 + j] = if i == 0 {
                        if j == 0 { identity() } else { jp2[j - 1] }
                    } else if j == 0 {
                        jp1[i - 1]
                    } else {
                        jp1[i - 1].add(jp2[j - 1])
                    };
                    j += 1;
                }
                i += 1;
            }
            let mut acc = identity();
            let mut win = 0usize;
            while win < 128usize {
                acc = acc.double().double();
                let top = 255 - win * 2;
                let sel = select16(table, bits1[top], bits1[top - 1], bits2[top], bits2[top - 1]);
                acc = acc.add(sel);
                win += 1;
            }
            acc
        }
    };
}
