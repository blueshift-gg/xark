//! Writes `$OUT_DIR/comb.rs`: the fixed-base comb tables of `eddsa_verify`. Window `j`
//! reads byte `j` of `W`; its entry `v` is `[2v·2^{8j}·4⁻⁶⁵ mod L]·G` as `(x, y, d·x·y)`,
//! each 8 little-endian 32-bit limbs, so the 32 windows sum to `C'' = [2W·4⁻⁶⁵]·G` and
//! the verifier's 65 two-doubling steps take it to `[2W]·G`. Entry `0` is the identity
//! `(0, 1, 0)`; the addition is complete, so it needs no offset. Computed in extended
//! coordinates (Hisil–Wong–Carter–Dawson 2008, `a = −1`) with one batched inversion.

use num_bigint::BigUint;
use std::fmt::Write as _;

fn dec(s: &str) -> BigUint {
    BigUint::parse_bytes(s.as_bytes(), 10).unwrap()
}

struct Curve {
    p: BigUint,
    d: BigUint,
}

/// `(X : Y : Z : T)` with `x = X/Z`, `y = Y/Z`, `x·y = T/Z`.
#[derive(Clone)]
struct Ext([BigUint; 4]);

impl Curve {
    fn m(&self, a: &BigUint, b: &BigUint) -> BigUint {
        a * b % &self.p
    }
    fn s(&self, a: &BigUint, b: &BigUint) -> BigUint {
        (a + &self.p - b) % &self.p
    }
    /// add-2008-hwcd for `a = −1` (complete for Ed25519's non-square `d`).
    fn add(&self, p: &Ext, q: &Ext) -> Ext {
        let [x1, y1, z1, t1] = &p.0;
        let [x2, y2, z2, t2] = &q.0;
        let a = self.m(x1, x2);
        let b = self.m(y1, y2);
        let c = self.m(&self.m(&self.d, t1), t2);
        let dd = self.m(z1, z2);
        let e = self.s(
            &self.m(&((x1 + y1) % &self.p), &((x2 + y2) % &self.p)),
            &((&a + &b) % &self.p),
        );
        let f = self.s(&dd, &c);
        let g = (&dd + &c) % &self.p;
        let h = (&b + &a) % &self.p;
        Ext([
            self.m(&e, &f),
            self.m(&g, &h),
            self.m(&f, &g),
            self.m(&e, &h),
        ])
    }
    fn mul(&self, k: &BigUint, base: &Ext) -> Ext {
        let one = BigUint::from(1u32);
        let mut acc = Ext([BigUint::ZERO, one.clone(), one, BigUint::ZERO]);
        for i in (0..k.bits()).rev() {
            acc = self.add(&acc, &acc);
            if k.bit(i) {
                acc = self.add(&acc, base);
            }
        }
        acc
    }
}

fn limbs(v: &BigUint) -> [u32; 8] {
    let mut out = [0u32; 8];
    for (i, l) in out.iter_mut().enumerate() {
        *l = ((v >> (32 * i)) & BigUint::from(u32::MAX))
            .try_into()
            .unwrap();
    }
    out
}

fn main() {
    let c = Curve {
        p: (BigUint::from(1u32) << 255u32) - 19u32,
        d: dec("37095705934669439343138083508754565189542113879843219016388785533085940283555"),
    };
    let l = dec("7237005577332262213973186563042994240857116359379907606001950938285454250989");
    let (gx, gy) = (
        dec("15112221349535400772501151409588531511454012693041857206046113283949847762202"),
        dec("46316835694926478169428394003475163141307993866256225615783033603165251855960"),
    );
    let g = Ext([gx.clone(), gy.clone(), BigUint::from(1u32), c.m(&gx, &gy)]);
    // 2·4⁻⁶⁵ mod L (L prime: Fermat).
    let inv4_65 = BigUint::from(4u32)
        .modpow(&BigUint::from(65u32), &l)
        .modpow(&(&l - 2u32), &l);
    let mut base = c.mul(&(inv4_65 * 2u32 % &l), &g);
    let one = BigUint::from(1u32);
    let identity = Ext([BigUint::ZERO, one.clone(), one, BigUint::ZERO]);
    let mut pts: Vec<Ext> = Vec::with_capacity(32 * 256);
    for _ in 0..32 {
        let mut e = identity.clone();
        for _ in 0..256 {
            pts.push(e.clone());
            e = c.add(&e, &base);
        }
        for _ in 0..8 {
            base = c.add(&base, &base);
        }
    }
    // Batched inversion of every Z (Montgomery's trick).
    let mut pre = Vec::with_capacity(pts.len());
    let mut acc = BigUint::from(1u32);
    for pt in &pts {
        pre.push(acc.clone());
        acc = c.m(&acc, &pt.0[2]);
    }
    let mut inv = acc.modpow(&(&c.p - 2u32), &c.p);
    let mut zinv = vec![BigUint::ZERO; pts.len()];
    for i in (0..pts.len()).rev() {
        zinv[i] = c.m(&inv, &pre[i]);
        inv = c.m(&inv, &pts[i].0[2]);
    }
    let mut src = String::new();
    writeln!(
        src,
        "/// The comb tables (see `build.rs`): `(x, y, d·x·y)`, 8 × 32-bit limbs each."
    )
    .unwrap();
    writeln!(src, "static COMB: [[[u32; 24]; 256]; 32] = [").unwrap();
    for j in 0..32 {
        writeln!(src, "[").unwrap();
        for v in 0..256 {
            let pt = &pts[256 * j + v];
            let x = c.m(&pt.0[0], &zinv[256 * j + v]);
            let y = c.m(&pt.0[1], &zinv[256 * j + v]);
            let f = c.m(&c.d, &c.m(&x, &y));
            let mut all = Vec::with_capacity(24);
            for w in [&x, &y, &f] {
                all.extend_from_slice(&limbs(w));
            }
            writeln!(src, "{all:?},").unwrap();
        }
        writeln!(src, "],").unwrap();
    }
    writeln!(src, "];").unwrap();
    let out = std::path::Path::new(&std::env::var("OUT_DIR").unwrap()).join("comb.rs");
    std::fs::write(out, src).unwrap();
    println!("cargo::rerun-if-changed=build.rs");
}
