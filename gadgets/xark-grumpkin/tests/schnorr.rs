//! `schnorr::verify` end to end: signatures from the host signer (`ark-grumpkin` and
//! `xark-poseidon2`'s native permutation) verify in the circuit, compiled from source
//! and solved by the reference solver; the known-answer vector pins the host signer;
//! each tampering is rejected, the non-canonical `s + n` among them (it multiplies
//! to the same point, so only the range check stops it); and no single variable of
//! an accepted assignment can be changed.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::OnceLock;

use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField};
use num_bigint::BigUint;
use xark_grumpkin::schnorr::host::{self, Base, Point, Scalar, SigningKey};
use xark_ir::primitive::PrimitiveProgram;
use xark_ir::solver::{self, Fp};

type Assign = BTreeMap<u32, Fp>;

const SRC: &str = "#![no_std]\n\
    use xark::{Field, Public};\n\
    use xark_grumpkin::{schnorr, Affine, WideScalar};\n\
    pub fn circuit(px: Public<Field>, py: Public<Field>, rx: Public<Field>, ry: Public<Field>,\n\
      slo: Public<Field>, shi: Public<Field>, m0: Public<Field>, m1: Public<Field>) {\n\
      let sig = schnorr::Signature { r: Affine { x: rx, y: ry }, s: WideScalar { limbs: [slo, shi] } };\n\
      schnorr::verify(Affine { x: px, y: py }, sig, [m0, m1]);\n\
    }\n";

// Known answer: the key from the seed `[7; 32]` signs `[1, 2]` with the
// deterministic nonce (`schnorr::host`), as `schnorr_ref.py` (plain-integer Grumpkin,
// the Python Poseidon2) prints it.
const KAT_PK: (&str, &str) = (
    "16837306250394561469239777106029351707115404698955158566455236435934559288042",
    "8379048664607850163636472482323064983106395318289710541319569979352437560537",
);
const KAT_R: (&str, &str) = (
    "1576218407445449210462149781286961675727750876359252323947749482491620593106",
    "14189880748219679695404688495100071535260695427322392414593643178090111068615",
);
const KAT_S: &str = "997515363115179018794159906157962186091522899114521254024238899579684489601";

fn program() -> &'static PrimitiveProgram {
    static P: OnceLock<PrimitiveProgram> = OnceLock::new();
    P.get_or_init(|| {
        let c = xark_test_harness::compile_source("schnorr", SRC, "bn254");
        assert!(c.status_success, "compile failed: {}", c.stderr);
        c.program()
    })
}

/// The group order `n` and `2¹²⁷`.
fn n() -> BigUint {
    BigUint::from_bytes_be(&Scalar::MODULUS.to_bytes_be())
}

/// A whole number below `2²⁵⁴` as its decimal 127-bit limbs `(lo, hi)`.
fn limbs(v: &BigUint) -> (String, String) {
    let mask = (BigUint::from(1u8) << 127) - 1u8;
    ((v & &mask).to_string(), (v >> 127u32).to_string())
}

fn int(s: Scalar) -> BigUint {
    BigUint::from_bytes_be(&s.into_bigint().to_bytes_be())
}

/// The circuit's inputs: `P`, `R`, `s` as a whole number (so a test can pass one
/// `≥ n`) and the two message elements.
struct Case {
    p: (String, String),
    r: (String, String),
    s: BigUint,
    m: [String; 2],
}

impl Case {
    fn new(p: Point, sig: host::Signature, m: [Base; 2]) -> Case {
        Case {
            p: (p.x.to_string(), p.y.to_string()),
            r: (sig.r.x.to_string(), sig.r.y.to_string()),
            s: int(sig.s),
            m: m.map(|v| v.to_string()),
        }
    }

    fn solve(&self) -> Result<Assign, solver::SolveError> {
        let p = program();
        let id = |name: &str| {
            p.vars
                .iter()
                .find(|v| v.name == name)
                .unwrap_or_else(|| panic!("missing circuit var `{name}`"))
                .id
        };
        let (lo, hi) = limbs(&self.s);
        let inputs = [
            ("px", self.p.0.clone()),
            ("py", self.p.1.clone()),
            ("rx", self.r.0.clone()),
            ("ry", self.r.1.clone()),
            ("slo", lo),
            ("shi", hi),
            ("m0", self.m[0].clone()),
            ("m1", self.m[1].clone()),
        ];
        let inputs = inputs.into_iter().map(|(n, v)| (id(n), v)).collect();
        solver::solve_and_check(p, &inputs)
    }
}

fn key(seed: u8) -> SigningKey {
    SigningKey::from_seed(&[seed; 32]).expect("a nonzero key")
}

fn msg(a: u64, b: u64) -> [Base; 2] {
    [Base::from(a), Base::from(b)]
}

#[test]
fn host_signer_matches_the_known_answer() {
    let sk = key(7);
    let m = msg(1, 2);
    let sig = sk.sign(&m);
    let pk = sk.public_key();
    assert_eq!(
        (pk.x.to_string(), pk.y.to_string()),
        (KAT_PK.0.into(), KAT_PK.1.into())
    );
    assert_eq!(
        (sig.r.x.to_string(), sig.r.y.to_string()),
        (KAT_R.0.into(), KAT_R.1.into())
    );
    assert_eq!(sig.s.to_string(), KAT_S);
    // The equation by hand, apart from `host::verify`.
    let e = Scalar::from_bigint(host::challenge(&sig.r, &pk, &m).into_bigint()).unwrap();
    assert_eq!(
        (Point::generator() * sig.s).into_affine(),
        (sig.r + pk * e).into_affine()
    );
    assert!(host::verify(&pk, &m, &sig));
    assert!(!host::verify(&pk, &msg(1, 3), &sig));
    assert!(!host::verify(&key(8).public_key(), &m, &sig));
    // Deterministic: the same message gets the same signature, another a new nonce.
    assert_eq!(sk.sign(&m), sig);
    assert_ne!(sk.sign(&msg(2, 1)).r, sig.r);
}

/// The generator the circuit multiplies by is arkworks'.
#[test]
fn generator_is_arkworks() {
    let g = Point::generator();
    let c = xark_grumpkin::schnorr::generator();
    assert_eq!(c.x, xark::Field::from(g.x));
    assert_eq!(c.y, xark::Field::from(g.y));
}

#[test]
fn circuit_accepts_host_signatures() {
    let cases: Vec<Case> = (1u8..=4)
        .map(|i| {
            let sk = key(i);
            let m = msg(u64::from(i) * 1000, u64::MAX - u64::from(i));
            Case::new(sk.public_key(), sk.sign(&m), m)
        })
        .collect();
    std::thread::scope(|t| {
        for (i, c) in cases.iter().enumerate() {
            t.spawn(move || {
                c.solve()
                    .unwrap_or_else(|e| panic!("signature {i} rejected: {e:?}"));
            });
        }
    });
    let kat = Case {
        p: (KAT_PK.0.into(), KAT_PK.1.into()),
        r: (KAT_R.0.into(), KAT_R.1.into()),
        s: KAT_S.parse().unwrap(),
        m: ["1".into(), "2".into()],
    };
    assert_no_forgeable_var(program(), &kat.solve().expect("the known answer"));
}

#[test]
fn circuit_rejects_tampering() {
    let sk = key(7);
    let m = msg(1, 2);
    let sig = sk.sign(&m);
    let honest = Case::new(sk.public_key(), sig, m);
    honest.solve().expect("honest signature");

    let other = key(8).public_key();
    let r_plus_g = (sig.r + Point::generator()).into_affine();
    let off = |p: &(String, String)| {
        (
            p.0.clone(),
            (p.1.parse::<BigUint>().unwrap() + 1u8).to_string(),
        )
    };
    let tamper: Vec<(&str, Case)> = vec![
        (
            "wrong key",
            Case {
                p: (other.x.to_string(), other.y.to_string()),
                ..clone(&honest)
            },
        ),
        (
            "wrong message",
            Case {
                m: ["1".into(), "3".into()],
                ..clone(&honest)
            },
        ),
        (
            "tampered R",
            Case {
                r: (r_plus_g.x.to_string(), r_plus_g.y.to_string()),
                ..clone(&honest)
            },
        ),
        (
            "tampered s",
            Case {
                s: &honest.s + 1u8,
                ..clone(&honest)
            },
        ),
        (
            "off-curve R",
            Case {
                r: off(&honest.r),
                ..clone(&honest)
            },
        ),
        (
            "off-curve P",
            Case {
                p: off(&honest.p),
                ..clone(&honest)
            },
        ),
        (
            "s = 0",
            Case {
                s: 0u8.into(),
                ..clone(&honest)
            },
        ),
        (
            "s = n",
            Case {
                s: n(),
                ..clone(&honest)
            },
        ),
    ];
    std::thread::scope(|t| {
        for (what, c) in &tamper {
            t.spawn(move || assert!(c.solve().is_err(), "{what} accepted"));
        }
    });
}

/// `s + n` multiplies `G` to the same point as `s`, so the equation holds: the range
/// check alone rejects it. It needs `s + n < 2²⁵⁴` to fit the limbs, which about a
/// third of signatures meet.
#[test]
fn circuit_rejects_non_canonical_s() {
    let sk = key(7);
    let bound = BigUint::from(1u8) << 254;
    let (m, sig) = (0u64..)
        .map(|i| {
            let m = msg(i, 0);
            (m, sk.sign(&m))
        })
        .find(|(_, sig)| int(sig.s) + n() < bound)
        .unwrap();
    let honest = Case::new(sk.public_key(), sig, m);
    honest.solve().expect("honest signature");
    let shifted = Case {
        s: &honest.s + n(),
        ..clone(&honest)
    };
    assert!(shifted.solve().is_err(), "s + n accepted");
}

/// The comparison `verify` makes of `s` (and, against `r − 1`, of the challenge's
/// limbs) at its edges: `n − 1` passes, `n`, `n + 1` and `2²⁵⁴ − 1` don't.
#[test]
fn require_canonical_at_the_order() {
    let src = "#![no_std]\n\
        use xark::{Field, Public};\n\
        use xark_grumpkin::{schnorr, WideScalar};\n\
        pub fn circuit(lo: Public<Field>, hi: Public<Field>) {\n\
          schnorr::require_canonical(WideScalar { limbs: [lo, hi] });\n\
        }\n";
    let c = xark_test_harness::compile_source("schnorr_canonical", src, "bn254");
    assert!(c.status_success, "compile failed: {}", c.stderr);
    let p = c.program();
    let run = |v: BigUint| {
        let (lo, hi) = limbs(&v);
        let id = |name: &str| p.vars.iter().find(|v| v.name == name).unwrap().id;
        solver::solve_and_check(&p, &[(id("lo"), lo), (id("hi"), hi)].into_iter().collect())
    };
    let one = BigUint::from(1u8);
    run(n() - &one).expect("n − 1");
    run(BigUint::from(0u8)).expect("0");
    run((n() >> 1u32) + &one).expect("(n + 1) / 2");
    for bad in [n(), n() + &one, (one.clone() << 254) - &one] {
        assert!(run(bad.clone()).is_err(), "{bad} accepted");
    }
}

fn clone(c: &Case) -> Case {
    Case {
        p: c.p.clone(),
        r: c.r.clone(),
        s: c.s.clone(),
        m: c.m.clone(),
    }
}

/// Changing any one variable of an accepted assignment breaks a row, but for the
/// witness-only scratch no row reads (as in `vec.rs`).
fn assert_no_forgeable_var(p: &PrimitiveProgram, assign: &Assign) {
    const UNREFERENCED: &str = "no constraint references this variable";
    let scratch: BTreeSet<u32> = solver::analyze_underconstrained(p, assign)
        .into_iter()
        .map(|u| {
            assert_eq!(u.reason, UNREFERENCED, "under-constrained: {u:?}");
            u.var
        })
        .collect();
    let (f1, f2) = (
        solver::fp_from_decimal("12345", p),
        solver::fp_from_decimal("54321", p),
    );
    let vars: Vec<(&u32, &Fp)> = assign.iter().collect();
    let missed: Vec<u32> = std::thread::scope(|t| {
        let chunks: Vec<_> = vars
            .chunks(vars.len().div_ceil(4))
            .map(|chunk| {
                let (f1, f2) = (&f1, &f2);
                let scratch = &scratch;
                t.spawn(move || {
                    let mut forged = assign.clone();
                    let mut missed = Vec::new();
                    for &(&v, honest) in chunk {
                        forged.insert(
                            v,
                            if *honest == *f1 {
                                f2.clone()
                            } else {
                                f1.clone()
                            },
                        );
                        if solver::check(p, &forged).is_ok() && !scratch.contains(&v) {
                            missed.push(v);
                        }
                        forged.insert(v, honest.clone());
                    }
                    missed
                })
            })
            .collect();
        chunks.into_iter().flat_map(|h| h.join().unwrap()).collect()
    });
    assert!(missed.is_empty(), "forgeable vars: {missed:?}");
}
