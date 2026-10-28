//! Adversarial checks of `witness_search`: hand-built edge cases (free variables
//! with non-boolean solution sets, aliases with non-unit coefficients, coefficients
//! around the small/large cutoff, backtracking) and random programs whose verdict is
//! compared with brute-force enumeration.
use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::{One, Zero};
use xark_ir::field::FieldConst;
use xark_ir::primitive::{
    Expression, FieldSpec, LinearTerm, MulTerm, PrimitiveProgram, Var, VarRole,
};
use xark_ir::solver::{check, fp_from_decimal};
use xark_ir::witness_search::{
    Projection, WitnessSearch, search_projection, search_witnesses, search_witnesses_within,
};

/// A derived variable `id = Σ cᵢ·xᵢ + k`.
type Comp = (u32, Vec<(BigInt, u32)>, BigInt);

fn p_bn254() -> BigInt {
    BigInt::parse_bytes(
        b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
        10,
    )
    .unwrap()
}

fn var(id: u32, name: &str, role: VarRole) -> Var {
    Var {
        id,
        name: name.into(),
        role,
    }
}

fn expr_big(mul: &[(BigInt, u32, u32)], lin: &[(BigInt, u32)], k: BigInt) -> Expression {
    Expression {
        mul_terms: mul
            .iter()
            .map(|(c, l, r)| MulTerm {
                coeff: FieldConst::from_bigint(c.clone()),
                left: *l,
                right: *r,
            })
            .collect(),
        linear_terms: lin
            .iter()
            .map(|(c, v)| LinearTerm {
                coeff: FieldConst::from_bigint(c.clone()),
                var: *v,
            })
            .collect(),
        constant: FieldConst::from_bigint(k),
        note: None,
    }
}

fn expr(mul: &[(i64, u32, u32)], lin: &[(i64, u32)], k: i64) -> Expression {
    expr_big(
        &mul.iter()
            .map(|&(c, l, r)| (BigInt::from(c), l, r))
            .collect::<Vec<_>>(),
        &lin.iter()
            .map(|&(c, v)| (BigInt::from(c), v))
            .collect::<Vec<_>>(),
        BigInt::from(k),
    )
}

fn prog(vars: Vec<Var>, cons: Vec<Expression>) -> PrimitiveProgram {
    PrimitiveProgram {
        field: FieldSpec::bn254(),
        vars,
        constraints: cons,
        witness_gen: Vec::new(),
    }
}

fn boolean(v: u32) -> Expression {
    expr(&[(1, v, v)], &[(-1, v)], 0)
}

fn inputs(pairs: &[(u32, &str)]) -> BTreeMap<u32, String> {
    pairs.iter().map(|(i, s)| (*i, s.to_string())).collect()
}

/// A `Unique` witness must satisfy every row.
fn assert_unique_valid(
    p: &PrimitiveProgram,
    ins: &BTreeMap<u32, String>,
    w: &BTreeMap<u32, xark_ir::solver::Fp>,
) {
    let mut assign = w.clone();
    for (id, s) in ins {
        assign.entry(*id).or_insert_with(|| fp_from_decimal(s, p));
    }
    check(p, &assign).expect("Unique witness satisfies all rows");
}

#[test]
fn free_var_with_solutions_0_and_5_is_not_unique() {
    // x·x − 5x = 0 ⇒ x ∈ {0, 5}; x derived, no inputs.
    let p = prog(
        vec![var(0, "x", VarRole::Derived)],
        vec![expr(&[(1, 0, 0)], &[(-5, 0)], 0)],
    );
    let r = search_witnesses(&p, &inputs(&[]), 1000).unwrap();
    eprintln!("{{0,5}}: {r:?}");
    assert!(matches!(r, WitnessSearch::Inconclusive(_)), "{r:?}");
    // (x−1)(x−5) = x² − 6x + 5 ⇒ {1,5}
    let p = prog(
        vec![var(0, "x", VarRole::Derived)],
        vec![expr(&[(1, 0, 0)], &[(-6, 0)], 5)],
    );
    let r = search_witnesses(&p, &inputs(&[]), 1000).unwrap();
    eprintln!("{{1,5}}: {r:?}");
    assert!(matches!(r, WitnessSearch::Inconclusive(_)), "{r:?}");
    // x(x−1)(x−5) = 0 via y = x²: {0,1,5} ⇒ Multiple is fine (0 and 1 both satisfy).
    let p = prog(
        vec![var(0, "x", VarRole::Derived), var(1, "y", VarRole::Derived)],
        vec![
            expr(&[(1, 0, 0)], &[(-1, 1)], 0),
            expr(&[(1, 1, 0)], &[(-6, 1), (5, 0)], 0),
        ],
    );
    let r = search_witnesses(&p, &inputs(&[]), 1000).unwrap();
    eprintln!("{{0,1,5}}: {r:?}");
    assert!(matches!(r, WitnessSearch::Multiple { .. }), "{r:?}");
}

#[test]
fn projection_with_a_free_internal_is_not_one() {
    // out = 3; w ∈ {0,5} free internal. Projection on out must not claim One.
    let p = prog(
        vec![
            var(0, "out", VarRole::PublicInput),
            var(1, "w", VarRole::Derived),
        ],
        vec![expr(&[], &[(1, 0)], -3), expr(&[(1, 1, 1)], &[(-5, 1)], 0)],
    );
    let r = search_projection(&p, &inputs(&[(0, "3")]), &[0], 1000, None).unwrap();
    eprintln!("proj free internal: {r:?}");
    assert!(matches!(r, Projection::Inconclusive(_)), "{r:?}");
    // With w boolean instead: One.
    let p = prog(
        vec![
            var(0, "out", VarRole::PublicInput),
            var(1, "w", VarRole::Derived),
        ],
        vec![expr(&[], &[(1, 0)], -3), boolean(1)],
    );
    let r = search_projection(&p, &inputs(&[(0, "3")]), &[0], 1000, None).unwrap();
    eprintln!("proj bool internal: {r:?}");
    assert!(matches!(r, Projection::One(_)), "{r:?}");
}

#[test]
fn alias_with_non_unit_coefficient() {
    // u ∈ [0,3] (2 bits), w ∈ [0,3]; 3v + 2u + 1 = 0 (v free → alias, big coeff);
    // v + 7w − 6 = 0.  Integer solution: u=1, w=1, v=−1.
    let vars = vec![
        var(0, "u", VarRole::Derived),
        var(1, "v", VarRole::Derived),
        var(2, "w", VarRole::Derived),
        var(3, "u0", VarRole::Derived),
        var(4, "u1", VarRole::Derived),
        var(5, "w0", VarRole::Derived),
        var(6, "w1", VarRole::Derived),
    ];
    let cons = vec![
        boolean(3),
        boolean(4),
        boolean(5),
        boolean(6),
        expr(&[], &[(1, 3), (2, 4), (-1, 0)], 0),
        expr(&[], &[(1, 5), (2, 6), (-1, 2)], 0),
        expr(&[], &[(3, 1), (2, 0)], 1),
        expr(&[], &[(1, 1), (7, 2)], -6),
    ];
    let p = prog(vars, cons);
    let r = search_witnesses(&p, &inputs(&[]), 1000).unwrap();
    match &r {
        WitnessSearch::Unique(w) => {
            assert_unique_valid(&p, &inputs(&[]), w);
            assert_eq!(w[&0].to_decimal(), "1");
            assert_eq!(w[&2].to_decimal(), "1");
            assert_eq!(w[&1].to_decimal(), (p_bn254() - BigInt::one()).to_string());
        }
        other => panic!("{other:?}"),
    }
}

#[test]
fn coefficients_near_the_small_cutoff() {
    let p = p_bn254();
    for e in [248u32, 249, 250, 251] {
        for delta in [-1i64, 0, 1] {
            let c: BigInt = (BigInt::one() << e) + delta;
            // c·b + x − k = 0, b bool, x 4-bit (bits x0..x3)
            let vars = vec![
                var(0, "b", VarRole::Derived),
                var(1, "x", VarRole::Derived),
                var(2, "x0", VarRole::Derived),
                var(3, "x1", VarRole::Derived),
                var(4, "x2", VarRole::Derived),
                var(5, "x3", VarRole::Derived),
            ];
            let mk = |k: BigInt| {
                prog(
                    vars.clone(),
                    vec![
                        boolean(0),
                        boolean(2),
                        boolean(3),
                        boolean(4),
                        boolean(5),
                        expr(&[], &[(1, 2), (2, 3), (4, 4), (8, 5), (-1, 1)], 0),
                        expr_big(&[], &[(c.clone(), 0), (BigInt::one(), 1)], -k),
                    ],
                )
            };
            for (k, want) in [
                (&c + 3, Some(("1", "3"))),
                (BigInt::from(3), Some(("0", "3"))),
                (&c * 2 + 3, None),
                ((&c + 3) % &p + &p, Some(("1", "3"))), // same residue, given as k+p
                (&c + 16, None),
            ] {
                let pr = mk(k.clone());
                let r = search_witnesses(&pr, &inputs(&[]), 10_000).unwrap();
                match (&r, want) {
                    (WitnessSearch::Unique(w), Some((b, x))) => {
                        assert_unique_valid(&pr, &inputs(&[]), w);
                        assert_eq!(
                            (w[&0].to_decimal(), w[&1].to_decimal()),
                            (b.into(), x.into()),
                            "2^{e}{delta:+} k={k}"
                        );
                    }
                    (WitnessSearch::None, None) => {}
                    _ => panic!("2^{e}{delta:+} k={k}: want {want:?}, got {r:?}"),
                }
            }
        }
    }
}

#[test]
fn wide_range_times_small_coefficient_wraps_the_field() {
    // c = 2^248 (small by the cutoff), b 6-bit: 63·c > p so the integer window is
    // wider than p and the interval pass must not treat the row as an integer equation.
    let p = p_bn254();
    let c: BigInt = BigInt::one() << 248;
    for nbits in [5u32, 6] {
        let mut vars = vec![var(0, "b", VarRole::Derived), var(1, "x", VarRole::Derived)];
        let mut cons = Vec::new();
        let mut lin = vec![(-1i64, 0u32)];
        for i in 0..nbits {
            vars.push(var(2 + i, &format!("b{i}"), VarRole::Derived));
            cons.push(boolean(2 + i));
            lin.push((1 << i, 2 + i));
        }
        cons.push(expr(&[], &lin, 0));
        let xb = 2 + nbits;
        let mut linx = vec![(-1i64, 1u32)];
        for i in 0..4 {
            vars.push(var(xb + i, &format!("x{i}"), VarRole::Derived));
            cons.push(boolean(xb + i));
            linx.push((1 << i, xb + i));
        }
        cons.push(expr(&[], &linx, 0));
        let bmax = (1i64 << nbits) - 1;
        for bv in [bmax, bmax - 1, 1, 0] {
            let k: BigInt = (&c * bv + 5) % &p;
            let mut cs = cons.clone();
            cs.push(expr_big(
                &[],
                &[(c.clone(), 0), (BigInt::one(), 1)],
                -k.clone(),
            ));
            let pr = prog(vars.clone(), cs);
            let r = search_witnesses(&pr, &inputs(&[]), 100_000).unwrap();
            match &r {
                WitnessSearch::Unique(w) => {
                    assert_unique_valid(&pr, &inputs(&[]), w);
                    assert_eq!(
                        (w[&0].to_decimal(), w[&1].to_decimal()),
                        (bv.to_string(), "5".to_string()),
                        "nbits={nbits} b={bv}"
                    );
                }
                other => panic!("nbits={nbits} b={bv}: {other:?}"),
            }
        }
    }
}

#[test]
fn backtracking_restores_aliases() {
    // b bool; b·y + y − 2z = 0; b·z + z − 2 = 0; z = z0 + 2 z1; y·y − 16 = 0.
    // b=0: z=2, y=4 ✓.  b=1: z=1, y=1 ✗(y²=16).  ⇒ Unique.
    let vars = vec![
        var(0, "b", VarRole::Derived),
        var(1, "y", VarRole::Derived),
        var(2, "z", VarRole::Derived),
        var(3, "z0", VarRole::Derived),
        var(4, "z1", VarRole::Derived),
    ];
    let cons = vec![
        boolean(0),
        boolean(3),
        boolean(4),
        expr(&[(1, 0, 1)], &[(1, 1), (-2, 2)], 0),
        expr(&[(1, 0, 2)], &[(1, 2)], -2),
        expr(&[], &[(1, 3), (2, 4), (-1, 2)], 0),
        expr(&[(1, 1, 1)], &[], -16),
    ];
    let p = prog(vars, cons);
    let r = search_witnesses(&p, &inputs(&[]), 1000).unwrap();
    match &r {
        WitnessSearch::Unique(w) => {
            assert_unique_valid(&p, &inputs(&[]), w);
            assert_eq!(
                (w[&0].to_decimal(), w[&1].to_decimal(), w[&2].to_decimal()),
                ("0".into(), "4".into(), "2".into())
            );
        }
        other => panic!("{other:?}"),
    }
    // Swap which branch succeeds: y·y − 1 = 0 ⇒ b=1 only.
    let mut p2 = p.clone();
    p2.constraints[6] = expr(&[(1, 1, 1)], &[], -1);
    let r = search_witnesses(&p2, &inputs(&[]), 1000).unwrap();
    match &r {
        WitnessSearch::Unique(w) => {
            assert_unique_valid(&p2, &inputs(&[]), w);
            assert_eq!(
                (w[&0].to_decimal(), w[&1].to_decimal(), w[&2].to_decimal()),
                ("1".into(), "1".into(), "1".into())
            );
        }
        other => panic!("{other:?}"),
    }
    // Neither: y·y − 9 = 0 ⇒ None.
    let mut p3 = p.clone();
    p3.constraints[6] = expr(&[(1, 1, 1)], &[], -9);
    assert!(matches!(
        search_witnesses(&p3, &inputs(&[]), 1000).unwrap(),
        WitnessSearch::None
    ));
}

#[test]
fn empty_program_and_budget_and_deadline() {
    let p = prog(vec![var(0, "x", VarRole::PublicInput)], vec![]);
    let r = search_witnesses(&p, &inputs(&[(0, "7")]), 10).unwrap();
    eprintln!("no constraints: {r:?}");
    assert!(matches!(r, WitnessSearch::Unique(_)));
    // budget 0
    let p = prog(vec![var(0, "b", VarRole::Derived)], vec![boolean(0)]);
    let r = search_witnesses(&p, &inputs(&[]), 0).unwrap();
    eprintln!("budget 0: {r:?}");
    assert!(matches!(r, WitnessSearch::Inconclusive(_)));
    // deadline 0 on a bigger program
    let mut vars = Vec::new();
    let mut cons = Vec::new();
    for i in 0..40u32 {
        vars.push(var(i, &format!("b{i}"), VarRole::Derived));
        cons.push(boolean(i));
    }
    let p = prog(vars, cons);
    let r = search_witnesses_within(&p, &inputs(&[]), 1 << 20, Some(std::time::Duration::ZERO))
        .unwrap();
    eprintln!("deadline 0: {r:?}");
    assert!(!matches!(r, WitnessSearch::Unique(_) | WitnessSearch::None));
}

// ---------------- randomized brute-force cross-check ----------------

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn modinv(a: &BigInt, p: &BigInt) -> BigInt {
    let a = ((a % p) + p) % p;
    a.modpow(&(p - 2), p)
}

fn md(a: BigInt, p: &BigInt) -> BigInt {
    ((a % p) + p) % p
}

/// Random program: inputs, booleans, composites (linear over bools with small/large
/// coefficients), "free" vars defined by 2-unknown rows with non-unit coefficients,
/// plus random extra rows (products, linears) that are satisfied by a hidden reference
/// assignment with high probability. Brute force over the boolean cube; every other
/// variable is determined (or we recompute it the same way the rows do).
#[test]
fn random_programs_match_brute_force() {
    let p = p_bn254();
    let cases: usize = std::env::var("WS_ADV_CASES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(400);
    let seed: u64 = std::env::var("WS_ADV_SEED")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(0xdead_beef_1234);
    let mut r = Rng(seed | 1);
    let mut stats = BTreeMap::<&str, usize>::new();
    let mut mismatches = Vec::new();
    for case in 0..cases {
        let n_in = 1 + r.below(2) as usize;
        let n_b = 2 + r.below(5) as usize;
        let n_c = r.below(3) as usize;
        let n_f = r.below(3) as usize;
        let mut vars = Vec::new();
        let mut cons = Vec::new();
        let mut ids = 0u32;
        let mut ins = Vec::new();
        let mut in_vals = Vec::<BigInt>::new();
        for i in 0..n_in {
            vars.push(var(ids, &format!("in{i}"), VarRole::PrivateInput));
            let v = match r.below(4) {
                0 => BigInt::zero(),
                1 => BigInt::from(r.below(8)),
                2 => &p - BigInt::from(1 + r.below(3)),
                _ => BigInt::from(r.below(1000)),
            };
            ins.push((ids, v.to_string()));
            in_vals.push(v);
            ids += 1;
        }
        let bools: Vec<u32> = (0..n_b)
            .map(|_| {
                let i = ids;
                ids += 1;
                i
            })
            .collect();
        for (k, &b) in bools.iter().enumerate() {
            vars.push(var(b, &format!("b{k}"), VarRole::Derived));
            cons.push(boolean(b));
        }
        // composites: c = Σ coeff·b + const
        let pick_coeff = |r: &mut Rng| -> BigInt {
            match r.below(8) {
                0 => BigInt::from(r.below(5) as i64 - 2),
                1 => -BigInt::from(1 + r.below(16)),
                2 => BigInt::one() << (200 + r.below(52) as u32),
                3 => -(BigInt::one() << (200 + r.below(52) as u32)),
                4 => (BigInt::one() << 249) - r.below(3),
                _ => BigInt::from(1 + r.below(16)),
            }
        };
        let mut comps: Vec<Comp> = Vec::new();
        for k in 0..n_c {
            let id = ids;
            ids += 1;
            vars.push(var(id, &format!("c{k}"), VarRole::Derived));
            let nterms = 1 + r.below(5) as usize;
            let mut terms = Vec::new();
            for _ in 0..nterms {
                let c = if r.below(2) == 0 {
                    BigInt::from(r.below(17) as i64 - 8)
                } else {
                    pick_coeff(&mut r)
                };
                terms.push((c, bools[r.below(n_b as u64) as usize]));
            }
            let konst = BigInt::from(r.below(7) as i64 - 3);
            // Σ coeff·b + konst − c = 0
            let mut lin: Vec<(BigInt, u32)> = terms.clone();
            lin.push((-BigInt::one(), id));
            cons.push(expr_big(&[], &lin, konst.clone()));
            comps.push((id, terms, konst));
        }
        // free: a·f + b·src + k = 0  (non-unit a)
        let mut frees: Vec<(u32, BigInt, BigInt, u32, BigInt)> = Vec::new();
        for k in 0..n_f {
            let id = ids;
            ids += 1;
            vars.push(var(id, &format!("f{k}"), VarRole::Derived));
            let a = BigInt::from([2i64, 3, -2, 5, -7][r.below(5) as usize]);
            let bcoef = pick_coeff(&mut r);
            let src = if !comps.is_empty() && r.below(2) == 0 {
                comps[r.below(comps.len() as u64) as usize].0
            } else {
                bools[r.below(n_b as u64) as usize]
            };
            let konst = BigInt::from(r.below(9) as i64 - 4);
            cons.push(expr_big(
                &[],
                &[(a.clone(), id), (bcoef.clone(), src)],
                konst.clone(),
            ));
            frees.push((id, a, bcoef, src, konst));
        }
        let all_ids: Vec<u32> = (0..ids).collect();
        // Hidden reference assignment (random bools) for extra rows.
        let eval = |bits: u64| -> BTreeMap<u32, BigInt> {
            let mut m = BTreeMap::new();
            for (i, v) in in_vals.iter().enumerate() {
                m.insert(i as u32, v.clone());
            }
            for (k, &b) in bools.iter().enumerate() {
                m.insert(b, BigInt::from((bits >> k) & 1));
            }
            for (id, terms, konst) in &comps {
                let mut s = konst.clone();
                for (c, b) in terms {
                    s += c * &m[b];
                }
                m.insert(*id, md(s, &p));
            }
            for (id, a, bc, src, konst) in &frees {
                // a·f + bc·src + k = 0 → f = −(bc·src + k)/a
                let v = md(-(bc * &m[src] + konst) * modinv(a, &p), &p);
                m.insert(*id, v);
            }
            m
        };
        let hidden = eval(r.next());
        let n_extra = 1 + r.below(4) as usize;
        for _ in 0..n_extra {
            let kind = r.below(7);
            let mut mul = Vec::new();
            let mut lin = Vec::new();
            let nvars = 1 + r.below(4) as usize;
            let small = |r: &mut Rng| BigInt::from(r.below(9) as i64 - 4);
            match kind {
                4 if !comps.is_empty() => {
                    // multi-term small-coefficient row over composites (interval path)
                    for _ in 0..(2 + r.below(3)) {
                        let v = comps[r.below(comps.len() as u64) as usize].0;
                        lin.push((small(&mut r), v));
                    }
                }
                5 if !comps.is_empty() => {
                    // univariate quadratic on a composite: a·c² + b·c
                    let v = comps[r.below(comps.len() as u64) as usize].0;
                    mul.push((small(&mut r), v, v));
                    lin.push((small(&mut r), v));
                    if r.below(2) == 0 {
                        lin.push((small(&mut r), v));
                    }
                }
                6 => {
                    // duplicate terms and v·v + v mixes on arbitrary vars
                    let v = all_ids[r.below(ids as u64) as usize];
                    mul.push((pick_coeff(&mut r), v, v));
                    mul.push((pick_coeff(&mut r), v, v));
                    lin.push((pick_coeff(&mut r), v));
                    lin.push((pick_coeff(&mut r), v));
                }
                _ => {
                    for _ in 0..nvars {
                        let v = all_ids[r.below(ids as u64) as usize];
                        if kind == 0 || (kind == 1 && r.below(2) == 0) {
                            let w = all_ids[r.below(ids as u64) as usize];
                            mul.push((pick_coeff(&mut r), v, w));
                        } else {
                            lin.push((pick_coeff(&mut r), v));
                        }
                    }
                }
            }
            // constant chosen so the hidden assignment satisfies the row (mostly)
            let mut s = BigInt::zero();
            for (c, l, rr) in &mul {
                s += c * &hidden[l] * &hidden[rr];
            }
            for (c, v) in &lin {
                s += c * &hidden[v];
            }
            let konst = if r.below(5) == 0 {
                BigInt::from(r.below(5) as i64 - 2)
            } else {
                md(-s, &p)
            };
            cons.push(expr_big(&mul, &lin, konst));
        }
        let pr = prog(vars, cons);
        let ins_map: BTreeMap<u32, String> = ins.iter().map(|(i, s)| (*i, s.clone())).collect();
        // brute force
        let mut sols: Vec<BTreeMap<u32, BigInt>> = Vec::new();
        for bits in 0..(1u64 << n_b) {
            let m = eval(bits);
            let assign: BTreeMap<u32, xark_ir::solver::Fp> = m
                .iter()
                .map(|(k, v)| (*k, fp_from_decimal(&v.to_string(), &pr)))
                .collect();
            if check(&pr, &assign).is_ok() {
                sols.push(m);
            }
        }
        let got = search_witnesses(&pr, &ins_map, 1 << 16).unwrap();
        let tag = match (&got, sols.len()) {
            (WitnessSearch::None, 0) => "none ok",
            (WitnessSearch::Unique(w), 1) => {
                assert_unique_valid(&pr, &ins_map, w);
                for (k, v) in w {
                    if let Some(bv) = sols[0].get(k)
                        && v.to_decimal() != bv.to_string()
                    {
                        mismatches.push(format!(
                            "case {case}: unique witness differs at var {k}: search {} brute {bv}",
                            v.to_decimal()
                        ));
                    }
                }
                "unique ok"
            }
            (WitnessSearch::Multiple { .. }, n) if n >= 2 => "multiple ok",
            (WitnessSearch::Inconclusive(_), _) => "inconclusive",
            (g, n) => {
                mismatches.push(format!(
                    "case {case}: search {g:?} but brute force found {n} solutions\n{pr:#?}"
                ));
                "MISMATCH"
            }
        };
        *stats.entry(tag).or_default() += 1;
    }
    eprintln!("{stats:?}");
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n=====\n"));
    // These programs are small enough to always decide: an inconclusive one means
    // the search lost a rule, and the comparison above would go vacuous.
    assert_eq!(stats.get("inconclusive"), None, "{stats:?}");
}

#[test]
fn window_alignment_negative_and_straddling_windows() {
    // c = −8·b0 − 4·b1 + 3·b2 + 1  ∈ [−11, 4]   (window straddles 0 / p)
    // d = 5·b3 − 2·b4             ∈ [−2, 5]
    // rows: c − d + 7 = 0 ; 2c + 3d + e = 0 with e = b5 + 2 b6 ∈ [0,3]; e·e − e·b2 ... keep linear
    // Brute force over 7 bools.
    let p = p_bn254();
    let mut vars: Vec<Var> = (0..7)
        .map(|i| var(i, &format!("b{i}"), VarRole::Derived))
        .collect();
    vars.push(var(7, "c", VarRole::Derived));
    vars.push(var(8, "d", VarRole::Derived));
    vars.push(var(9, "e", VarRole::Derived));
    let mut cons: Vec<Expression> = (0..7).map(boolean).collect();
    cons.push(expr(&[], &[(-8, 0), (-4, 1), (3, 2), (-1, 7)], 1));
    cons.push(expr(&[], &[(5, 3), (-2, 4), (-1, 8)], 0));
    cons.push(expr(&[], &[(1, 5), (2, 6), (-1, 9)], 0));
    let mut ks = Vec::new();
    for k1 in -13i64..=10 {
        for k2 in [-40i64, -20, -10, -5, -2, 0, 1, 3, 7, 12, 20, 35] {
            for k3 in [-121i64, -20, -4, -1, 0, 1, 3, 8, 16, 25] {
                ks.push((k1, k2, k3));
            }
        }
    }
    let mut tally = BTreeMap::<&str, usize>::new();
    for (k1, k2, k3) in ks {
        let mut cs = cons.clone();
        cs.push(expr(&[], &[(1, 7), (-1, 8)], k1));
        cs.push(expr(&[], &[(2, 7), (3, 8), (1, 9)], k2));
        cs.push(expr(&[(1, 7, 7)], &[(-1, 9)], k3));
        let pr = prog(vars.clone(), cs);
        let mut sols = 0;
        let mut sol = None;
        for bits in 0..128u64 {
            let b = |i: u64| -> BigInt { BigInt::from((bits >> i) & 1) };
            let c: BigInt = -8 * b(0) - 4 * b(1) + 3 * b(2) + 1;
            let d: BigInt = 5 * b(3) - 2 * b(4);
            let e: BigInt = b(5) + 2 * b(6);
            let m: BTreeMap<u32, BigInt> = (0..7u32)
                .map(|i| (i, b(i as u64)))
                .chain([
                    (7, md(c.clone(), &p)),
                    (8, md(d.clone(), &p)),
                    (9, md(e.clone(), &p)),
                ])
                .collect();
            let assign: BTreeMap<u32, xark_ir::solver::Fp> = m
                .iter()
                .map(|(k, v)| (*k, fp_from_decimal(&v.to_string(), &pr)))
                .collect();
            if check(&pr, &assign).is_ok() {
                sols += 1;
                sol = Some(m);
            }
        }
        let got = search_witnesses(&pr, &inputs(&[]), 1 << 16).unwrap();
        let tag = match (&got, sols) {
            (WitnessSearch::None, 0) => "none",
            (WitnessSearch::Unique(w), 1) => {
                assert_unique_valid(&pr, &inputs(&[]), w);
                for (k, v) in &sol.unwrap() {
                    assert_eq!(w[k].to_decimal(), v.to_string());
                }
                "unique"
            }
            (WitnessSearch::Multiple { .. }, n) if n >= 2 => "multiple",
            _ => panic!("k=({k1},{k2},{k3}): brute {sols}, search {got:?}"),
        };
        *tally.entry(tag).or_default() += 1;
    }
    eprintln!("alignment tally: {tally:?}");
}
