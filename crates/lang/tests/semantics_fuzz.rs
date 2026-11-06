//! Native-semantics fuzzing: random circuits over witness integers, checked against
//! what Rust itself computes.
//!
//! Each case is a random straight-line program over `uN` witnesses (`+ - * / %`,
//! bit ops, shifts, wrapping ops, narrowing casts, comparisons feeding selects and
//! `assert!`, `match` on a witness byte, loads from and stores to an array at a
//! witness index, loops whose bodies branch on witness bits, nested witness `if`s
//! whose arms compute (and may panic) or `assert!`, `inv` / `to_bits` / `lt` in
//! witness arms) ending in `require_eq(Field::from(v), out)`. For edge-heavy inputs
//! the program is evaluated here with Rust's (debug, overflow-checked) semantics, and
//! every input is decided by exhaustive witness search (all satisfying assignments,
//! not the honest solver's one):
//!
//! * returns `v` → exactly one witness proves `out = v` (and the honest solver finds
//!   it), none proves `out = v + 1`;
//! * panics (overflow, `/ 0`, a failed `assert!`) → no witness proves any `out` tried
//!   (the honest value, wrapped, 0).
//!
//! `XARK_FUZZ_CASES` (default 24) and `XARK_FUZZ_SEED` widen it. A circuit the
//! frontend refuses to compile is reported, not failed: an honest rejection is never
//! unsound. A search that can't decide is reported too.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use xark_ir::solver;
use xark_ir::witness_search::{self, WitnessSearch};

/// Case splits per witness search before it gives up (reported, not failed).
const SEARCH_BUDGET: usize = 4096;

/// xorshift64*: deterministic, dependency-free.
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

#[derive(Clone, Copy, Debug)]
enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    And,
    Or,
    Xor,
    WAdd,
    WSub,
    WMul,
}

#[derive(Clone, Copy, Debug)]
enum Cmp {
    Lt,
    Le,
    Eq,
    Ne,
}

#[derive(Clone, Debug)]
enum Expr {
    Var(usize),
    Const(u64),
    Bin(Op, Box<Expr>, Box<Expr>),
    Shl(Box<Expr>, u32),
    Shr(Box<Expr>, u32),
    Not(Box<Expr>),
    /// `(e as u8) as uN`
    Narrow(Box<Expr>),
}

#[derive(Clone, Debug)]
enum Stmt {
    /// `let vK = expr;`
    Let(Expr),
    /// `let vK = if va CMP vb { vc } else { vd };` (arms are plain values)
    Select(Cmp, usize, usize, usize, usize),
    /// `assert!(va CMP vb);`
    Assert(Cmp, usize, usize),
    /// `let vK = match va as u8 { k0 => c0, …, _ => default };`
    Match(usize, Vec<(u8, u64)>, u64),
    /// `let vK = [c0, …, c7][(va & 7) as usize];`
    Index(usize, [u64; 8]),
    /// `let vK = if va CMP vb { expr } else { expr };` (only the taken arm may panic)
    Cond(Cmp, usize, usize, Expr, Expr),
    /// `if va CMP vb { assert!(vc CMP vd); }`
    CondAssert(Cmp, usize, usize, Cmp, usize, usize),
    /// `let vK = { let mut acc = vb; for i in 0..n { if (va >> i) & 1 == 1 { acc = acc OP vc; } } acc };`
    Loop(usize, usize, Op, usize, u32),
    /// `let vK = { let mut t = [c0, c1, c2, c3]; t[(va & 3) as usize] = vb; t[(vc & 3) as usize] };`
    Store([u64; 4], usize, usize, usize),
    /// `let vK = if va CMP vb { if vc CMP vd { e1 } else { e2 } } else { e3 };`
    Nested(Cmp, usize, usize, Cmp, usize, usize, Expr, Expr, Expr),
    /// `if va CMP vb { <field op on vx, vy> }`: `inv` (panics on 0), `to_bits::<n>`
    /// (panics unless `vx < 2^n`), `require(lt::<n>(vx, vy))`.
    CondField(Cmp, usize, usize, FieldOp, usize, usize),
}

#[derive(Clone, Copy, Debug)]
enum FieldOp {
    Inv,
    Bits(u32),
    Lt(u32),
}

struct Prog {
    bits: u32,
    n_inputs: usize,
    stmts: Vec<Stmt>,
}

impl Prog {
    fn ty(&self) -> String {
        format!("u{}", self.bits)
    }
    fn mask(&self) -> u128 {
        (1u128 << self.bits) - 1
    }
}

fn gen_expr(r: &mut Rng, p: &Prog, n_vals: usize, depth: u32) -> Expr {
    let leaf = depth == 0 || r.below(3) == 0;
    if leaf {
        if r.below(4) == 0 {
            let edge = [0u128, 1, 2, 3, p.mask(), p.mask() - 1, 7, 255];
            let c = edge[r.below(edge.len() as u64) as usize] & p.mask();
            return Expr::Const(c as u64);
        }
        return Expr::Var(r.below(n_vals as u64) as usize);
    }
    let sub = |r: &mut Rng| Box::new(gen_expr(r, p, n_vals, depth - 1));
    match r.below(15) {
        0..=10 => {
            let ops = [
                Op::Add,
                Op::Sub,
                Op::Mul,
                Op::Div,
                Op::Rem,
                Op::And,
                Op::Or,
                Op::Xor,
                Op::WAdd,
                Op::WSub,
                Op::WMul,
            ];
            Expr::Bin(ops[r.below(11) as usize], sub(r), sub(r))
        }
        11 => Expr::Shl(sub(r), r.below(p.bits as u64) as u32),
        12 => Expr::Shr(sub(r), r.below(p.bits as u64) as u32),
        13 => Expr::Not(sub(r)),
        _ => Expr::Narrow(sub(r)),
    }
}

fn gen_prog(r: &mut Rng) -> Prog {
    let bits = [8u32, 16, 32, 64][r.below(4) as usize];
    let n_inputs = 1 + r.below(3) as usize;
    let mut p = Prog {
        bits,
        n_inputs,
        stmts: Vec::new(),
    };
    let mut n_vals = n_inputs;
    let cmps = [Cmp::Lt, Cmp::Le, Cmp::Eq, Cmp::Ne];
    for _ in 0..(2 + r.below(4)) {
        let pick = |r: &mut Rng| r.below(n_vals as u64) as usize;
        let s = match r.below(15) {
            10 => Stmt::Loop(
                pick(r),
                pick(r),
                [Op::Add, Op::WAdd, Op::Xor, Op::Sub][r.below(4) as usize],
                pick(r),
                1 + r.below(4) as u32,
            ),
            11 => {
                let mut t = [0u64; 4];
                for x in &mut t {
                    *x = r.below(1000);
                }
                Stmt::Store(t, pick(r), pick(r), pick(r))
            }
            12 => Stmt::Nested(
                cmps[r.below(4) as usize],
                pick(r),
                pick(r),
                cmps[r.below(4) as usize],
                pick(r),
                pick(r),
                gen_expr(r, &p, n_vals, 2),
                gen_expr(r, &p, n_vals, 2),
                gen_expr(r, &p, n_vals, 2),
            ),
            13 | 14 => {
                let n = 1 + r.below(bits.min(16) as u64) as u32;
                let op = [FieldOp::Inv, FieldOp::Bits(n), FieldOp::Lt(n)][r.below(3) as usize];
                Stmt::CondField(
                    cmps[r.below(4) as usize],
                    pick(r),
                    pick(r),
                    op,
                    pick(r),
                    pick(r),
                )
            }
            8 => Stmt::Cond(
                cmps[r.below(4) as usize],
                pick(r),
                pick(r),
                gen_expr(r, &p, n_vals, 2),
                gen_expr(r, &p, n_vals, 2),
            ),
            9 if n_vals > 1 => Stmt::CondAssert(
                cmps[r.below(4) as usize],
                pick(r),
                pick(r),
                cmps[r.below(4) as usize],
                pick(r),
                pick(r),
            ),
            6 => {
                let mut arms: Vec<(u8, u64)> = Vec::new();
                for _ in 0..(1 + r.below(5)) {
                    let k = r.below(8) as u8;
                    if !arms.iter().any(|(a, _)| *a == k) {
                        arms.push((k, r.below(1000)));
                    }
                }
                Stmt::Match(r.below(n_vals as u64) as usize, arms, r.below(1000))
            }
            7 => {
                let mut t = [0u64; 8];
                for x in &mut t {
                    *x = r.below(1000);
                }
                Stmt::Index(r.below(n_vals as u64) as usize, t)
            }
            0 => Stmt::Select(
                cmps[r.below(4) as usize],
                pick(r),
                pick(r),
                pick(r),
                pick(r),
            ),
            1 if n_vals > 1 => Stmt::Assert(
                cmps[r.below(4) as usize],
                r.below(n_vals as u64) as usize,
                r.below(n_vals as u64) as usize,
            ),
            _ => Stmt::Let(gen_expr(r, &p, n_vals, 3)),
        };
        if !matches!(
            s,
            Stmt::Assert(..) | Stmt::CondAssert(..) | Stmt::CondField(..)
        ) {
            n_vals += 1;
        }
        p.stmts.push(s);
    }
    p
}

fn var(i: usize, p: &Prog) -> String {
    if i < p.n_inputs {
        format!("x{i}")
    } else {
        format!("v{}", i - p.n_inputs)
    }
}

fn render_expr(e: &Expr, p: &Prog) -> String {
    let ty = p.ty();
    match e {
        Expr::Var(i) => var(*i, p),
        Expr::Const(c) => format!("{c}{ty}"),
        Expr::Bin(op, a, b) => {
            let (a, b) = (render_expr(a, p), render_expr(b, p));
            match op {
                Op::Add => format!("({a} + {b})"),
                Op::Sub => format!("({a} - {b})"),
                Op::Mul => format!("({a} * {b})"),
                Op::Div => format!("({a} / {b})"),
                Op::Rem => format!("({a} % {b})"),
                Op::And => format!("({a} & {b})"),
                Op::Or => format!("({a} | {b})"),
                Op::Xor => format!("({a} ^ {b})"),
                Op::WAdd => format!("{a}.wrapping_add({b})"),
                Op::WSub => format!("{a}.wrapping_sub({b})"),
                Op::WMul => format!("{a}.wrapping_mul({b})"),
            }
        }
        Expr::Shl(a, k) => format!("({} << {k})", render_expr(a, p)),
        Expr::Shr(a, k) => format!("({} >> {k})", render_expr(a, p)),
        Expr::Not(a) => format!("(!{})", render_expr(a, p)),
        Expr::Narrow(a) => format!("(({} as u8) as {ty})", render_expr(a, p)),
    }
}

fn cmp_str(c: Cmp) -> &'static str {
    match c {
        Cmp::Lt => "<",
        Cmp::Le => "<=",
        Cmp::Eq => "==",
        Cmp::Ne => "!=",
    }
}

fn render(p: &Prog) -> String {
    let ty = p.ty();
    let mut s = String::from(
        "#![no_std]\n#![allow(unconditional_panic, arithmetic_overflow)]\n\
         use xark::prelude::*;\npub fn circuit(",
    );
    for i in 0..p.n_inputs {
        write!(s, "x{i}: Private<{ty}>, ").unwrap();
    }
    s.push_str("out: Public<Field>) {\n");
    let mut k = 0;
    for st in &p.stmts {
        match st {
            Stmt::Let(e) => {
                writeln!(s, "    let v{k}: {ty} = {};", render_expr(e, p)).unwrap();
                k += 1;
            }
            Stmt::Select(c, a, b, t, f) => {
                writeln!(
                    s,
                    "    let v{k}: {ty} = if {} {} {} {{ {} }} else {{ {} }};",
                    var(*a, p),
                    cmp_str(*c),
                    var(*b, p),
                    var(*t, p),
                    var(*f, p)
                )
                .unwrap();
                k += 1;
            }
            Stmt::Assert(c, a, b) => {
                writeln!(
                    s,
                    "    assert!({} {} {});",
                    var(*a, p),
                    cmp_str(*c),
                    var(*b, p)
                )
                .unwrap();
            }
            Stmt::Cond(c, a, b, t, f) => {
                writeln!(
                    s,
                    "    let v{k}: {ty} = if {} {} {} {{ {} }} else {{ {} }};",
                    var(*a, p),
                    cmp_str(*c),
                    var(*b, p),
                    render_expr(t, p),
                    render_expr(f, p)
                )
                .unwrap();
                k += 1;
            }
            Stmt::CondAssert(c, a, b, c2, x, y) => {
                writeln!(
                    s,
                    "    if {} {} {} {{ assert!({} {} {}); }}",
                    var(*a, p),
                    cmp_str(*c),
                    var(*b, p),
                    var(*x, p),
                    cmp_str(*c2),
                    var(*y, p)
                )
                .unwrap();
            }
            Stmt::Loop(a, b, op, c, n) => {
                let c = var(*c, p);
                let step = match op {
                    Op::Add => format!("acc + {c}"),
                    Op::Sub => format!("acc - {c}"),
                    Op::Xor => format!("acc ^ {c}"),
                    _ => format!("acc.wrapping_add({c})"),
                };
                writeln!(
                    s,
                    "    let v{k}: {ty} = {{ let mut acc: {ty} = {}; for i in 0..{n} {{ if ({} >> i) & 1 == 1 {{ acc = {step}; }} }} acc }};",
                    var(*b, p),
                    var(*a, p),
                )
                .unwrap();
                k += 1;
            }
            Stmt::Store(t, a, b, c) => {
                let items: Vec<String> = t
                    .iter()
                    .map(|x| format!("{}{ty}", *x as u128 & p.mask()))
                    .collect();
                writeln!(
                    s,
                    "    let v{k}: {ty} = {{ let mut t = [{}]; t[({} & 3) as usize] = {}; t[({} & 3) as usize] }};",
                    items.join(", "),
                    var(*a, p),
                    var(*b, p),
                    var(*c, p)
                )
                .unwrap();
                k += 1;
            }
            Stmt::Nested(c, a, b, c2, x, y, e1, e2, e3) => {
                writeln!(
                    s,
                    "    let v{k}: {ty} = if {} {} {} {{ if {} {} {} {{ {} }} else {{ {} }} }} else {{ {} }};",
                    var(*a, p),
                    cmp_str(*c),
                    var(*b, p),
                    var(*x, p),
                    cmp_str(*c2),
                    var(*y, p),
                    render_expr(e1, p),
                    render_expr(e2, p),
                    render_expr(e3, p)
                )
                .unwrap();
                k += 1;
            }
            Stmt::CondField(c, a, b, op, x, y) => {
                let (fx, fy) = (
                    format!("Field::from({})", var(*x, p)),
                    format!("Field::from({})", var(*y, p)),
                );
                let body = match op {
                    FieldOp::Inv => format!("let _ = {fx}.inv();"),
                    FieldOp::Bits(n) => format!("let _ = {fx}.to_bits::<{n}>();"),
                    FieldOp::Lt(n) => format!("require({fx}.lt::<{n}>({fy}));"),
                };
                writeln!(
                    s,
                    "    if {} {} {} {{ {body} }}",
                    var(*a, p),
                    cmp_str(*c),
                    var(*b, p)
                )
                .unwrap();
            }
            Stmt::Match(a, arms, d) => {
                write!(s, "    let v{k}: {ty} = match {} as u8 {{ ", var(*a, p)).unwrap();
                for (key, val) in arms {
                    write!(s, "{key} => {}, ", *val as u128 & p.mask()).unwrap();
                }
                writeln!(s, "_ => {} }};", *d as u128 & p.mask()).unwrap();
                k += 1;
            }
            Stmt::Index(a, t) => {
                let items: Vec<String> = t
                    .iter()
                    .map(|x| format!("{}{ty}", *x as u128 & p.mask()))
                    .collect();
                writeln!(
                    s,
                    "    let v{k}: {ty} = [{}][({} & 7) as usize];",
                    items.join(", "),
                    var(*a, p)
                )
                .unwrap();
                k += 1;
            }
        }
    }
    writeln!(
        s,
        "    require_eq(Field::from({}), out);\n}}",
        var(p.n_inputs + k - 1, p)
    )
    .unwrap();
    s
}

/// Rust's debug semantics: `None` where the program panics.
fn eval_expr(e: &Expr, p: &Prog, vals: &[u128]) -> Option<u128> {
    let m = p.mask();
    let max = m;
    Some(match e {
        Expr::Var(i) => vals[*i],
        Expr::Const(c) => *c as u128,
        Expr::Bin(op, a, b) => {
            let (a, b) = (eval_expr(a, p, vals)?, eval_expr(b, p, vals)?);
            match op {
                Op::Add => Some(a + b).filter(|v| *v <= max)?,
                Op::Sub => a.checked_sub(b)?,
                Op::Mul => a.checked_mul(b).filter(|v| *v <= max)?,
                Op::Div => a.checked_div(b)?,
                Op::Rem => a.checked_rem(b)?,
                Op::And => a & b,
                Op::Or => a | b,
                Op::Xor => a ^ b,
                Op::WAdd => (a + b) & m,
                Op::WSub => a.wrapping_sub(b) & m,
                Op::WMul => a.wrapping_mul(b) & m,
            }
        }
        Expr::Shl(a, k) => (eval_expr(a, p, vals)? << k) & m,
        Expr::Shr(a, k) => eval_expr(a, p, vals)? >> k,
        Expr::Not(a) => !eval_expr(a, p, vals)? & m,
        Expr::Narrow(a) => eval_expr(a, p, vals)? & 0xff,
    })
}

fn eval(p: &Prog, inputs: &[u128]) -> Option<u128> {
    let mut vals = inputs.to_vec();
    let holds = |c: Cmp, a: u128, b: u128| match c {
        Cmp::Lt => a < b,
        Cmp::Le => a <= b,
        Cmp::Eq => a == b,
        Cmp::Ne => a != b,
    };
    for st in &p.stmts {
        match st {
            Stmt::Let(e) => {
                let v = eval_expr(e, p, &vals)?;
                vals.push(v);
            }
            Stmt::Select(c, a, b, t, f) => {
                let v = if holds(*c, vals[*a], vals[*b]) {
                    vals[*t]
                } else {
                    vals[*f]
                };
                vals.push(v);
            }
            Stmt::Assert(c, a, b) => {
                if !holds(*c, vals[*a], vals[*b]) {
                    return None;
                }
            }
            Stmt::Match(a, arms, d) => {
                let key = (vals[*a] & 0xff) as u8;
                let v = arms.iter().find(|(k, _)| *k == key).map_or(*d, |(_, v)| *v);
                vals.push(v as u128 & p.mask());
            }
            Stmt::Index(a, t) => vals.push(t[(vals[*a] & 7) as usize] as u128 & p.mask()),
            Stmt::Cond(c, a, b, t, f) => {
                let e = if holds(*c, vals[*a], vals[*b]) { t } else { f };
                let v = eval_expr(e, p, &vals)?;
                vals.push(v);
            }
            Stmt::CondAssert(c, a, b, c2, x, y) => {
                if holds(*c, vals[*a], vals[*b]) && !holds(*c2, vals[*x], vals[*y]) {
                    return None;
                }
            }
            Stmt::Loop(a, b, op, c, n) => {
                let mut acc = vals[*b];
                let (cv, m) = (vals[*c], p.mask());
                for i in 0..*n {
                    if (vals[*a] >> i) & 1 == 1 {
                        acc = match op {
                            Op::Add => Some(acc + cv).filter(|v| *v <= m)?,
                            Op::Sub => acc.checked_sub(cv)?,
                            Op::Xor => acc ^ cv,
                            _ => (acc + cv) & m,
                        };
                    }
                }
                vals.push(acc);
            }
            Stmt::Store(t, a, b, c) => {
                let mut t: Vec<u128> = t.iter().map(|x| *x as u128 & p.mask()).collect();
                t[(vals[*a] & 3) as usize] = vals[*b];
                vals.push(t[(vals[*c] & 3) as usize]);
            }
            Stmt::Nested(c, a, b, c2, x, y, e1, e2, e3) => {
                let e = if holds(*c, vals[*a], vals[*b]) {
                    if holds(*c2, vals[*x], vals[*y]) {
                        e1
                    } else {
                        e2
                    }
                } else {
                    e3
                };
                let v = eval_expr(e, p, &vals)?;
                vals.push(v);
            }
            Stmt::CondField(c, a, b, op, x, y) => {
                if holds(*c, vals[*a], vals[*b]) {
                    let (vx, vy) = (vals[*x], vals[*y]);
                    let ok = match op {
                        FieldOp::Inv => vx != 0,
                        FieldOp::Bits(n) => vx < 1u128 << n,
                        FieldOp::Lt(n) => vx < 1u128 << n && vy < 1u128 << n && vx < vy,
                    };
                    if !ok {
                        return None;
                    }
                }
            }
        }
    }
    vals.last().copied()
}

fn gen_input(r: &mut Rng, p: &Prog) -> u128 {
    let m = p.mask();
    match r.below(6) {
        0 => 0,
        1 => 1,
        2 => m,
        3 => m - r.below(3) as u128,
        4 => r.below(16) as u128,
        _ => r.next() as u128 & m,
    }
}

#[test]
fn circuits_match_native_rust_semantics() {
    let cases: usize = std::env::var("XARK_FUZZ_CASES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(24);
    let seed: u64 = std::env::var("XARK_FUZZ_SEED")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(0x5eed_1234_abcd);
    let mut r = Rng(seed | 1);
    let (mut compiled, mut refused, mut checks) = (0usize, Vec::new(), 0usize);
    let mut failures = Vec::new();
    let (mut searches, mut inconclusive) = (0usize, BTreeMap::<String, usize>::new());
    for case in 0..cases {
        let p = gen_prog(&mut r);
        let src = render(&p);
        let c = xark_test_harness::compile_source(&format!("fuzz_sem_{case}"), &src, "bn254");
        if !c.status_success {
            let first = c
                .stderr
                .lines()
                .find(|l| l.contains("error"))
                .unwrap_or("")
                .to_string();
            assert!(
                !c.stderr.contains("panicked at") && !c.stderr.contains("RUST_BACKTRACE"),
                "case {case}: the compiler crashed\n{src}\n{}",
                c.stderr
            );
            // "The circuit panicked" at compile time claims every input panics:
            // check that against Rust on a sample.
            if c.stderr.contains("the circuit panicked") {
                for _ in 0..32 {
                    let xs: Vec<u128> = (0..p.n_inputs).map(|_| gen_input(&mut r, &p)).collect();
                    if let Some(v) = eval(&p, &xs) {
                        failures.push(format!(
                            "case {case} {xs:?}: refused as always panicking, but Rust gives {v}\n{src}"
                        ));
                        break;
                    }
                }
            }
            if std::env::var_os("XARK_FUZZ_SHOW_REFUSED").is_some() {
                eprintln!("--- refused case {case}: {first}\n{src}");
            }
            refused.push(first);
            continue;
        }
        compiled += 1;
        let prog = c.program();
        let id = |name: &str| prog.vars.iter().find(|v| v.name == name).map(|v| v.id);
        let solve = |xs: &[u128], out: u128| {
            let mut m = BTreeMap::new();
            for (i, x) in xs.iter().enumerate() {
                m.insert(id(&format!("x{i}")).unwrap(), x.to_string());
            }
            m.insert(id("out").unwrap(), out.to_string());
            solver::solve_and_check(&prog, &m)
        };
        // The adversary: every satisfying witness for these inputs, not just the
        // honest solver's.
        let search = |xs: &[u128], out: u128| {
            let mut m = BTreeMap::new();
            for (i, x) in xs.iter().enumerate() {
                m.insert(id(&format!("x{i}")).unwrap(), x.to_string());
            }
            m.insert(id("out").unwrap(), out.to_string());
            witness_search::search_witnesses(&prog, &m, SEARCH_BUDGET).unwrap()
        };
        let mut adversary = |failures: &mut Vec<String>,
                             xs: &[u128],
                             out: u128,
                             want_unique: bool| {
            searches += 1;
            match (search(xs, out), want_unique) {
                (WitnessSearch::Unique(_), true) | (WitnessSearch::None, false) => {}
                (WitnessSearch::Inconclusive(why), _) => {
                    if std::env::var_os("XARK_FUZZ_SHOW_INCONCLUSIVE").is_some() {
                        eprintln!("--- inconclusive case {case} {xs:?} out = {out}: {why}\n{src}");
                    }
                    *inconclusive.entry(why).or_default() += 1;
                }
                (WitnessSearch::Multiple { name, .. }, _) => failures.push(format!(
                    "case {case} {xs:?} out = {out}: two satisfying witnesses (differ at `{name}`)\n{src}"
                )),
                (WitnessSearch::None, true) => failures.push(format!(
                    "case {case} {xs:?}: Rust gives {out}, no witness satisfies the circuit\n{src}"
                )),
                (WitnessSearch::Unique(_), false) => failures.push(format!(
                    "case {case} {xs:?}: a forged witness proves out = {out}\n{src}"
                )),
            }
        };
        for _ in 0..8 {
            let xs: Vec<u128> = (0..p.n_inputs).map(|_| gen_input(&mut r, &p)).collect();
            checks += 1;
            match eval(&p, &xs) {
                Some(v) => {
                    adversary(&mut failures, &xs, v, true);
                    adversary(&mut failures, &xs, v + 1, false);
                }
                None => {
                    for out in [0u128, 1, xs.first().copied().unwrap_or(0)] {
                        adversary(&mut failures, &xs, out, false);
                    }
                }
            }
            match eval(&p, &xs) {
                Some(v) => match solve(&xs, v) {
                    Ok(assign) => {
                        if solve(&xs, v + 1).is_ok() {
                            failures
                                .push(format!("case {case} {xs:?}: accepts out = {v} + 1\n{src}"));
                        }
                        let holes: Vec<_> = solver::analyze_underconstrained(&prog, &assign)
                            .into_iter()
                            .filter(|u| u.reason != "no constraint references this variable")
                            .collect();
                        if !holes.is_empty() {
                            failures.push(format!(
                                "case {case} {xs:?}: under-constrained {:?}\n{src}",
                                &holes[..holes.len().min(3)]
                            ));
                        }
                    }
                    Err(e) => failures.push(format!(
                        "case {case} {xs:?}: Rust gives {v}, circuit rejects it ({e})\n{src}"
                    )),
                },
                None => {
                    for out in [0u128, 1, xs.first().copied().unwrap_or(0)] {
                        if solve(&xs, out).is_ok() {
                            failures.push(format!(
                                "case {case} {xs:?}: Rust panics, circuit accepts out = {out}\n{src}"
                            ));
                        }
                    }
                }
            }
        }
    }
    let mut kinds: BTreeMap<&str, usize> = BTreeMap::new();
    for f in &refused {
        *kinds.entry(f.as_str()).or_default() += 1;
    }
    eprintln!(
        "{cases} programs: {compiled} compiled, {} refused, {checks} input checks",
        refused.len()
    );
    for (k, n) in &kinds {
        eprintln!("  refused ×{n}: {k}");
    }
    let undecided: usize = inconclusive.values().sum();
    eprintln!("{searches} witness searches, {undecided} inconclusive");
    for (k, n) in &inconclusive {
        eprintln!("  inconclusive ×{n}: {k}");
    }
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n---\n")
    );
    assert!(compiled > 0, "no generated program compiled");
    // The adversarial half must check something: at most 10% of searches undecided.
    assert!(
        searches > 0 && undecided * 10 <= searches,
        "{undecided} of {searches} witness searches inconclusive"
    );
}
