//! End-to-end checks of `scalar_mul`, `wide_scalar_mul` and `multi_scalar_mul`
//! against `ark-grumpkin` (`examples/grumpkin_reference`, bin `scalar_mul`, prints the
//! constants below; the first MSM vector is the older Python `gref.py` one). Each
//! circuit is compiled from source by `xark-test-harness` and solved by the reference
//! solver: honest vectors verify, wrong outputs and exceptional inputs are rejected,
//! and no single variable of an accepted assignment can be changed (forged).

use std::collections::{BTreeMap, BTreeSet};
use xark_ir::primitive::PrimitiveProgram;
use xark_ir::solver::{self, Fp};

type Pt = (&'static str, &'static str);
type Assign = BTreeMap<u32, Fp>;

// `examples/grumpkin_reference` bin `scalar_mul`: P = 7·G, Q = 9·G, O = the offset.
const P: Pt = (
    "6502298228793251914218452601347199200336821300374732886528232462753193470018",
    "9407677376110273038006540221648729284102344671467345386528008239979586131147",
);
const NEG_P: Pt = (
    "6502298228793251914218452601347199200336821300374732886528232462753193470018",
    "12480565495729002184239865523608545804446019728948688957170195946596222364470",
);
const Q: Pt = (
    "7426331349063244596250713317947873730792793474529352435198059581717112405878",
    "7484184379535064294143018645362320921270470834230314099936005646196658438893",
);
const O: Pt = (
    "5",
    "26447525821777463057023244913909144251512587297343525263882",
);
const NEG_O: Pt = (
    "5",
    "21888242871839275195798879923479812031525119486506890092185616889232283231735",
);
const MID: &str = "338770000845734292534325025077361652240";
const MAX128: &str = "340282366920938463463374607431768211455";
const P_X2: Pt = (
    "12129716857924429340218542075908212533496677097166424713975580824254252046442",
    "11162489639683440471287028718798944516272846750856846865789391746548932089300",
);
const P_XMID: Pt = (
    "16660709030175581512354163313937716757502296131982517654548476685530961098467",
    "11715312318446535013980042341486777010443813696436174735241234683937372914259",
);
const P_XMAX128: Pt = (
    "2137819383813252581401233293719473543374074748951839552069509908387091837782",
    "17583163600808341068946509169083876934863382002853477587978667508431582427189",
);
// Wide scalars as their 127-bit limbs `(lo, hi)`: r − 1 (BN254's scalar field),
// n − 1 (Grumpkin's group order, so (n − 1)·P = −P) and 2²⁵⁴ − 1.
const R1_LIMBS: Pt = (
    "53438638232309528389504892708671455232",
    "128647529226366354083724114970452078778",
);
const N1_LIMBS: Pt = (
    "31244211653629615648651297062205062470",
    "128647529226366354083724114970452078779",
);
const MAX254_LIMBS: Pt = (
    "170141183460469231731687303715884105727",
    "170141183460469231731687303715884105727",
);
const P_XR1: Pt = (
    "16131400377994935718876046815023592821490968534889029052762844845114665524560",
    "5372362056797318860598135311924727564632217008939576841775662817840078489719",
);
const P_XMAX254: Pt = (
    "12703925997184929626448299990681372589963865887580028924850812001438496408757",
    "12988081997150545424902137116510793731667022435618747462218804320066967781662",
);
const MSM_0_MID: Pt = (
    "8409000569300457092895047028362631013831762939218967070361333141449067522605",
    "14424771049864283859459882970067639193723138479806416763172843470323023241674",
);
const MSM_MAX_1: Pt = (
    "13164808700936670096926222796517579004098944330903628285916460536018381707555",
    "17050770860895151953123639565411861801226326901858777036955077899812983342569",
);
const MSM_O_P: Pt = (
    "16365849948753139812342507094540477935075075969408105073068683288337824053449",
    "21735661148021205443265539505505723955736392337448213260239633058420267811785",
);
// The true results of the degenerate MSM inputs the circuit rejects.
const P_X12: Pt = (
    "15609061585951208521228829861764661591132862252469391817985676016234932657650",
    "3272752857784018407324988398576129811786603601131493390026953092233386677633",
);
const NEG_P_X2: Pt = (
    "12129716857924429340218542075908212533496677097166424713975580824254252046442",
    "10725753232155834750959377026458330572275517649559187477908812440026876406317",
);
const S1_Q1: Pt = (
    "11596188065080419238435929782821225214257696975395313359885195599222316813193",
    "13453363696591478931236877623258711810177659660490672929213188796210422544",
);

// Python reference vector (gref.py): R = s0·Q0 + s1·Q1 over Grumpkin, N_BITS=128.
const S0: &str = "1512366075204170929049582354406559215";
const S1: &str = "338770000845734292534325025077361652240";
const Q0: Pt = (
    "8",
    "17211924001480414201552586258339381047922154443519291062668150353239757288029",
);
const Q1: Pt = (
    "10",
    "3764497608137669826449761938357951019955713832105137848030504861970310222496",
);
const R: Pt = (
    "18795281547672131371183968279919782939389077073414573264326681878560793134719",
    "2414680004978840508961516437196481407162521166594374623807266823818455121132",
);

const SCALAR_MUL_SRC: &str = "#![no_std]\n\
    use xark::{require_eq, Field, Public};\n\
    use xark_grumpkin::{decompose, scalar_mul};\n\
    pub fn circuit(s: Public<Field>, px: Public<Field>, py: Public<Field>,\n\
      rx: Public<Field>, ry: Public<Field>) {\n\
      let r = scalar_mul(decompose(s), [px, py]);\n\
      require_eq(r[0], rx);\n\
      require_eq(r[1], ry);\n\
    }\n";

const WIDE_SRC: &str = "#![no_std]\n\
    use xark::{require_eq, Field, Public};\n\
    use xark_grumpkin::{wide_scalar_mul, Affine, WideScalar};\n\
    pub fn circuit(lo: Public<Field>, hi: Public<Field>, px: Public<Field>, py: Public<Field>,\n\
      rx: Public<Field>, ry: Public<Field>) {\n\
      let r = wide_scalar_mul(WideScalar { limbs: [lo, hi] }, Affine { x: px, y: py });\n\
      require_eq(r.x, rx);\n\
      require_eq(r.y, ry);\n\
    }\n";

fn compile(name: &str, src: &str) -> PrimitiveProgram {
    let c = xark_test_harness::compile_source(name, src, "bn254");
    assert!(c.status_success, "compile failed for {name}: {}", c.stderr);
    c.program()
}

fn msm_program() -> PrimitiveProgram {
    let src =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/grumpkin/src/lib.rs");
    let c = xark_test_harness::compile_file(&src, "grumpkin", "bn254");
    assert!(
        c.status_success,
        "compiling examples/grumpkin failed: {}",
        c.stderr
    );
    c.program()
}

fn solve(p: &PrimitiveProgram, inputs: &[(&str, &str)]) -> Result<Assign, solver::SolveError> {
    let id = |name: &str| {
        p.vars
            .iter()
            .find(|v| v.name == name)
            .unwrap_or_else(|| panic!("missing circuit var `{name}`"))
            .id
    };
    let inputs = inputs.iter().map(|(n, v)| (id(n), v.to_string())).collect();
    solver::solve_and_check(p, &inputs)
}

fn scalar_mul(p: &PrimitiveProgram, s: &str, pt: Pt, r: Pt) -> Result<Assign, solver::SolveError> {
    solve(
        p,
        &[
            ("s", s),
            ("px", pt.0),
            ("py", pt.1),
            ("rx", r.0),
            ("ry", r.1),
        ],
    )
}

fn wide(p: &PrimitiveProgram, s: Pt, pt: Pt, r: Pt) -> Result<Assign, solver::SolveError> {
    solve(
        p,
        &[
            ("lo", s.0),
            ("hi", s.1),
            ("px", pt.0),
            ("py", pt.1),
            ("rx", r.0),
            ("ry", r.1),
        ],
    )
}

fn msm(
    p: &PrimitiveProgram,
    s: (&str, &str),
    p0: Pt,
    p1: Pt,
    r: Pt,
) -> Result<Assign, solver::SolveError> {
    solve(
        p,
        &[
            ("s0", s.0),
            ("s1", s.1),
            ("p0.x", p0.0),
            ("p0.y", p0.1),
            ("p1.x", p1.0),
            ("p1.y", p1.1),
            ("r.x", r.0),
            ("r.y", r.1),
        ],
    )
}

/// Changing any one variable of an accepted assignment breaks a row: forged hints
/// (`λ1`, `λ2`, the inverses), every accumulator coordinate, and the output. The only
/// exceptions are the witness-only scratch variables no row reads (the inverses
/// behind `λ2` and `y'`), which the analyzer reports as unreferenced.
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
    let mut forged = assign.clone();
    let mut missed = Vec::new();
    for (&v, honest) in assign {
        forged.insert(
            v,
            if *honest == f1 {
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
    assert!(missed.is_empty(), "forgeable vars: {missed:?}");
}

#[test]
fn scalar_mul_matches_ark_grumpkin() {
    let p = compile("scalar_mul", SCALAR_MUL_SRC);
    for (s, r) in [("1", P), ("2", P_X2), (MID, P_XMID), (MAX128, P_XMAX128)] {
        scalar_mul(&p, s, P, r).unwrap_or_else(|e| panic!("s = {s}: {e:?}"));
        assert!(
            scalar_mul(&p, s, P, (r.0, "123")).is_err(),
            "s = {s}: wrong y accepted"
        );
        assert!(
            scalar_mul(&p, s, P, ("123", r.1)).is_err(),
            "s = {s}: wrong x accepted"
        );
    }
    assert_no_forgeable_var(&p, &scalar_mul(&p, MID, P, P_XMID).unwrap());
}

/// `0·P` has no affine result; an off-curve base or the offset `±O` as the base
/// (an exceptional first step) is rejected whatever output is claimed.
#[test]
fn scalar_mul_rejects_zero_off_curve_and_offset() {
    let p = compile("scalar_mul", SCALAR_MUL_SRC);
    assert!(scalar_mul(&p, "0", P, P).is_err(), "0·P accepted");
    assert!(
        scalar_mul(&p, "1", (P.0, "1"), (P.0, "1")).is_err(),
        "off-curve base accepted"
    );
    assert!(scalar_mul(&p, "1", O, O).is_err(), "base O accepted");
    assert!(
        scalar_mul(&p, "1", NEG_O, NEG_O).is_err(),
        "base −O accepted"
    );
}

/// `scalar_mul` pins its bits itself: a caller passing raw field elements gets a
/// non-boolean bit rejected, not an output the prover chose.
#[test]
fn scalar_mul_rejects_a_non_boolean_bit() {
    let src = "#![no_std]\n\
        use xark::{Field, Public};\n\
        use xark_grumpkin::scalar_mul;\n\
        pub fn circuit(b: Public<Field>, px: Public<Field>, py: Public<Field>) {\n\
          let _ = scalar_mul([b; 128], [px, py]);\n\
        }\n";
    let p = compile("scalar_mul_raw_bits", src);
    let run = |b| solve(&p, &[("b", b), ("px", P.0), ("py", P.1)]);
    run("1").expect("bits all 1 accepted");
    assert!(run("2").is_err(), "bit 2 accepted");
}

#[test]
fn wide_scalar_mul_matches_ark_grumpkin() {
    let p = compile("wide_scalar_mul", WIDE_SRC);
    for (s, r) in [
        (("1", "0"), P),
        (R1_LIMBS, P_XR1),
        (N1_LIMBS, NEG_P),
        (MAX254_LIMBS, P_XMAX254),
    ] {
        wide(&p, s, P, r).unwrap_or_else(|e| panic!("s = {s:?}: {e:?}"));
        assert!(
            wide(&p, s, P, (r.0, "123")).is_err(),
            "s = {s:?}: wrong y accepted"
        );
    }
    assert!(wide(&p, ("0", "0"), P, P).is_err(), "0·P accepted");
    assert!(
        wide(&p, ("1", "0"), (P.0, "1"), P).is_err(),
        "off-curve base accepted"
    );
    assert!(wide(&p, ("1", "0"), O, O).is_err(), "base O accepted");
    assert!(
        wide(&p, ("1", "0"), NEG_O, NEG_O).is_err(),
        "base −O accepted"
    );
    assert_no_forgeable_var(&p, &wide(&p, MAX254_LIMBS, P, P_XMAX254).unwrap());
}

#[test]
fn msm_matches_reference_vectors() {
    let p = msm_program();
    let assign = msm(&p, (S0, S1), Q0, Q1, R).expect("gref.py vector");
    assert_no_forgeable_var(&p, &assign);
    assert!(
        msm(&p, (S0, S1), Q0, Q1, ("123", R.1)).is_err(),
        "wrong output x accepted"
    );
    // A zero scalar, the widest scalar, and the offset `O` as a base.
    msm(&p, ("0", MID), P, Q, MSM_0_MID).expect("0·P + mid·Q");
    msm(&p, (MAX128, "1"), P, Q, MSM_MAX_1).expect("(2¹²⁸ − 1)·P + Q");
    msm(&p, (MID, "3"), O, P, MSM_O_P).expect("mid·O + 3·P");
    assert!(
        msm(&p, ("0", MID), P, Q, P).is_err(),
        "wrong output accepted"
    );
}

/// The shared table needs `P₀ ≠ ±P₁`; an all-zero result has no affine point; an
/// off-curve point (the affine stand-in `(0, 0)` for the identity among them) is
/// rejected by the on-curve check. Each claims the true result where one exists.
#[test]
fn msm_rejects_degenerate_inputs() {
    let p = msm_program();
    assert!(
        msm(&p, ("5", "7"), P, P, P_X12).is_err(),
        "P₀ = P₁ accepted"
    );
    assert!(
        msm(&p, ("5", "7"), P, NEG_P, NEG_P_X2).is_err(),
        "P₀ = −P₁ accepted"
    );
    assert!(msm(&p, ("0", "0"), P, Q, P).is_err(), "0·P + 0·Q accepted");
    assert!(
        msm(&p, (S0, S1), ("0", "0"), Q1, S1_Q1).is_err(),
        "identity (0, 0) accepted"
    );
    assert!(
        msm(&p, (S0, S1), (Q0.0, "1"), Q1, R).is_err(),
        "off-curve point accepted"
    );
}
