//! `#[input]`: one impl gives a struct its leaves (named by the compiler's
//! layout, in input order), its host values for the prover, its `to_fields`, and its
//! `schema.json` description. These tests pin the leaf names, order and values, which
//! must match the compiler's input-var order exactly.

use xark::input::Type;
use xark::{Bitfield, Choice, Country, Date, Field, Input, Text, input};

/// The leaves with decimal values, for comparison.
fn leaves<T: Input>(v: &T, prefix: &str) -> Vec<(String, String)> {
    input::leaves(v, prefix)
        .into_iter()
        .map(|(n, f)| (n, f.to_string()))
        .collect()
}

/// Scalars + a fixed array — `Field`s (host-built) rendered to decimals, `<prefix>.f[i]`
/// for array elements.
#[input]
struct Account {
    id: Field,
    tags: [Field; 3],
    balance: Field,
}

#[test]
fn input_leaves_are_values_in_input_order() {
    let acct = Account {
        id: Field::from(7u64),
        tags: [Field::from(10u64), Field::from(11u64), Field::from(12u64)],
        balance: Field::from(999u64),
    };
    assert_eq!(
        leaves(&acct, "user"),
        [
            ("user.id", "7"),
            ("user.tags[0]", "10"),
            ("user.tags[1]", "11"),
            ("user.tags[2]", "12"),
            ("user.balance", "999"),
        ]
        .map(|(n, v)| (n.to_string(), v.to_string()))
    );
    assert_eq!(<Account as Input>::LEN, 5);
    assert_eq!(acct.to_fields().map(|f| f.to_decimal())[4], "999");
}

/// Native integers, byte arrays, and a nested derived struct: host values stay
/// native (`u64`, `[u8; 2]`), and the nested struct's leaves appear inline under its
/// field name.
#[input]
struct Inner {
    a: u64,
    b: Field,
}

#[input]
struct Outer {
    inner: Inner,
    tag: [u8; 2],
    c: u32,
}

#[test]
fn input_uints_and_nesting_leaves() {
    let o = Outer {
        inner: Inner {
            a: u64::MAX,
            b: Field::from(20u8),
        },
        tag: [1, 2],
        c: 3,
    };
    let leaves = leaves(&o, "o");
    let got: Vec<(&str, &str)> = leaves
        .iter()
        .map(|(k, v)| (k.as_str(), v.as_str()))
        .collect();
    assert_eq!(
        got,
        vec![
            ("o.inner.a", "18446744073709551615"),
            ("o.inner.b", "20"),
            ("o.tag[0]", "1"),
            ("o.tag[1]", "2"),
            ("o.c", "3"),
        ]
    );
    assert_eq!(<Inner as Input>::LEN, 2);
    assert_eq!(<Outer as Input>::LEN, 5);
    // `to_fields` works on the host too: integers convert with `Field::from`.
    let flat = o.to_fields();
    assert_eq!(flat[0].to_decimal(), "18446744073709551615");
    assert_eq!(flat[4].to_decimal(), "3");
    // And back: a value from its field elements.
    let back: Outer = input::from_fields(&flat);
    assert_eq!((back.inner.a, back.tag, back.c), (u64::MAX, [1, 2], 3));
}

/// A hand-written impl: a type the derive can't express (a generic one).
#[derive(Clone, Copy)]
struct Pair<T>(T, T);

impl<T: Input> Input for Pair<T> {
    const TYPE: Type = Type::Named(&Type::named(
        "Pair",
        input::Layout::fields(&[
            input::Member::new("first", T::TYPE),
            input::Member::new("second", T::TYPE),
        ]),
    ));
    fn read(r: &mut input::Reader<'_>) -> Self {
        Pair(r.read(), r.read())
    }
    fn write(&self, w: &mut input::Writer<'_>) {
        w.write(&self.0);
        w.write(&self.1);
    }
}

#[test]
fn a_hand_written_impl() {
    let p = Pair(3u8, 4u8);
    assert_eq!(
        leaves(&p, "p"),
        [("p.first", "3"), ("p.second", "4")].map(|(n, v)| (n.to_string(), v.to_string()))
    );
}

use xark::{Private, Public};

/// A holder's standing.
#[input]
enum Tier {
    Retail,
    Accredited,
}

#[xark::circuit]
#[allow(clippy::too_many_arguments)]
fn schema_demo(
    o: Private<Outer>,
    n: Public<u64>,
    b: Private<[u8; 4]>,
    w: Public<[u32; 2]>,
    f: Public<Field>,
    day: Public<Date>,
    doc: Private<Text>,
    tier: Private<Choice<Tier>>,
    allowed: Public<Bitfield<Country>>,
) {
    let _ = (o, n, b, w, f, day, doc, tier, allowed);
}

#[test]
fn circuit_schema_describes_every_type_once() {
    let s = SchemaDemoInputs::schema();
    let v: serde_json::Value = serde_json::from_str(&s).unwrap();
    assert_eq!(v["version"], 2);
    assert_eq!(v["circuit"], "schema_demo");
    let names: Vec<&str> = v["inputs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|i| i["name"].as_str().unwrap())
        .collect();
    assert_eq!(
        names,
        ["o", "n", "b", "w", "f", "day", "doc", "tier", "allowed"]
    );
    assert_eq!(
        v["types"]["Outer"].to_string(),
        r#"{"struct":[{"name":"inner","type":{"ref":"Inner"}},{"name":"tag","type":{"array":{"len":2,"of":{"uint":8}}}},{"name":"c","type":{"uint":32}}]}"#
    );
    assert_eq!(
        v["types"]["Choice<Tier>"].to_string(),
        r#"{"encoding":{"choice":"Tier"},"newtype":"field"}"#
    );
    assert_eq!(
        v["types"]["Tier"]["enum"],
        serde_json::json!(["Retail", "Accredited"])
    );
    assert_eq!(v["types"]["Country"]["enum"].as_array().unwrap().len(), 249);
    assert_eq!(v["types"]["Date"]["encoding"]["date"], "yyyymmdd");
    assert_eq!(
        v["public_inputs"],
        serde_json::json!(["n", "w[0]", "w[1]", "f", "day", "allowed"])
    );
}

/// Off-circuit, circuit code runs natively: `Field` arithmetic, comparisons and
/// hints compute what the solver would, and a failed `require` panics at its line.
#[test]
fn circuit_code_runs_natively_on_the_host() {
    use xark::{require, require_eq};
    let (a, b) = (Field::from(6u8), Field::from(7u8));
    assert_eq!((a * b + a - b).to_decimal(), "41");
    assert_eq!((-a + a).to_decimal(), "0");
    assert_eq!((a.inv() * a).to_decimal(), "1");
    assert_eq!(a.pow(3).to_decimal(), "216");
    assert!(a == Field::from(6u8) && a != b);
    assert!(a.lt::<8>(b) && !b.lt::<8>(a) && a < 7u8);
    assert_eq!(
        Field::from(5u8).to_bits::<3>().map(|b| b.to_decimal()),
        ["1", "0", "1"]
    );
    let qr = Field::hint_div_rem(Field::from(17u8), Field::from(5u8));
    assert_eq!([qr[0].to_decimal(), qr[1].to_decimal()], ["3", "2"]);
    // p − 1 is −1.
    assert_eq!(
        (Field::from(0u8) - Field::from(1u8) + Field::from(1u8)).to_decimal(),
        "0"
    );

    require(a < 7u8);
    require_eq(a * b, 42u64);
    let fails = |f: fn()| {
        let msg = std::panic::catch_unwind(f).expect_err("must fail");
        let msg = msg
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| msg.downcast_ref::<&str>().copied())
            .unwrap_or_default()
            .to_string();
        assert!(msg.contains("requirement failed"), "{msg}");
    };
    fails(|| require(Field::from(9u8) < 7u8));
    fails(|| require_eq(Field::from(1u8), 2u64));
    fails(|| {
        let _ = Field::from(8u8).to_bits::<3>(); // 8 doesn't fit 3 bits
    });
    // Inside a witness-only region requirements aren't constraints, so aren't checked.
    xark::witness_begin();
    require_eq(Field::from(1u8), 2u64);
    xark::witness_end();
}

mod case {
    use xark::prelude::*;
    include!("cases/schema_match.rs");
}

/// The host's `<Fn>Inputs::schema()` is the very `schema.json` the build writes.
#[test]
fn host_schema_is_the_built_schema() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/test-cases");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("schema_match.rs");
    let src = format!(
        "#![no_std]\nuse xark::prelude::*;\n{}",
        include_str!("cases/schema_match.rs")
    );
    std::fs::write(&path, src).unwrap();
    let c = xark_test_harness::compile_file(&path, "schema_match", "bn254");
    assert!(c.status_success, "{}", c.stderr);
    let built: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(c.out_dir.join("schema.json")).unwrap())
            .unwrap();
    let host: serde_json::Value = serde_json::from_str(&case::SchemaMatchInputs::schema()).unwrap();
    assert_eq!(built, host);
}

/// `#[input]` on an `impl` leaves the block as written outside a client build, and its
/// values cross in their natural JSON forms (`xark::client`), as a client sees them.
mod exported {
    use xark::prelude::*;

    #[input]
    pub struct Window {
        pub from: Date,
        pub to: Date,
    }

    #[input]
    impl Window {
        /// From `from` on, with no end.
        pub fn starting(from: impl Into<Date>) -> Window {
            Window {
                from: from.into(),
                to: Date::MAX,
            }
        }
        pub fn until(self, to: Date) -> Self {
            Window { to, ..self }
        }
        fn private_helper(&self) -> bool {
            true
        }
    }

    #[test]
    fn exported_blocks_are_plain_rust() {
        let w = Window::starting("2026-10-20").until(Date::new(2027, 1, 1));
        assert!(w.private_helper());
        let json = xark::client::to_json(&w).unwrap();
        assert_eq!(
            json,
            serde_json::json!({ "from": "2026-10-20", "to": "2027-01-01" })
        );
        let back: Window = xark::client::from_json(&json).unwrap();
        assert_eq!(xark::client::to_json(&back).unwrap(), json);
    }
}
