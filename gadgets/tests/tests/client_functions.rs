//! `#[input]` on an `impl` block makes its methods client functions, from any crate:
//! a gadget's functions reach the client of every circuit whose inputs use its
//! types, and nothing else.

mod common;
use common::{tempdir, xark_bin};
use std::path::Path;
use std::process::Command;

fn write(path: &Path, text: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, text).unwrap();
}

/// `xark <args>` in `dir`: success, and stdout + stderr.
fn xark(dir: &Path, args: &[&str]) -> (bool, String) {
    let o = Command::new(xark_bin())
        .args(args)
        .current_dir(dir)
        .output()
        .expect("invoke xark");
    let out = String::from_utf8_lossy(&o.stdout).into_owned() + &String::from_utf8_lossy(&o.stderr);
    (o.status.success(), out)
}

#[test]
fn a_gadgets_functions_reach_the_client() {
    let tmp = tempdir();
    let lang = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../crates/lang");
    let lang = lang.canonicalize().unwrap();
    let lints = "[lints.rust]\nunexpected_cfgs = { level = \"warn\", check-cfg = ['cfg(xark)'] }\n";
    // A third-party gadget: an input type with its own functions, and a helper
    // for a type no circuit below takes.
    write(
        &tmp.path().join("gadget/Cargo.toml"),
        &format!(
            "[package]\nname = \"gadget\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\
             [dependencies]\nxark = {{ path = {:?} }}\n{lints}",
            lang.display().to_string()
        ),
    );
    write(
        &tmp.path().join("gadget/src/lib.rs"),
        "#![cfg_attr(xark, no_std)]\nuse xark::prelude::*;\n\
         /// A range of positions.\n\
         #[input]\npub struct Span { pub lo: u32, pub hi: u32 }\n\
         #[input]\nimpl Span {\n\
         /// `lo..hi`, checked.\n\
         pub fn new(lo: u32, hi: u32) -> Span { assert!(lo <= hi, \"lo above hi\"); Span { lo, hi } }\n\
         /// How many positions.\n\
         pub fn len(&self) -> u32 { self.hi - self.lo }\n\
         pub fn join(self, other: Self) -> Self { Span { lo: self.lo.min(other.lo), hi: self.hi.max(other.hi) } }\n\
         pub fn covers(&self, other: &Span) -> bool { self.lo <= other.lo && other.hi <= self.hi }\n\
         pub fn join_all(self, others: [Self; 2]) -> Span { self.join(others[0]).join(others[1]) }\n}\n\
         #[input]\npub struct Unused { pub x: Field }\n\
         #[input]\nimpl Unused {\npub fn zero() -> Unused { Unused { x: Field::zero() } }\n}\n",
    );
    write(
        &tmp.path().join("circ/Cargo.toml"),
        &format!(
            "[package]\nname = \"circ\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\
             [dependencies]\nxark = {{ path = {:?} }}\n\
             gadget = {{ path = \"../gadget\" }}\n[workspace]\n{lints}",
            lang.display().to_string()
        ),
    );
    write(
        &tmp.path().join("circ/src/lib.rs"),
        "#![cfg_attr(xark, no_std)]\nuse xark::prelude::*;\nuse gadget::Span;\n\
         #[circuit]\npub fn circ(s: Private<Span>, n: Public<u32>) {\n\
         require_eq(Field::from(s.hi) - Field::from(s.lo), Field::from(n));\n}\n",
    );
    let circ = tmp.path().join("circ");
    let (ok, out) = xark(&circ, &["build"]);
    assert!(ok, "build failed:\n{out}");
    let (ok, out) = xark(&circ, &["client"]);
    assert!(ok, "client failed:\n{out}");
    assert!(out.contains("skipping `Unused::zero`"), "{out}");
    let dir = circ.join("target/xark/circ");
    assert!(dir.join("client.wasm").exists());
    let ts = std::fs::read_to_string(dir.join("circ.ts")).unwrap();
    for want in [
        "export const Span = {",
        "   * `lo..hi`, checked.",
        "  new(lo: U32, hi: U32): SpanValue {",
        "  len(span: Span): number {",
        // `len` is also a method on the values `new` returns.
        "export class SpanValue {",
        "  len(): number {\n    return Span.len(this);",
        // `Self` is the type, and `&T` a `T`, in parameters as in results.
        "  join(span: Span, other: Span): SpanValue {",
        "  covers(span: Span, other: Span): boolean {",
        "  joinAll(span: Span, others: readonly [Span, Span]): SpanValue {",
    ] {
        assert!(ts.contains(want), "missing {want:?} in:\n{ts}");
    }
    assert!(!ts.contains("Unused"), "{ts}");
}

/// A copy of `examples/arithmetic_square` in `tmp`, with `extra` appended to its
/// `src/lib.rs`.
fn square(tmp: &Path, extra: &str) -> std::path::PathBuf {
    let dir = tmp.join("square");
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/arithmetic_square");
    for f in ["Cargo.toml", "src/lib.rs"] {
        let text = std::fs::read_to_string(src.join(f)).unwrap();
        // The copy's path dependencies, absolute.
        let abs = src.join("../../crates").canonicalize().unwrap();
        let text = text.replace("../../crates", abs.to_str().unwrap());
        write(
            &dir.join(f),
            &if f == "src/lib.rs" {
                text + extra
            } else {
                text
            },
        );
    }
    dir
}

/// A circuit with no client functions gets no `client.wasm` (nor its loader).
#[test]
fn no_functions_no_module() {
    let tmp = tempdir();
    let dir = square(tmp.path(), "");
    let (ok, out) = xark(&dir, &["build"]);
    assert!(ok, "build failed:\n{out}");
    let (ok, out) = xark(&dir, &["client"]);
    assert!(ok, "client failed:\n{out}");
    let out_dir = dir.join("target/xark/arithmetic_square");
    assert!(!out_dir.join("client.wasm").exists());
    let ts = std::fs::read_to_string(out_dir.join("arithmetic_square.ts")).unwrap();
    assert!(ts.contains("  client: false,") && !ts.contains(".call("));
}

/// Host code that doesn't build for wasm fails `xark client`, showing why, rather
/// than quietly writing a client without the Rust functions; `--no-functions`
/// skips them on purpose.
#[test]
fn a_client_build_failure_is_an_error() {
    let tmp = tempdir();
    let dir = square(
        tmp.path(),
        "\n#[cfg(xark_client)]\ncompile_error!(\"host code that can't build for wasm\");\n",
    );
    let (ok, out) = xark(&dir, &["build"]);
    assert!(ok, "build failed:\n{out}");
    let (ok, out) = xark(&dir, &["client"]);
    assert!(!ok, "client should fail:\n{out}");
    assert!(out.contains("host code that can't build for wasm"), "{out}");
    assert!(
        out.contains("--no-functions") && !out.contains("✅"),
        "{out}"
    );
    let (ok, out) = xark(&dir, &["client", "--no-functions"]);
    assert!(ok, "client --no-functions failed:\n{out}");
}

/// A generic exported function is refused where it's written, in any build: a client
/// couldn't choose its type (and the `client.wasm` build would fail obscurely).
#[test]
fn a_generic_function_is_refused() {
    let tmp = tempdir();
    let dir = square(
        tmp.path(),
        "\nmod generic {\nuse xark::prelude::*;\n\
         #[input]\npub struct W { pub x: u32 }\n\
         #[input]\nimpl W {\npub fn with<T: Into<u32>>(self, x: T) -> W { W { x: x.into() } }\n}\n}\n",
    );
    let (ok, out) = xark(&dir, &["build"]);
    assert!(!ok, "build should fail:\n{out}");
    assert!(
        out.contains("an exported function can't be generic"),
        "{out}"
    );
}

/// A tuple struct's fields (`"0"`) and raw identifiers (`r#type`) give a client
/// that compiles: quoted keys are read as `v["0"]`, and names lose their `r#`.
#[test]
fn tuple_structs_and_raw_identifiers() {
    let tmp = tempdir();
    let dir = square(
        tmp.path(),
        "\nmod odd {\nuse xark::prelude::*;\n\
         #[input]\npub struct Pair(pub u32, pub u32);\n\
         #[input]\npub struct Tagged { pub r#type: u32, pub pair: Pair }\n\
         #[input]\nimpl Pair {\n\
         pub fn swap(self) -> Pair { Pair(self.1, self.0) }\n\
         pub fn r#with(self, r#first: u32) -> Pair { Pair(r#first, self.1) }\n}\n\
         #[circuit]\npub fn odd(t: Private<Tagged>, r#ref: Public<Pair>) {\n\
         require_eq(Field::from(t.r#type + t.pair.0), Field::from(r#ref.0));\n}\n}\n",
    );
    // The crate's own circuit and this one: build the one named `odd`.
    let lib = dir.join("src/lib.rs");
    let text = std::fs::read_to_string(&lib).unwrap();
    std::fs::write(&lib, text.replacen("#[circuit]", "", 1)).unwrap();
    let (ok, out) = xark(&dir, &["build"]);
    assert!(ok, "build failed:\n{out}");
    let (ok, out) = xark(&dir, &["client", "-o", "client/"]);
    assert!(ok, "client failed:\n{out}");
    let ts = std::fs::read_to_string(dir.join("client/odd.ts")).unwrap();
    let schema = std::fs::read_to_string(dir.join("client/odd.schema.ts")).unwrap();
    assert!(
        !ts.contains("r#") && !schema.contains("r#"),
        "{ts}\n{schema}"
    );
    for want in [
        "this[\"0\"] = v[\"0\"];",
        "\"0\": v[\"0\"],",
        "  type: U32;",
        "  ref: Pair;",
        "  with(first: U32): PairValue {",
    ] {
        assert!(ts.contains(want), "missing {want:?} in:\n{ts}");
    }
    assert!(!ts.contains("v.\"") && !ts.contains("this.\""), "{ts}");
}

/// A circuit (module `m`, `#[circuit] fn m`) of input struct `S` with `fields`, and
/// with Rust methods when `methods`: its `xark client` result and the client's text.
fn client_for(fields: &str, methods: bool) -> (bool, String) {
    let tmp = tempdir();
    let imp = if methods {
        "#[input]\nimpl S {\npub fn same(self) -> S { self }\n}\n"
    } else {
        ""
    };
    let dir = square(
        tmp.path(),
        &format!(
            "\nmod m {{\nuse xark::prelude::*;\n\
             #[input]\npub struct S {{ {fields} }}\n{imp}\
             #[circuit]\npub fn m(s: Private<S>, n: Public<u32>) {{ let _ = s; require_eq(Field::from(n), Field::from(n)); }}\n}}\n"
        ),
    );
    let lib = dir.join("src/lib.rs");
    let text = std::fs::read_to_string(&lib).unwrap();
    std::fs::write(&lib, text.replacen("#[circuit]", "", 1)).unwrap();
    let (ok, out) = xark(&dir, &["build"]);
    assert!(ok, "build failed:\n{out}");
    let (ok, out) = xark(&dir, &["client", "-o", "client/"]);
    let ts = std::fs::read_to_string(dir.join("client/m.ts")).unwrap_or_default();
    (ok, out + &ts)
}

/// Underscores around a name are kept (`_reserved`); names JavaScript can't hold as
/// a plain property are refused, saying so, rather than generating a broken client.
#[test]
fn names_javascript_cant_hold_are_refused() {
    let (ok, out) = client_for("pub _reserved: u32, pub net_worth: u32", false);
    assert!(
        ok && out.contains("  _reserved: U32;") && out.contains("  netWorth: U32;"),
        "{out}"
    );
    let (ok, out) = client_for("pub __proto__: u32", false);
    assert!(
        !ok && out.contains("`__proto__` can't be a JavaScript property"),
        "{out}"
    );
    let (ok, out) = client_for("pub constructor: u32", true);
    assert!(
        !ok && out.contains("field named `constructor` and Rust methods"),
        "{out}"
    );
    let (ok, out) = client_for("pub constructor: u32", false);
    assert!(ok && out.contains("  constructor: U32;"), "{out}");
}
