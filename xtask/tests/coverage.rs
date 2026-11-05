//! `cargo xtask lean-export --coverage` on small circuits: one per kind of call the
//! check classifies, each with a call it must reject, named by its site.

use std::path::Path;
use std::process::Command;

/// Build `src` as circuit crate `name` (depending on `xark`, `xark-bits` and `xark-bignum`), run
/// the coverage check on it, and return whether it passed and its output.
fn coverage(name: &str, src: &str) -> (bool, String) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("coverage-{name}"));
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(
        dir.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n\
             [lib]\npath = \"src/lib.rs\"\n\n[dependencies]\n\
             xark = {{ path = \"{lang}\" }}\nxark-bits = {{ path = \"{bits}\" }}\n\
             xark-bignum = {{ path = \"{bignum}\" }}\n\n\
             [lints.rust]\nunexpected_cfgs = {{ level = \"warn\", check-cfg = ['cfg(xark)'] }}\n\n\
             [workspace]\n",
            lang = root.join("crates/lang").display(),
            bits = root.join("gadgets/xark-bits").display(),
            bignum = root.join("gadgets/xark-bignum").display(),
        ),
    )
    .unwrap();
    std::fs::write(dir.join("src/lib.rs"), src).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_xtask"))
        .args(["lean-export", "--coverage", "--circuit"])
        .arg(&dir)
        .output()
        .unwrap();
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    (out.status.success(), text)
}

/// The report lines for site `at` (a site has one per class).
fn report(text: &str, at: &str) -> String {
    let found: Vec<&str> = text
        .lines()
        .filter(|l| l.contains(at) && (l.contains(" call ") || l.contains(" calls ")))
        .collect();
    assert!(!found.is_empty(), "no report for {at}:\n{text}");
    found.join("\n")
}

/// The report lines for the circuit's own `src/lib.rs:<n>:`.
fn lines(text: &str, n: u32) -> String {
    report(text, &format!("/src/lib.rs:{n}:"))
}

/// Where `xor32` calls `xor`, which names the site of every `xor` call through it.
const XOR32: &str = "gadgets/xark-bits/src/lib.rs:32:";

/// Four `add32` calls: on fresh variables (the proven template's rows); with a
/// constant word whose obligation (its constants are bits) BLAKE2s's calls already
/// commit; with a word that is one variable repeated (linear-combination plugs,
/// whose bit assumption only the caller can enforce); and with a word of 2s, which
/// no committed obligation covers (and none can: 2 isn't a bit). And a `to_bits` at
/// width 5, which no harness proves: its rows differ from every template. The last
/// three fail the check, naming their sites.
#[test]
fn a_call_whose_rows_differ_from_the_proven_template_fails_naming_its_site() {
    let (ok, text) = coverage(
        "folded-add32",
        "use xark::{Field, Private, circuit};\n\
         \n\
         #[circuit]\n\
         pub fn folded(a: Private<[Field; 32]>, b: Private<[Field; 32]>, x: Private<Field>) {\n\
         \x20   let fresh = xark_bits::add32(a, b);\n\
         \x20   xark_bits::add32(Field::from(0x6a09e667u32).to_bits::<32>(), fresh);\n\
         \x20   xark_bits::add32([x; 32], fresh);\n\
         \x20   xark_bits::add32([Field::from(2u8); 32], fresh);\n\
         \x20   let _ = x.to_bits::<5>();\n\
         }\n",
    );
    assert!(!ok, "the check passed:\n{text}");
    let fresh = lines(&text, 5);
    assert!(
        fresh.contains("xark_bits::add32") && fresh.contains(": 1 call covered"),
        "{fresh}"
    );
    let consts = lines(&text, 6);
    assert!(
        consts.contains("covered with constant plugs") && !consts.contains("not allowlisted"),
        "{consts}"
    );
    let aliased = lines(&text, 7);
    assert!(
        aliased.contains("the caller must enforce Assumptions")
            && aliased.contains("not allowlisted"),
        "{aliased}"
    );
    let twos = lines(&text, 8);
    let name = twos
        .split("covered with constant plugs (")
        .nth(1)
        .and_then(|r| r.split(')').next())
        .unwrap_or_else(|| panic!("{twos}"));
    assert!(
        text.contains(&format!("has no obligation {name}")),
        "{text}"
    );
    let five = lines(&text, 9);
    assert!(
        five.contains("xark::lang::to_bits")
            && five.contains("different rows (template ")
            && five.contains("not allowlisted"),
        "{five}"
    );
}

/// A constant operand folds the proven template: `!x` as `xor` with all-ones is
/// the `xor` template with plug 0 := 1, its hint folded into `1 − x` and its row
/// closed true, and `to_bits` of a constant folds to no row at all. Both are
/// covered with folded constants, and the check passes. (A fold that closes a false
/// row can't come from a circuit, since the frontend refuses to compile one; the
/// frontend's `a_fold_that_closes_a_false_row_fails` checks the tool rejects it.)
#[test]
fn a_call_with_folded_constants_is_covered() {
    let (ok, text) = coverage(
        "folded-consts",
        "use xark::{Field, Private, circuit};\n\
         \n\
         #[circuit]\n\
         pub fn folded(a: Private<Field>) {\n\
         \x20   let x = a.to_bits::<32>();\n\
         \x20   let ones = Field::from(0xffff_ffffu32).to_bits::<32>();\n\
         \x20   let _ = xark_bits::xor32(ones, x);\n\
         }\n",
    );
    assert!(ok, "the check failed:\n{text}");
    let ones = lines(&text, 6);
    assert!(
        ones.contains("xark::lang::to_bits")
            && ones.contains("covered with folded constants (no assumptions)"),
        "{ones}"
    );
    // Bit 0 is a linear form (`a − Σ 2ⁱ·bᵢ`), so its call has an LC plug: a proven
    // bit, from the covered decomposition.
    let xor = report(&text, XOR32);
    assert!(
        xor.contains(": 31 calls covered with folded constants (k_")
            && xor.contains(": 1 call covered with LC plugs (assumptions discharged by producers)"),
        "{xor}"
    );
}

/// A `to_bits` the frontend answers from its memo emits nothing: it is covered when
/// its bits are those of a covered decomposition of the same input at the same
/// width. A memo hit of a width no template proves (5) is still covered, as bits of
/// proven bits: the first decomposition's own rows pin each bit, and they sum to the
/// input. That first decomposition isn't, and fails the check. (A silent call
/// returning another input's bits can't come from a circuit, since the memo is keyed
/// by input; `coverage::tests` checks the tool rejects it.)
#[test]
fn a_memo_hit_is_covered_by_the_decomposition_it_reuses() {
    let (ok, text) = coverage(
        "memo-hits",
        "use xark::{Field, Private, circuit};\n\
         \n\
         #[circuit]\n\
         pub fn memo(a: Private<Field>, b: Private<Field>) {\n\
         \x20   let _ = a.to_bits::<8>();\n\
         \x20   let _ = a.to_bits::<8>();\n\
         \x20   let _ = b.to_bits::<5>();\n\
         \x20   let _ = b.to_bits::<5>();\n\
         }\n",
    );
    assert!(!ok, "the check passed:\n{text}");
    let first = lines(&text, 5);
    assert!(first.ends_with(": 1 call covered"), "{first}");
    let again = lines(&text, 6);
    assert!(
        again.ends_with(": 1 call covered: reuses a covered decomposition"),
        "{again}"
    );
    let five = lines(&text, 7);
    assert!(
        five.contains("different rows (template ") && five.contains("not allowlisted"),
        "{five}"
    );
    let again = lines(&text, 8);
    assert!(
        again.ends_with(": 1 call covered: bits of producer bits"),
        "{again}"
    );
}

/// `xor`'s soundness assumes bit inputs. A linear-combination plug `1 − y` is
/// covered when `y` is a proven bit: an output of a covered `to_bits` (a producer),
/// or a variable a `require_bool` row pins. A plug `1 − q` for an unpinned `q`
/// isn't: its assumption is the caller's, and an unlisted one fails.
#[test]
fn lc_plugs_are_covered_only_when_every_input_is_a_proven_bit() {
    let (ok, text) = coverage(
        "bit-plugs",
        "use xark::{Field, Private, circuit};\n\
         use xark_bits::{not32, xor32};\n\
         \n\
         #[circuit]\n\
         pub fn plugs(a: Private<Field>, b: Private<Field>, p: Private<Field>, q: Private<Field>) {\n\
         \x20   let x = a.to_bits::<32>();\n\
         \x20   let _ = xor32(x, not32(b.to_bits::<32>()));\n\
         \x20   p.require_bool();\n\
         \x20   let _ = xor32(x, not32([p; 32]));\n\
         \x20   let _ = xor32(x, not32([q; 32]));\n\
         }\n",
    );
    assert!(!ok, "the check passed:\n{text}");
    let xor = report(&text, XOR32);
    assert!(
        xor.lines().any(|l| l
            .ends_with(": 32 calls covered with LC plugs (assumptions discharged by producers)")),
        "{xor}"
    );
    assert!(
        xor.contains(
            ": 32 calls covered with LC plugs (assumptions discharged by producers and booleanity rows)"
        ),
        "{xor}"
    );
    assert!(
        xor.contains(": 32 calls LC plugs: the caller must enforce Assumptions — not allowlisted"),
        "{xor}"
    );
}

/// A `mul_cert_k1` nested in a covered `ec_add_k1_check` is covered by the
/// enclosing proof (its rows are part of that call's); the same certificates nested
/// in an `ec_add_k1_check` with linear-combination plugs no allowlist entry names,
/// and the gadget called directly with such plugs, are not.
#[test]
fn a_nested_call_is_covered_only_inside_a_covered_parent() {
    let (ok, text) = coverage(
        "nested-cert",
        "use xark::{Field, Private, circuit};\n\
         \n\
         #[circuit]\n\
         pub fn nested(p: Private<[Field; 120]>, x: Private<Field>, z: Private<Field>) {\n\
         \x20   let l = |i: usize| core::array::from_fn::<Field, 8, _>(|j| p[8 * i + j]);\n\
         \x20   xark_bignum::ec_add_k1_check(l(0), l(1), l(2), l(3), l(4), l(5), l(6), l(7));\n\
         \x20   xark_bignum::mul_cert_k1([x; 8], [x; 8], [x; 8]);\n\
         \x20   xark_bignum::ec_add_k1_check([z; 8], l(8), l(9), l(10), l(11), l(12), l(13), l(14));\n\
         }\n",
    );
    assert!(!ok, "the check passed:\n{text}");
    let add = lines(&text, 6);
    assert!(add.ends_with(": 1 call covered"), "{add}");
    let nested: Vec<&str> = text
        .lines()
        .filter(|l| {
            l.starts_with("xark_bignum::mul_cert_k1") && l.contains("xark-bignum/src/lib.rs")
        })
        .collect();
    let inside: Vec<&&str> = nested.iter().filter(|l| l.contains("inside")).collect();
    assert_eq!(inside.len(), 4, "{text}");
    for l in inside {
        assert!(
            l.ends_with(": 1 call covered: inside a covered `xark_bignum::ec_add_k1_check` call"),
            "{l}"
        );
    }
    // The LC-plug parent's certificates are classified on their own.
    assert!(nested.len() > 4, "{text}");
    let bad = lines(&text, 8);
    assert!(
        bad.ends_with(": 1 call LC plugs: the caller must enforce Assumptions — not allowlisted"),
        "{bad}"
    );
    // `[x; 8]` folds the product at `ω = −1` (`Σ (−1)ʲ·x = 0`) to a constant.
    let direct = lines(&text, 7);
    assert!(
        direct.ends_with(
            ": 1 call LC plugs: the caller must enforce Assumptions (after folding constants) \
             — not allowlisted"
        ),
        "{direct}"
    );
}

/// A `#[gadget]` with no harness under `formal/templates/` has no proof: its call
/// fails the check, naming the gadget and its site, instead of being skipped.
#[test]
fn a_gadget_with_no_harness_fails_naming_it() {
    let (ok, text) = coverage(
        "harness-less",
        "use xark::{Field, Private, circuit, gadget};\n\
         \n\
         #[gadget]\n\
         pub fn square(x: Field) -> Field {\n\
         \x20   x * x\n\
         }\n\
         \n\
         #[circuit]\n\
         pub fn unproven(a: Private<Field>) {\n\
         \x20   xark::require_eq(square(a), Field::from(4u8));\n\
         }\n",
    );
    assert!(!ok, "the check passed:\n{text}");
    assert!(
        text.lines().any(|l| l.contains("harness_less::square")
            && l.contains("no harness under formal/templates/")
            && l.contains("/src/lib.rs:10:")),
        "{text}"
    );
}
