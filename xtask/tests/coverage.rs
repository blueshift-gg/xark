//! `cargo xtask lean-export --coverage` on a circuit with four `add32` calls: one on
//! fresh variables (the proven template's rows); one with a constant word whose
//! obligation (its constants are bits) BLAKE2s's calls already commit, covered; one
//! whose word is one variable repeated (linear-combination plugs, whose bit
//! assumption only the caller can enforce); and one with a word of 2s, which no
//! committed obligation covers (and none can: 2 isn't a bit). The last two must fail
//! the check, naming their sites.

use std::path::Path;
use std::process::Command;

#[test]
fn a_call_whose_rows_differ_from_the_proven_template_fails_naming_its_site() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("coverage-folded-add32");
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(
        dir.join("Cargo.toml"),
        format!(
            "[package]\nname = \"folded-add32\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n\
             [lib]\npath = \"src/lib.rs\"\n\n[dependencies]\n\
             xark = {{ path = \"{lang}\" }}\nxark-bits = {{ path = \"{bits}\" }}\n\n\
             [lints.rust]\nunexpected_cfgs = {{ level = \"warn\", check-cfg = ['cfg(xark)'] }}\n\n\
             [workspace]\n",
            lang = root.join("crates/lang").display(),
            bits = root.join("gadgets/xark-bits").display(),
        ),
    )
    .unwrap();
    std::fs::write(
        dir.join("src/lib.rs"),
        "use xark::{Field, Private, circuit};\n\
         \n\
         #[circuit]\n\
         pub fn folded(a: Private<[Field; 32]>, b: Private<[Field; 32]>, x: Private<Field>) {\n\
         \x20   let fresh = xark_bits::add32(a, b);\n\
         \x20   xark_bits::add32(Field::from(0x6a09e667u32).to_bits::<32>(), fresh);\n\
         \x20   xark_bits::add32([x; 32], fresh);\n\
         \x20   xark_bits::add32([Field::from(2u8); 32], fresh);\n\
         }\n",
    )
    .unwrap();

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
    assert!(!out.status.success(), "the check passed:\n{text}");
    let line = |n: u32| {
        text.lines()
            .find(|l| l.contains(&format!("src/lib.rs:{n}:")))
            .unwrap_or_else(|| panic!("no report for src/lib.rs:{n}:\n{text}"))
            .to_string()
    };
    let fresh = line(5);
    assert!(
        fresh.contains("xark_bits::add32")
            && fresh.contains("folded-add32")
            && fresh.contains("covered"),
        "{fresh}"
    );
    let consts = line(6);
    assert!(
        consts.contains("covered with constant plugs") && !consts.contains("not allowlisted"),
        "{consts}"
    );
    let aliased = line(7);
    assert!(
        aliased.contains("the caller must enforce Assumptions")
            && aliased.contains("not allowlisted"),
        "{aliased}"
    );
    let twos = line(8);
    let name = twos
        .split("covered with constant plugs (")
        .nth(1)
        .and_then(|r| r.split(')').next())
        .unwrap_or_else(|| panic!("{twos}"));
    assert!(
        text.contains(&format!("has no obligation {name}")),
        "{text}"
    );
}
