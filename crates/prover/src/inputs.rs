//! Input leaves (`id.dob`, `msg[3]`) to the solver's `VarId → decimal` map.
//!
//! Values in their natural forms (a date, a hash's bytes, a point) are encoded into
//! leaves by the schema codec (`xark-schema`: `xark prove --inputs`, xark-wasm's
//! `encodeInputs`, generated clients); this takes the leaves. A value may also be
//! nested ([`InputValue::Map`] / [`InputValue::List`]) mirroring the input's shape,
//! which [`flatten_inputs`] turns into the leaf names.

use std::collections::BTreeMap;

use xark_ir::VarId;
use xark_ir::primitive::VarRole;

/// A structured input value, as parsed from JSON (CLI) or a JS object (wasm).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InputValue {
    /// A scalar: decimal, `0x`-hex, or a logical value such as a hex byte string.
    Scalar(String),
    /// An array or tuple: element `i` becomes `name[i]`.
    List(Vec<InputValue>),
    /// A struct: field `f` becomes `name.f`.
    Map(Vec<(String, InputValue)>),
}

/// Flatten nested values to `leaf-name → scalar`, using the compiler's structural-flatten
/// names (`name.field`, `name[i]`). Scalars pass through under their own name, so flat and
/// nested inputs can be mixed.
pub fn flatten_inputs(
    entries: impl IntoIterator<Item = (String, InputValue)>,
) -> BTreeMap<String, String> {
    fn go(name: String, v: InputValue, out: &mut BTreeMap<String, String>) {
        match v {
            InputValue::Scalar(s) => {
                out.insert(name, s);
            }
            InputValue::List(xs) => {
                for (i, x) in xs.into_iter().enumerate() {
                    go(format!("{name}[{i}]"), x, out);
                }
            }
            InputValue::Map(fs) => {
                for (f, x) in fs {
                    go(format!("{name}.{f}"), x, out);
                }
            }
        }
    }
    let mut out = BTreeMap::new();
    for (k, v) in entries {
        go(k, v, &mut out);
    }
    out
}

fn logical_root(leaf: &str) -> &str {
    let cut = leaf.find(['[', '.']).unwrap_or(leaf.len());
    &leaf[..cut]
}

/// Resolve `leaf → value` inputs to `VarId → decimal` for the solver. Each value is
/// a field element, decimal or `0x`-hex (`0 <= x < p`; anything else is an error,
/// not reduced). Every input leaf must be given, and only input leaves.
pub fn resolve_input_ids(
    vars: &[xark_ir::primitive::Var],
    inputs: &BTreeMap<String, String>,
) -> Result<BTreeMap<VarId, String>, String> {
    // Only inputs can be supplied: a derived (solver-computed) var is never settable.
    let input_vars: Vec<xark_ir::primitive::Var> = vars
        .iter()
        .filter(|v| !matches!(v.role, VarRole::Derived))
        .cloned()
        .collect();
    let vars = &input_vars[..];
    let by_name: BTreeMap<&str, VarId> = vars.iter().map(|v| (v.name.as_str(), v.id)).collect();
    let mut id_inputs: BTreeMap<VarId, String> = BTreeMap::new();

    for (k, v) in inputs {
        if let Some(&id) = by_name.get(k.as_str()) {
            let dec = crate::field_input_decimal(v)
                .map_err(|e| format!("invalid value for input `{k}`: {e}"))?;
            id_inputs.insert(id, dec);
            continue;
        }

        // Unknown — list the circuit's logical inputs (deduped roots, not leaves).
        let mut roots: Vec<&str> = vars.iter().map(|v| logical_root(&v.name)).collect();
        roots.sort_unstable();
        roots.dedup();
        return Err(format!("unknown input `{k}` (circuit inputs: {roots:?})"));
    }
    // Every input must be given — named here, rather than as the solver's
    // "missing input for variable <id>".
    let mut missing: Vec<&str> = Vec::new();
    for v in vars.iter().filter(|v| !id_inputs.contains_key(&v.id)) {
        let root = logical_root(&v.name);
        if !missing.contains(&root) {
            missing.push(root);
        }
    }
    if !missing.is_empty() {
        let list = missing
            .iter()
            .map(|m| format!("`{m}`"))
            .collect::<Vec<_>>()
            .join(", ");
        return Err(format!("missing input {list}"));
    }
    Ok(id_inputs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use xark_ir::primitive::Var;

    fn var(id: u32, name: &str, role: VarRole) -> Var {
        Var {
            id: id as VarId,
            name: name.to_string(),
            role,
        }
    }

    fn vars() -> Vec<Var> {
        vec![
            var(0, "id.dob", VarRole::PrivateInput),
            var(1, "id.salt", VarRole::PrivateInput),
            var(2, "msg[0]", VarRole::PrivateInput),
            var(3, "msg[1]", VarRole::PrivateInput),
            var(4, "out", VarRole::PublicInput),
            var(5, "tmp", VarRole::Derived),
        ]
    }

    fn resolve(entries: Vec<(&str, InputValue)>) -> Result<BTreeMap<VarId, String>, String> {
        let flat = flatten_inputs(entries.into_iter().map(|(k, v)| (k.to_string(), v)));
        resolve_input_ids(&vars(), &flat)
    }

    use InputValue::{List, Map, Scalar};

    #[test]
    fn nested_values_resolve_like_flat_leaves() {
        let got = resolve(vec![
            (
                "id",
                Map(vec![
                    ("dob".into(), Scalar("19940312".into())),
                    ("salt".into(), Scalar("0x10".into())),
                ]),
            ),
            ("msg", List(vec![Scalar("1".into()), Scalar("2".into())])),
            ("out", Scalar("9".into())),
        ])
        .unwrap();
        let want: BTreeMap<VarId, String> =
            [(0, "19940312"), (1, "16"), (2, "1"), (3, "2"), (4, "9")]
                .into_iter()
                .map(|(i, v)| (i as VarId, v.to_string()))
                .collect();
        assert_eq!(got, want);
    }

    /// Natural forms are the schema codec's: a byte array given as hex isn't split
    /// here (that's `encodeInputs` / `--inputs`), it's an unknown leaf.
    #[test]
    fn values_are_leaves() {
        let err = resolve(vec![("msg", Scalar("0x0102".into()))]).unwrap_err();
        assert!(err.contains("unknown input `msg`"), "{err}");
    }

    #[test]
    fn derived_vars_are_not_settable() {
        let err = resolve(vec![("tmp", Scalar("1".into()))]).unwrap_err();
        assert!(err.contains("unknown input `tmp`"), "{err}");
        assert!(
            !err.contains("\"tmp\""),
            "derived vars aren't listed as inputs: {err}"
        );
    }

    #[test]
    fn field_inputs_must_be_field_elements() {
        let p = "21888242871839275222246405745257275088548364400416034343698204186575808495617";
        let p_minus_1 =
            "21888242871839275222246405745257275088548364400416034343698204186575808495616";
        let all = |out: &str| {
            resolve(vec![
                ("id.dob", Scalar("0".into())),
                ("id.salt", Scalar("0".into())),
                ("msg", List(vec![Scalar("0".into()), Scalar("0".into())])),
                ("out", Scalar(out.into())),
            ])
        };
        assert_eq!(all(p_minus_1).unwrap()[&4], p_minus_1);
        assert_eq!(all("0x10").unwrap()[&4], "16");
        for bad in [
            p,
            "-1",
            "0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001",
        ] {
            let err = all(bad).unwrap_err();
            assert!(err.contains("not a field element"), "{bad}: {err}");
        }
    }

    #[test]
    fn missing_inputs_are_named() {
        let err = resolve(vec![("out", InputValue::Scalar("1".into()))]).unwrap_err();
        assert_eq!(err, "missing input `id`, `msg`");
    }

    #[test]
    fn bad_values_name_the_input() {
        let err = resolve(vec![("out", Scalar("nine".into()))]).unwrap_err();
        assert!(err.contains("`out`"), "{err}");
    }
}
