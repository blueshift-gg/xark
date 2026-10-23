//! A circuit's inputs as the standard types every client language maps from.
//!
//! [`Model::new`] resolves `schema.json` once: each input's type becomes a [`Ty`]
//! (newtypes unwrapped, encodings turned into the standard type they stand for), and
//! the structs and enums the inputs reach are collected in order. A language target
//! (`ts.rs`) then only says how each [`Ty`] looks in that language: its own types,
//! and the JSON form xark-wasm takes and gives back. Encoding values into field
//! elements stays in the one Rust codec (`xark_schema`), which every target
//! calls into, so no target reimplements it.

use std::collections::BTreeMap;

use anyhow::{Context, Result, bail};
use serde_json::Value;

/// A standard type, as a client sees it.
#[derive(Clone, Debug, PartialEq)]
pub enum Ty {
    /// A field element.
    Field,
    /// An unsigned integer of this many bits.
    Uint(u64),
    /// `true` or `false`.
    Bool,
    /// A byte string: `[u8; N]` (`of: None`), or a byte-encoded type such as a hash or
    /// a curve point (`of: Some(name)`), of `len` bytes when that is fixed.
    Bytes {
        of: Option<String>,
        len: Option<u64>,
    },
    /// A whole number split into limbs (a non-native field element).
    Number { of: String },
    /// A calendar day.
    Date,
    /// A string of at most `max` UTF-8 bytes.
    Text { max: u64 },
    /// One variant of an enum.
    Choice(String),
    /// A set of an enum's variants.
    Set(String),
    /// `len` values of one type.
    Array(Box<Ty>, u64),
    /// Values of different types.
    Tuple(Vec<Ty>),
    /// A struct, by name (see [`Model::structs`]).
    Struct(String),
}

/// One input (or struct field).
#[derive(Clone, Debug)]
pub struct Field {
    /// As declared (`born_before`); targets apply their own case.
    pub name: String,
    pub ty: Ty,
    /// The Rust type as written (`Bitfield<Country>`), for docs.
    pub rust: String,
}

/// A circuit's inputs, resolved.
#[derive(Debug)]
pub struct Model {
    pub circuit: String,
    /// The inputs, in declaration order, and whether each is public.
    pub inputs: Vec<(Field, bool)>,
    /// Every struct an input reaches, its fields in order.
    pub structs: BTreeMap<String, Vec<Field>>,
    /// Every enum a `Choice` or `Set` names, its variants in order.
    pub enums: BTreeMap<String, Vec<String>>,
    /// The client functions (`#[input]` on an `impl`), run from `client.wasm`.
    pub exports: Vec<Export>,
    /// The digest of the circuit the client is generated from (`xark build`'s).
    pub digest: Option<String>,
}

/// A Rust method a client calls (`#[input]` on an `impl`).
#[derive(Clone, Debug)]
pub struct Export {
    /// The wasm export (`Policy.min_age`).
    pub export: String,
    /// The type it's defined on, and its own name (`Policy`, `min_age`).
    pub ty: String,
    pub name: String,
    /// `self` (`Some(false)`), `&self` (`Some(true)`), or none.
    pub receiver: Option<bool>,
    pub params: Vec<Field>,
    pub returns: Ty,
    /// Its doc comment.
    pub doc: String,
}

impl Model {
    pub fn new(schema: &Value) -> Result<Model> {
        if schema["version"].as_u64() != Some(2) {
            bail!(
                "unsupported schema version {} (expected 2: rebuild the circuit with this xark)",
                schema["version"]
            );
        }
        let mut m = Model {
            circuit: schema["circuit"]
                .as_str()
                .context("schema without `circuit`")?
                .to_string(),
            inputs: Vec::new(),
            structs: BTreeMap::new(),
            enums: BTreeMap::new(),
            exports: Vec::new(),
            digest: None,
        };
        for i in schema["inputs"].as_array().into_iter().flatten() {
            let f = m.field(schema, i)?;
            m.inputs.push((f, i["visibility"] == "public"));
        }
        Ok(m)
    }

    fn field(&mut self, schema: &Value, f: &Value) -> Result<Field> {
        let name = f["name"].as_str().unwrap_or_default();
        // `{ __proto__: … }` sets an object's prototype in JavaScript: such a value
        // could never be passed in, or read back.
        if xark_schema::camel(name) == "__proto__" {
            bail!("an input or field named `{name}` can't be a JavaScript property: rename it");
        }
        Ok(Field {
            name: name.to_string(),
            ty: self.ty(schema, &f["type"])?,
            rust: rust_type(&f["type"]),
        })
    }

    fn ty(&mut self, schema: &Value, ty: &Value) -> Result<Ty> {
        if ty == "field" {
            return Ok(Ty::Field);
        }
        if ty == "bool" {
            return Ok(Ty::Bool);
        }
        if let Some(w) = ty["uint"].as_u64() {
            return Ok(Ty::Uint(w));
        }
        if let Some(a) = ty.get("array") {
            let len = a["len"].as_u64().unwrap_or(0);
            if a["of"]["uint"] == 8 {
                return Ok(Ty::Bytes {
                    of: None,
                    len: Some(len),
                });
            }
            return Ok(Ty::Array(Box::new(self.ty(schema, &a["of"])?), len));
        }
        if let Some(t) = ty["tuple"].as_array() {
            return Ok(Ty::Tuple(
                t.iter()
                    .map(|e| self.ty(schema, e))
                    .collect::<Result<_>>()?,
            ));
        }
        let r = ty["ref"]
            .as_str()
            .with_context(|| format!("unknown schema type {ty}"))?;
        let def = &schema["types"][r];
        let enc = &def["encoding"];
        let mut variants = |e: &str| -> String {
            let names = schema["types"][e]["enum"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(|n| n.as_str().map(str::to_string))
                .collect();
            self.enums.insert(e.to_string(), names);
            e.to_string()
        };
        Ok(if enc.get("date").is_some() {
            Ty::Date
        } else if let Some(max) = enc["text"].as_u64() {
            Ty::Text { max }
        } else if let Some(e) = enc["choice"].as_str() {
            Ty::Choice(variants(e))
        } else if let Some(e) = enc["set"].as_str() {
            Ty::Set(variants(e))
        } else if enc.get("limbs").is_some() {
            Ty::Number { of: r.to_string() }
        } else if enc.is_object() {
            Ty::Bytes {
                of: Some(r.to_string()),
                len: byte_len(schema, r),
            }
        } else if let Some(n) = def.get("newtype") {
            self.ty(schema, n)?
        } else {
            if !self.structs.contains_key(r) {
                // Reserve the name first, so a struct reached twice is resolved once.
                self.structs.insert(r.to_string(), Vec::new());
                let fields = def["struct"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .map(|f| self.field(schema, f))
                    .collect::<Result<_>>()?;
                self.structs.insert(r.to_string(), fields);
            }
            Ty::Struct(r.to_string())
        })
    }

    /// Add the exported methods described by `lines` (the client module's
    /// `xark.exports` section: one JSON object per line), resolving each type written
    /// in Rust against the circuit's input types.
    ///
    /// A function whose types aren't all among them (a gadget's helper for a type this
    /// circuit doesn't take) is skipped: its `Type::name` is returned.
    pub fn add_exports(&mut self, schema: &Value, lines: &str) -> Result<Vec<String>> {
        let mut skipped = Vec::new();
        for line in lines.lines().filter(|l| !l.trim().is_empty()) {
            let d: Value = serde_json::from_str(line).context("an `xark.exports` entry")?;
            let s = |k: &str| d[k].as_str().unwrap_or_default().to_string();
            if self.exports.iter().any(|e| e.export == s("export")) {
                continue; // described twice
            }
            // Every type it names must be the circuit's: checked on a copy first, so a
            // skipped function leaves no structs or enums behind.
            let mut names = vec![s("returns")];
            names.extend(
                d["params"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .map(|p| p["type"].as_str().unwrap_or_default().to_string()),
            );
            if !d["self"].is_null() {
                names.push(s("type"));
            }
            let mut probe = Model {
                circuit: String::new(),
                inputs: Vec::new(),
                structs: self.structs.clone(),
                enums: self.enums.clone(),
                exports: Vec::new(),
                digest: None,
            };
            if names.iter().any(|n| probe.rust_ty(schema, n).is_err()) {
                skipped.push(format!("{}::{}", s("type"), s("name")));
                continue;
            }
            let params = d["params"]
                .as_array()
                .into_iter()
                .flatten()
                .map(|p| {
                    let rust = p["type"].as_str().unwrap_or_default().to_string();
                    Ok(Field {
                        name: p["name"].as_str().unwrap_or_default().to_string(),
                        ty: self.rust_ty(schema, &rust)?,
                        rust,
                    })
                })
                .collect::<Result<_>>()?;
            let returns = self.rust_ty(schema, &s("returns"))?;
            self.exports.push(Export {
                export: s("export"),
                ty: s("type"),
                name: s("name"),
                receiver: d["self"].as_str().map(|r| r == "ref"),
                params,
                returns,
                doc: s("doc"),
            });
        }
        Ok(skipped)
    }

    /// A type as written in Rust (`u16`, `[u8;4]`, `Choice<Country>`), as a standard
    /// type: a primitive, or one of the circuit's input types by name.
    fn rust_ty(&mut self, schema: &Value, rust: &str) -> Result<Ty> {
        let ty = match rust {
            "Field" => serde_json::json!("field"),
            "bool" => serde_json::json!("bool"),
            r if r.starts_with('u') && r[1..].parse::<u64>().is_ok() => {
                serde_json::json!({ "uint": r[1..].parse::<u64>()? })
            }
            r if r.starts_with('[') && r.ends_with(']') => {
                let (of, len) = r[1..r.len() - 1]
                    .rsplit_once(';')
                    .with_context(|| format!("`{r}`"))?;
                return Ok(match self.rust_ty(schema, of)? {
                    Ty::Uint(8) => Ty::Bytes {
                        of: None,
                        len: Some(len.parse()?),
                    },
                    t => Ty::Array(Box::new(t), len.parse()?),
                });
            }
            r if r.starts_with('(') && r.ends_with(')') => {
                let inner = &r[1..r.len() - 1];
                return Ok(Ty::Tuple(
                    split_top(inner)
                        .into_iter()
                        .map(|t| self.rust_ty(schema, t))
                        .collect::<Result<_>>()?,
                ));
            }
            r if schema["types"]
                .get(r)
                .is_some_and(|d| d.get("enum").is_none()) =>
            {
                serde_json::json!({ "ref": r })
            }
            r => bail!(
                "`{r}` isn't one of the circuit's input types: an exported method takes and \
                 returns those (or `Field`, `uN`, `bool`, arrays and tuples of them)"
            ),
        };
        self.ty(schema, &ty)
    }

    /// The public inputs, in declaration order.
    pub fn public(&self) -> impl Iterator<Item = &Field> {
        self.inputs.iter().filter(|(_, p)| *p).map(|(f, _)| f)
    }

    /// Whether `e` is a method named like one of its type's fields: in Rust they
    /// don't clash, but a value in most client languages can't have both.
    pub fn shares_field_name(&self, e: &Export) -> bool {
        e.receiver.is_some()
            && self
                .structs
                .get(&e.ty)
                .is_some_and(|fs| fs.iter().any(|f| f.name == e.name))
    }
}

/// `A,B<C,D>,[E;2]` split at its top-level commas.
fn split_top(s: &str) -> Vec<&str> {
    let (mut out, mut depth, mut start) = (Vec::new(), 0i32, 0);
    for (i, c) in s.char_indices() {
        match c {
            '<' | '(' | '[' => depth += 1,
            '>' | ')' | ']' => depth -= 1,
            ',' if depth == 0 => {
                out.push(&s[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    if start < s.len() {
        out.push(&s[start..]);
    }
    out
}

/// A byte-encoded named type's length, when fixed.
fn byte_len(schema: &Value, r: &str) -> Option<u64> {
    let def = &schema["types"][r];
    let enc = &def["encoding"];
    if let Some(b) = enc["bytes"].as_u64() {
        return Some(b);
    }
    def["struct"]
        .as_array()?
        .iter()
        .map(|f| byte_len(schema, f["type"]["ref"].as_str()?))
        .sum()
}

/// A Rust type as written, from a schema type.
fn rust_type(ty: &Value) -> String {
    if ty == "field" {
        return "Field".into();
    }
    if ty == "bool" {
        return "bool".into();
    }
    if let Some(w) = ty["uint"].as_u64() {
        return format!("u{w}");
    }
    if let Some(a) = ty.get("array") {
        return format!("[{}; {}]", rust_type(&a["of"]), a["len"]);
    }
    if let Some(t) = ty["tuple"].as_array() {
        let p: Vec<String> = t.iter().map(rust_type).collect();
        return format!("({})", p.join(", "));
    }
    ty["ref"].as_str().unwrap_or("?").into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resolves_standard_types() {
        let schema: Value = serde_json::from_str(
            r#"{"version": 2, "circuit": "c",
              "inputs": [
                {"name": "id", "visibility": "private", "type": {"ref": "Id"}},
                {"name": "k", "visibility": "public", "type": {"ref": "Point"}}],
              "types": {
                "Id": {"struct": [
                  {"name": "home", "type": {"ref": "Choice<Country>"}},
                  {"name": "born", "type": {"ref": "Date"}},
                  {"name": "w", "type": {"ref": "W"}}]},
                "W": {"newtype": {"uint": 32}},
                "Choice<Country>": {"newtype": "field", "encoding": {"choice": "Country"}},
                "Country": {"enum": ["AD", "US"]},
                "Date": {"newtype": "field", "encoding": {"date": "yyyymmdd"}},
                "Fp": {"struct": [{"name": "limbs", "type": {"array": {"of": "field", "len": 3}}}],
                       "encoding": {"bytes": 32, "limbs": 86}},
                "Point": {"struct": [{"name": "x", "type": {"ref": "Fp"}}, {"name": "y", "type": {"ref": "Fp"}}],
                          "encoding": {"concat": "fields"}}},
              "public_inputs": []}"#,
        )
        .unwrap();
        let m = Model::new(&schema).unwrap();
        let id = &m.structs["Id"];
        assert_eq!(id[0].ty, Ty::Choice("Country".into()));
        assert_eq!((&id[1].ty, &id[2].ty), (&Ty::Date, &Ty::Uint(32)));
        assert_eq!(m.enums["Country"], ["AD", "US"]);
        assert_eq!(
            m.inputs[1].0.ty,
            Ty::Bytes {
                of: Some("Point".into()),
                len: Some(64)
            }
        );
        assert!(!m.structs.contains_key("Fp"));
    }

    #[test]
    fn resolves_exported_signatures() {
        let schema: Value = serde_json::from_str(
            r#"{"version": 2, "circuit": "c",
              "inputs": [{"name": "p", "visibility": "public", "type": {"ref": "P"}}],
              "types": {
                "P": {"struct": [{"name": "day", "type": {"ref": "Date"}}]},
                "Date": {"newtype": "field", "encoding": {"date": "yyyymmdd"}}},
              "public_inputs": ["p.day"]}"#,
        )
        .unwrap();
        let mut m = Model::new(&schema).unwrap();
        m.add_exports(
            &schema,
            r#"{"export":"P.on","type":"P","name":"on","self":null,"params":[{"name":"d","type":"Date"},{"name":"k","type":"(u8,[u8;2])"}],"returns":"P","doc":"x"}
{"export":"P.f","type":"P","name":"f","self":"ref","params":[],"returns":"Field","doc":""}"#,
        )
        .unwrap();
        let on = &m.exports[0];
        assert_eq!(on.params[0].ty, Ty::Date);
        assert_eq!(
            on.params[1].ty,
            Ty::Tuple(vec![
                Ty::Uint(8),
                Ty::Bytes {
                    of: None,
                    len: Some(2)
                }
            ])
        );
        assert_eq!(
            (&on.returns, m.exports[1].receiver),
            (&Ty::Struct("P".into()), Some(true))
        );
        // A gadget's function for a type this circuit doesn't take: skipped.
        let other = r#"{"export":"Q.g","type":"Q","name":"g","self":null,"params":[{"name":"x","type":"Nope"}],"returns":"P","doc":""}"#;
        assert_eq!(m.add_exports(&schema, other).unwrap(), ["Q::g"]);
        assert_eq!(m.exports.len(), 2);
    }

    #[test]
    fn a_method_named_like_a_field_stays_a_function() {
        let schema: Value = serde_json::from_str(
            r#"{"version": 2, "circuit": "c",
              "inputs": [{"name": "p", "visibility": "public", "type": {"ref": "P"}}],
              "types": {"P": {"struct": [{"name": "day", "type": {"uint": 8}}]}},
              "public_inputs": ["p.day"]}"#,
        )
        .unwrap();
        let mut m = Model::new(&schema).unwrap();
        m.add_exports(
            &schema,
            r#"{"export":"P.day","type":"P","name":"day","self":"value","params":[{"name":"d","type":"u8"}],"returns":"P","doc":""}
{"export":"P.next","type":"P","name":"next","self":"value","params":[],"returns":"P","doc":""}"#,
        )
        .unwrap();
        let clash: Vec<_> = m.exports.iter().map(|e| m.shares_field_name(e)).collect();
        assert_eq!(clash, [true, false]);
        // In TypeScript, `day` is only `P.day(value, d)`; `next` is a method too.
        let ts = super::super::ts::generate(&m, "c.schema").unwrap();
        assert!(ts.contains("export class PValue {"), "{ts}");
        assert!(
            ts.contains("  next(): PValue {\n    return P.next(this);"),
            "{ts}"
        );
        assert!(ts.contains("  day(p: P, d: U8): PValue {"), "{ts}");
        assert!(!ts.contains("  day(d: U8)"), "{ts}");
    }
}
