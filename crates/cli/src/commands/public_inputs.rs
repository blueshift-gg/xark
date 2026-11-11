//! The typed public inputs `xark export` writes into the verifier crate.
//!
//! From `schema.json`, a `PublicInputs` struct with the circuit's public inputs as
//! named fields, in the Rust types a Solana program has at hand (an integer, a
//! `[u8; 32]`, a `Days<1900, 2100>` from a `Clock`, a `Country`), and its
//! `to_fields()`: the field elements the proof was made over, packed as `#[input]`
//! packs them. A program then builds what it requires by name instead of by
//! position and bit offset.
//!
//! `to_fields()` mirrors `xark_schema`'s encoder (`encode`, `pack`): every leaf the
//! codec names (`policy.{today,born_by}`, `holder.hi`) becomes a `const` Rust
//! expression for its 32 little-endian bytes, made with `xark_verifier::fields` (a
//! packed run with its `Packer`, each field's width a const generic). A type with
//! no `no_std` form here (a limbed number, an Ed25519 point) gives no typed inputs:
//! `verify` then takes the field elements. With a sample proof, the crate's self-test writes the sample's
//! public inputs as a typed value (from `xark_schema::decode_public`) and checks
//! that its `to_fields()` is the sample's and that it verifies, so the two
//! encoders are checked against each other on every export.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use ark_bn254::Fr;
use num_bigint::BigUint;
use serde_json::Value;

/// What the typed inputs add to the generated `lib.rs`.
pub struct Typed {
    /// The input types, `PublicInputs` and its `to_fields`.
    pub items: String,
    /// The sample's public inputs as a `PublicInputs` expression, for the self-test.
    pub sample: Option<String>,
}

/// The typed public inputs for `schema`, or `None` when one of them has no Rust form
/// here (or the schema doesn't match the key's `n` public inputs).
pub fn generate(schema: &Value, n: usize, sample: Option<&[Fr]>) -> Option<Typed> {
    let mut g = Gen {
        schema,
        defs: BTreeMap::new(),
        leaves: BTreeMap::new(),
        uses: Uses::default(),
    };
    let mut fields = String::new();
    let public: Vec<&Value> = schema["inputs"]
        .as_array()?
        .iter()
        .filter(|i| i["visibility"] == "public")
        .collect();
    for input in &public {
        let name = input["name"].as_str()?;
        let ty = g.rust_ty(&input["type"])?;
        let _ = writeln!(fields, "    pub {}: {ty},", ident(name));
        g.leaves(&input["type"], name, &format!("self.{}", ident(name)))?;
    }
    let order: Vec<&str> = schema["public_inputs"]
        .as_array()?
        .iter()
        .map(|l| l.as_str())
        .collect::<Option<_>>()?;
    if order.len() != n || order.len() != g.leaves.len() {
        return None;
    }
    let exprs: Vec<String> = order
        .iter()
        .map(|l| g.leaves.get(*l).map(Leaf::element))
        .collect::<Option<_>>()?;

    let mut items = String::new();
    items.push_str(&g.uses.helpers());
    for def in g.defs.values() {
        items.push_str(def);
        items.push('\n');
    }
    let _ = write!(
        items,
        "/// This circuit's public inputs, by name: what a proof proves, and what your\n\
         /// program requires (from its own state: a policy, a root, a signer).\n\
         #[derive(Clone, Copy, Debug, PartialEq, Eq)]\n\
         pub struct PublicInputs {{\n{fields}}}\n\n\
         impl PublicInputs {{\n    \
         /// The field elements the proof is over, in proof order, each 32 bytes\n    \
         /// little-endian, packed as the circuit's `#[input]` packs them.\n    \
         pub const fn to_fields(&self) -> Fields {{\n        \
         [\n"
    );
    for e in exprs {
        let _ = writeln!(items, "            {e},");
    }
    items.push_str(
        "        ]\n    }\n}\n\n\
         impl From<PublicInputs> for Fields {\n    \
         fn from(inputs: PublicInputs) -> Fields {\n        \
         inputs.to_fields()\n    }\n}\n\n\
         impl From<&PublicInputs> for Fields {\n    \
         fn from(inputs: &PublicInputs) -> Fields {\n        \
         inputs.to_fields()\n    }\n}\n",
    );
    // A sample that can't be written out typed only loses the self-test.
    let sample = sample.and_then(|values| {
        let decoded = xark_schema::Schema::parse(&schema.to_string())
            .ok()?
            .decode_public(values, false)
            .ok()?;
        let mut lit = String::from("PublicInputs {\n");
        for input in &public {
            let name = input["name"].as_str()?;
            let v = g.literal(&input["type"], &decoded[name])?;
            let _ = writeln!(lit, "            {}: {v},", ident(name));
        }
        lit.push_str("        }");
        Some(lit)
    });
    Some(Typed { items, sample })
}

struct Gen<'a> {
    schema: &'a Value,
    /// The input types' definitions, by Rust name.
    defs: BTreeMap<String, String>,
    /// Each leaf the codec names, and how to make it.
    leaves: BTreeMap<String, Leaf>,
    uses: Uses,
}

/// How one leaf is made: a value of so many bits (packable), or an element as is.
enum Leaf {
    /// A `u128` expression.
    Uint(String),
    /// An `i128` expression, of this many bits.
    Int(String, u64),
    /// An expression for the element's 32 bytes.
    Element(String),
}

impl Leaf {
    /// The leaf as an element of its own.
    fn element(&self) -> String {
        match self {
            Leaf::Uint(e) => format!("fields::uint({e})"),
            Leaf::Int(e, w) => format!("fields::int::<{w}>({e})"),
            Leaf::Element(e) => e.clone(),
        }
    }

    /// The leaf as the next `bits` of a `Packer`.
    fn pack(&self, bits: u64) -> String {
        match self {
            Leaf::Uint(e) => format!(".uint::<{bits}>({e})"),
            Leaf::Int(e, _) => format!(".int::<{bits}>({e})"),
            Leaf::Element(e) => format!(".bits::<{bits}>(&{e})"),
        }
    }
}

/// The helper types the definitions use.
#[derive(Default)]
struct Uses {
    time: bool,
    text: bool,
    set: bool,
}

/// Names the generated crate already uses, which an input type can't take.
const RESERVED: &[&str] = &[
    "Proof",
    "PublicInputs",
    "Verifier",
    "VerifierError",
    "Time",
    "Days",
    "Text",
    "Bitfield",
    "Variant",
    // Names the generated code uses from Rust's prelude.
    "Option",
    "Some",
    "None",
    "From",
    "Clone",
    "Copy",
    "Debug",
    "PartialEq",
    "Eq",
    "Fields",
    "Packer",
    "fields",
];

impl Gen<'_> {
    fn def(&self, r: &str) -> &Value {
        &self.schema["types"][r]
    }

    /// The Rust type a value of `ty` takes, its definition recorded.
    fn rust_ty(&mut self, ty: &Value) -> Option<String> {
        if ty == "field" {
            return Some("[u8; 32]".into());
        }
        if ty == "bool" {
            return Some("bool".into());
        }
        if let Some(w) = ty["uint"].as_u64() {
            return match w {
                8 | 16 | 32 | 64 | 128 => Some(format!("u{w}")),
                1..=127 => Some(format!("fields::Uint<{w}>")),
                _ => None,
            };
        }
        if let Some(w) = ty["int"].as_u64() {
            return [8, 16, 32, 64, 128].contains(&w).then(|| format!("i{w}"));
        }
        if let Some(a) = ty.get("array") {
            return Some(format!(
                "[{}; {}]",
                self.rust_ty(&a["of"])?,
                a["len"].as_u64()?
            ));
        }
        if let Some(t) = ty["tuple"].as_array() {
            let items: Vec<String> = t.iter().map(|e| self.rust_ty(e)).collect::<Option<_>>()?;
            return Some(format!("({},)", items.join(", ")));
        }
        let r = ty["ref"].as_str()?;
        let def = self.def(r).clone();
        let enc = &def["encoding"];
        if enc.get("timestamp").is_some() {
            return Some("i64".into());
        }
        if let Some(t) = enc.get("time") {
            self.uses.time = true;
            let (unit, from, to) = (t["unit"].as_u64()?, t["from"].as_u64()?, t["to"].as_u64()?);
            return Some(if unit == 86_400 {
                format!("Days<{from}, {to}>")
            } else {
                format!("Time<{unit}, {from}, {to}>")
            });
        }
        if enc.get("text").is_some() {
            self.uses.text = true;
            return Some("Text".into());
        }
        if let Some(e) = enc["choice"].as_str() {
            self.enumeration(e)?;
            return Some(rust_name(e));
        }
        if let Some(e) = enc["set"].as_str() {
            if self.def(e)["enum"].as_array()?.len() > 253 {
                return None;
            }
            self.enumeration(e)?;
            self.set_of(e)?;
            self.uses.set = true;
            return Some(format!("Bitfield<{}>", rust_name(e)));
        }
        if enc.get("limbs").is_some() || enc["ed25519"] == true {
            return None;
        }
        if enc.is_object() {
            return Some(format!("[u8; {}]", self.byte_len(r)?));
        }
        if def.get("newtype").is_some() {
            return self.rust_ty(&def["newtype"]);
        }
        let name = rust_name(r);
        if RESERVED.contains(&name.as_str()) {
            return None;
        }
        if !self.defs.contains_key(&name) {
            // Recorded first, so a recursive reference ends.
            self.defs.insert(name.clone(), String::new());
            let fields = def["struct"].as_array()?;
            // A tuple struct's fields are named `0`, `1`, …: it stays one (`.0` and
            // `Pt { 0: … }` work on either).
            let tuple = !fields.is_empty()
                && fields.iter().all(|f| {
                    f["name"]
                        .as_str()
                        .is_some_and(|n| n.parse::<usize>().is_ok())
                });
            let mut body = format!(
                "/// `{r}`, as the circuit takes it.\n\
                 #[derive(Clone, Copy, Debug, PartialEq, Eq)]\npub struct {name}"
            );
            if tuple {
                let types: Vec<String> = fields
                    .iter()
                    .map(|f| self.rust_ty(&f["type"]).map(|t| format!("pub {t}")))
                    .collect::<Option<_>>()?;
                let _ = writeln!(body, "({});", types.join(", "));
            } else {
                body.push_str(" {\n");
                for f in fields {
                    let t = self.rust_ty(&f["type"])?;
                    let _ = writeln!(body, "    pub {}: {t},", ident(f["name"].as_str()?));
                }
                body.push_str("}\n");
            }
            self.defs.insert(name.clone(), body);
        }
        Some(name)
    }

    /// Record enum `e`: its variants, in order, as their positions.
    fn enumeration(&mut self, e: &str) -> Option<()> {
        let name = rust_name(e);
        if RESERVED.contains(&name.as_str()) {
            return None;
        }
        if self.defs.contains_key(&name) {
            return Some(());
        }
        let variants = self.def(e)["enum"].as_array()?;
        let repr = if variants.len() <= 256 { "u8" } else { "u16" };
        let mut body = format!(
            "/// `{e}`: a variant is its position, as the circuit counts it.\n\
             #[derive(Clone, Copy, Debug, PartialEq, Eq)]\n#[repr({repr})]\npub enum {name} {{\n"
        );
        for v in variants {
            let _ = writeln!(body, "    {},", ident(v.as_str()?));
        }
        body.push_str("}\n");
        self.defs.insert(name, body);
        Some(())
    }

    /// Record the methods of a set of enum `e`'s variants.
    fn set_of(&mut self, e: &str) -> Option<()> {
        let name = rust_name(e);
        let n = self.def(e)["enum"].as_array()?.len();
        let body = format!(
            "impl Bitfield<{name}> {{\n    \
             /// Every variant.\n    \
             pub const ALL: Self = Self::EMPTY.with_first({n});\n\n    \
             /// This set and `v`.\n    \
             pub const fn with(self, v: {name}) -> Self {{\n        \
             self.with_bit(v as usize)\n    }}\n\n    \
             /// Whether `v` is in the set.\n    \
             pub const fn contains(&self, v: {name}) -> bool {{\n        \
             self.has_bit(v as usize)\n    }}\n}}\n"
        );
        // Beside the enum (a key no Rust name can be).
        self.defs.insert(format!("{name} set"), body);
        Some(())
    }

    /// A byte-encoded type's length (`xark_schema`'s `encoded_len`).
    fn byte_len(&self, r: &str) -> Option<usize> {
        let def = self.def(r);
        if let Some(b) = def["encoding"]["bytes"].as_u64() {
            return Some(b as usize);
        }
        self.byte_sizes(r).map(|s| s.iter().sum())
    }

    /// Its fields' byte lengths (`xark_schema`'s `concat_sizes`).
    fn byte_sizes(&self, r: &str) -> Option<Vec<usize>> {
        let def = self.def(r);
        match &def["encoding"]["concat"] {
            Value::Array(xs) => xs.iter().map(|x| x.as_u64().map(|v| v as usize)).collect(),
            _ => def["struct"]
                .as_array()?
                .iter()
                .map(|f| self.byte_len(f["type"]["ref"].as_str()?))
                .collect(),
        }
    }

    /// Record the leaves of `access`, a value of `ty` at codec path `path`
    /// (`xark_schema`'s `encode`, then `pack`).
    fn leaves(&mut self, ty: &Value, path: &str, access: &str) -> Option<()> {
        let leaf = |g: &mut Self, l: Leaf| {
            g.leaves.insert(path.to_string(), l);
            Some(())
        };
        if ty == "field" {
            return leaf(self, Leaf::Element(access.to_string()));
        }
        if let Some(w) = ty["uint"].as_u64()
            && ![8, 16, 32, 64, 128].contains(&w)
        {
            return leaf(self, Leaf::Uint(format!("{access}.get()")));
        }
        if ty == "bool" || ty.get("uint").is_some() {
            return leaf(self, Leaf::Uint(format!("{access} as u128")));
        }
        if let Some(w) = ty["int"].as_u64() {
            return leaf(self, Leaf::Int(format!("{access} as i128"), w));
        }
        if let Some(a) = ty.get("array") {
            for i in 0..a["len"].as_u64()? {
                self.leaves(&a["of"], &format!("{path}[{i}]"), &format!("{access}[{i}]"))?;
            }
            return Some(());
        }
        if let Some(t) = ty["tuple"].as_array() {
            for (i, e) in t.iter().enumerate() {
                self.leaves(e, &format!("{path}.{i}"), &format!("{access}.{i}"))?;
            }
            return Some(());
        }
        let r = ty["ref"].as_str()?;
        let def = self.def(r).clone();
        let enc = &def["encoding"];
        if enc.get("timestamp").is_some() {
            return leaf(self, Leaf::Int(format!("{access} as i128"), 64));
        }
        if enc.get("time").is_some() {
            return leaf(self, Leaf::Uint(format!("{access}.steps() as u128")));
        }
        if enc.get("text").is_some() || enc.get("set").is_some() {
            return leaf(self, Leaf::Element(format!("{access}.to_field()")));
        }
        if enc.get("choice").is_some() {
            return leaf(self, Leaf::Uint(format!("{access} as u128")));
        }
        if enc.is_object() {
            return self.byte_leaves(r, path, access, 0);
        }
        if def.get("newtype").is_some() {
            return self.leaves(&def["newtype"], path, access);
        }
        for g in groups(&def) {
            match g {
                Group::Alone(f) => {
                    let n = f["name"].as_str()?;
                    self.leaves(
                        &f["type"],
                        &format!("{path}.{n}"),
                        &format!("{access}.{}", ident(n)),
                    )?;
                }
                Group::Packed(fs) => {
                    let mut packer = String::from("Packer::new()");
                    let mut names = Vec::new();
                    let mut next = 0;
                    for f in &fs {
                        let n = f["name"].as_str()?;
                        let at = format!("{path}.{n}");
                        self.leaves(&f["type"], &at, &format!("{access}.{}", ident(n)))?;
                        // A packed field is one leaf, folded into the packed one. A
                        // `Packer` packs each run from bit 0, field after field.
                        let l = self.leaves.remove(&at)?;
                        let (offset, bits) = (
                            f["packed"]["offset"].as_u64()?,
                            f["packed"]["bits"].as_u64()?,
                        );
                        if offset != next {
                            return None;
                        }
                        next += bits;
                        packer.push_str(&l.pack(bits));
                        names.push(n);
                    }
                    packer.push_str(".finish()");
                    self.leaves.insert(
                        format!("{path}.{{{}}}", names.join(",")),
                        Leaf::Element(packer),
                    );
                }
            }
        }
        Some(())
    }

    /// The leaves of a byte-encoded `r` at byte `offset` of `access`: each field's
    /// chunk, read big-endian (`xark_schema`'s `encode_bytes`).
    fn byte_leaves(&mut self, r: &str, path: &str, access: &str, offset: usize) -> Option<()> {
        let def = self.def(r).clone();
        let sizes = self.byte_sizes(r)?;
        let mut off = offset;
        for (f, size) in def["struct"].as_array()?.iter().zip(sizes) {
            let at = format!("{path}.{}", f["name"].as_str()?);
            match f["type"]["ref"].as_str() {
                Some(fr) => self.byte_leaves(fr, &at, access, off)?,
                None => {
                    self.leaves.insert(
                        at,
                        Leaf::Element(format!("fields::be(&{access}, {off}, {size})")),
                    );
                }
            }
            off += size;
        }
        Some(())
    }

    /// `v`, a decoded value of `ty` (`decode_public`'s natural form), as a Rust
    /// expression.
    fn literal(&mut self, ty: &Value, v: &Value) -> Option<String> {
        if ty == "field" {
            return Some(bytes32(&v.as_str()?.parse::<BigUint>().ok()?));
        }
        if ty == "bool" {
            return Some(v.as_bool()?.to_string());
        }
        if let Some(w) = ty["uint"].as_u64()
            && ![8, 16, 32, 64, 128].contains(&w)
        {
            let n = match v {
                Value::String(s) => s.clone(),
                _ => v.to_string(),
            };
            return Some(format!("fields::Uint::<{w}>::new({n}).unwrap()"));
        }
        if ty.get("uint").is_some() || ty.get("int").is_some() {
            return Some(match v {
                Value::String(s) => s.clone(),
                _ => v.to_string(),
            });
        }
        if let Some(a) = ty.get("array") {
            if a["of"]["uint"] == 8 {
                return Some(byte_list(&hex(v.as_str()?)?));
            }
            let items: Vec<String> = v
                .as_array()?
                .iter()
                .map(|x| self.literal(&a["of"], x))
                .collect::<Option<_>>()?;
            return Some(format!("[{}]", items.join(", ")));
        }
        if let Some(t) = ty["tuple"].as_array() {
            let items: Vec<String> = t
                .iter()
                .zip(v.as_array()?)
                .map(|(e, x)| self.literal(e, x))
                .collect::<Option<_>>()?;
            return Some(format!("({},)", items.join(", ")));
        }
        let r = ty["ref"].as_str()?;
        let def = self.def(r).clone();
        let enc = &def["encoding"];
        if enc.get("timestamp").is_some() {
            return Some(xark_schema::time::parse(v.as_str()?).ok()?.to_string());
        }
        if let Some(t) = enc.get("time") {
            let secs = xark_schema::time::parse(v.as_str()?).ok()?;
            let start = xark_schema::time::days_from_civil(t["from"].as_i64()?, 1, 1)
                * xark_schema::time::DAY;
            let steps = (secs - start) / t["unit"].as_i64()?;
            return Some(format!(
                "<{}>::from_steps({steps}).unwrap()",
                self.rust_ty(ty)?
            ));
        }
        if enc.get("text").is_some() {
            return Some(format!("Text::new({:?}).unwrap()", v.as_str()?));
        }
        if let Some(e) = enc["choice"].as_str() {
            return Some(format!("{}::{}", rust_name(e), ident(v.as_str()?)));
        }
        if let Some(e) = enc["set"].as_str() {
            let e = rust_name(e);
            let mut s = format!("Bitfield::<{e}>::EMPTY");
            for x in v.as_array()? {
                let _ = write!(s, ".with({e}::{})", ident(x.as_str()?));
            }
            return Some(s);
        }
        if enc.is_object() {
            return Some(byte_list(&hex(v.as_str()?)?));
        }
        if def.get("newtype").is_some() {
            return self.literal(&def["newtype"], v);
        }
        let mut s = format!("{} {{ ", rust_name(r));
        for f in def["struct"].as_array()? {
            let n = f["name"].as_str()?;
            let _ = write!(s, "{}: {}, ", ident(n), self.literal(&f["type"], &v[n])?);
        }
        s.push('}');
        Some(s)
    }
}

impl Uses {
    /// The helpers every typed crate has (`enc`), and the input types it uses.
    fn helpers(&self) -> String {
        let mut out = String::from(
            "/// How the public inputs become field elements, as the circuit's `#[input]`\n\
             /// makes them; also for packing your own.\n\
             #[allow(unused_imports)]\n\
             pub use xark_verifier::fields::{self, Packer};\n\n",
        );
        if self.time {
            out.push_str(TIME);
        }
        if self.text {
            out.push_str(TEXT);
        }
        if self.set {
            out.push_str(SET);
        }
        out
    }
}

enum Group<'a> {
    Alone(&'a Value),
    Packed(Vec<&'a Value>),
}

/// A struct's fields, grouped by the element each shares (`xark_schema`'s `groups`:
/// a run of `"packed"` fields, each run starting at offset 0).
fn groups(def: &Value) -> Vec<Group<'_>> {
    let mut out: Vec<Group> = Vec::new();
    for f in def["struct"].as_array().into_iter().flatten() {
        match (f.get("packed"), out.last_mut()) {
            (Some(p), Some(Group::Packed(fs))) if p["offset"].as_u64() != Some(0) => fs.push(f),
            (Some(_), _) => out.push(Group::Packed(vec![f])),
            (None, _) => out.push(Group::Alone(f)),
        }
    }
    out
}

/// A Rust type name for schema type `r` (`Choice<Country>` has none: its variants'
/// enum is `Country`).
fn rust_name(r: &str) -> String {
    let mut out = String::new();
    let mut upper = false;
    for c in r.chars() {
        if c.is_ascii_alphanumeric() || c == '_' {
            out.push(if upper { c.to_ascii_uppercase() } else { c });
            upper = false;
        } else {
            upper = true;
        }
    }
    out
}

/// `name` as a Rust identifier (a keyword, raw).
fn ident(name: &str) -> String {
    const KEYWORDS: &[&str] = &[
        "as", "async", "await", "break", "const", "continue", "dyn", "else", "enum", "extern",
        "false", "fn", "for", "gen", "if", "impl", "in", "let", "loop", "match", "mod", "move",
        "mut", "pub", "ref", "return", "static", "struct", "trait", "true", "type", "unsafe",
        "use", "where", "while", "abstract", "become", "box", "do", "final", "macro", "override",
        "priv", "try", "typeof", "unsized", "virtual", "yield",
    ];
    if KEYWORDS.contains(&name) {
        format!("r#{name}")
    } else {
        name.to_string()
    }
}

fn hex(s: &str) -> Option<Vec<u8>> {
    let s = s.strip_prefix("0x")?;
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(s.get(i..i + 2)?, 16).ok())
        .collect()
}

fn byte_list(b: &[u8]) -> String {
    let items: Vec<String> = b.iter().map(|x| format!("{x:#04x}")).collect();
    format!("[{}]", items.join(", "))
}

/// A field element (decoded, so below the modulus), as its 32 little-endian bytes.
fn bytes32(n: &BigUint) -> String {
    let mut b = n.to_bytes_le();
    b.resize(32, 0);
    byte_list(&b)
}

const TIME: &str = r#"/// A moment in `UNIT`-second steps from the start of year `FROM` to the end of
/// `TO` (UTC), as the circuit's `xark::Time`: a program makes one from its `Clock`
/// with [`Time::from_unix`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Time<const UNIT: u32, const FROM: u16, const TO: u16>(u64);

/// A day from the start of year `FROM` to the end of year `TO`.
pub type Days<const FROM: u16, const TO: u16> = Time<86_400, FROM, TO>;

impl<const UNIT: u32, const FROM: u16, const TO: u16> Time<UNIT, FROM, TO> {
    /// The first moment, as Unix seconds: the start of `FROM`.
    pub const START: i64 = days_from_civil(FROM as i64) * 86_400;
    const END: i64 = days_from_civil(TO as i64 + 1) * 86_400;
    /// How many steps the range holds.
    pub const STEPS: u64 = ((Self::END - Self::START - 1) / UNIT as i64 + 1) as u64;

    /// The step holding Unix time `secs` (rounded down), or `None` outside the range.
    pub const fn from_unix(secs: i64) -> Option<Self> {
        if secs < Self::START || secs >= Self::END {
            return None;
        }
        Some(Time(((secs - Self::START) / UNIT as i64) as u64))
    }

    /// The `n`th step, or `None` past the last.
    pub const fn from_steps(n: u64) -> Option<Self> {
        if n < Self::STEPS { Some(Time(n)) } else { None }
    }

    /// Steps since the start of `FROM`: what the circuit holds.
    pub const fn steps(self) -> u64 {
        self.0
    }

    /// The moment this step starts, as Unix seconds.
    pub const fn to_unix(self) -> i64 {
        Self::START + self.0 as i64 * UNIT as i64
    }
}

/// Days from 1970-01-01 to January 1 of `year`.
const fn days_from_civil(year: i64) -> i64 {
    let y = year - 1;
    let era = y.div_euclid(400);
    let yoe = y - era * 400;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + 306;
    era * 146_097 + doe - 719_468
}

"#;

const TEXT: &str = r#"/// A string of at most 31 UTF-8 bytes, as the circuit's `xark::Text`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Text([u8; 32]);

impl Text {
    /// `s`, or `None` past 31 bytes.
    pub const fn new(s: &str) -> Option<Text> {
        let b = s.as_bytes();
        if b.len() > 31 {
            return None;
        }
        let mut out = [0u8; 32];
        let mut i = 0;
        while i < b.len() {
            out[i] = b[i];
            i += 1;
        }
        Some(Text(out))
    }

    /// Its field element: the bytes, little-endian.
    pub const fn to_field(&self) -> [u8; 32] {
        self.0
    }
}

"#;

const SET: &str = r#"/// A set of an enum's variants, as the circuit's `xark::Bitfield`: bit `i` for the
/// variant at position `i`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bitfield<E>([u8; 32], core::marker::PhantomData<E>);

impl<E> Bitfield<E> {
    /// No variants.
    pub const EMPTY: Self = Bitfield([0; 32], core::marker::PhantomData);

    const fn with_bit(mut self, i: usize) -> Self {
        self.0[i / 8] |= 1 << (i % 8);
        self
    }

    const fn has_bit(&self, i: usize) -> bool {
        self.0[i / 8] >> (i % 8) & 1 == 1
    }

    const fn with_first(mut self, n: usize) -> Self {
        let mut i = 0;
        while i < n {
            self = self.with_bit(i);
            i += 1;
        }
        self
    }

    /// Its field element.
    pub const fn to_field(&self) -> [u8; 32] {
        self.0
    }
}

"#;

#[cfg(test)]
mod tests {
    use serde_json::json;

    /// A public input with no `no_std` form here (a limbed number) gives no typed
    /// inputs, so the crate keeps the field elements by position.
    #[test]
    fn an_input_without_a_rust_form_falls_back() {
        let schema = json!({
            "version": 2,
            "circuit": "c",
            "inputs": [{ "name": "n", "type": { "ref": "U256" }, "visibility": "public" }],
            "public_inputs": ["n.0", "n.1", "n.2"],
            "types": { "U256": { "encoding": { "limbs": 86 }, "struct": [] } },
        });
        assert!(super::generate(&schema, 3, None).is_none());
    }

    /// A schema whose public inputs aren't the key's count isn't trusted.
    #[test]
    fn a_count_mismatch_falls_back() {
        let schema = json!({
            "version": 2,
            "circuit": "c",
            "inputs": [{ "name": "y", "type": "field", "visibility": "public" }],
            "public_inputs": ["y"],
            "types": {},
        });
        assert!(super::generate(&schema, 1, None).is_some());
        assert!(super::generate(&schema, 2, None).is_none());
    }
}
