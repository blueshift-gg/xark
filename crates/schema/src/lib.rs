//! A circuit's inputs as `schema.json` describes them, and the one place their
//! values are encoded: the CLI's `--inputs`, `xark-wasm` (so generated TypeScript
//! clients), and the input templates all go through [`Schema`].
//!
//! `xark build` writes `schema.json` from the `#[circuit]` fn's parameter types:
//!
//! ```text
//! {"version": 2,
//!  "inputs": [{"name": "born_before", "visibility": "public", "type": {"ref": "Days<1900,2100>"}}, …],
//!  "types": {"Days<1900,2100>": {"newtype": {"uint": 17},
//!                                 "encoding": {"time": {"unit": 86400, "from": 1900, "to": 2100}}},
//!            "Country": {"enum": ["AD", "AE", …]}, …},
//!  "public_inputs": ["commitment", "born_before", …]}
//! ```
//!
//! `xark::input::schema_json` writes it from each parameter's `Input::TYPE`. A type
//! is `"field"`, `{"uint": N}`, `{"int": N}` (two's complement), `"bool"`, `{"array": {"of", "len"}}`, `{"tuple": […]}` or
//! `{"ref": "<Name>"}`: a struct (`{"struct": [{"name", "type"}, …]}`) or a newtype
//! (`{"newtype": <type>}`). An enum (`{"enum": [names]}`) is never an input itself,
//! only what a `choice` or `set` names. A named type may carry an `encoding`, the
//! standard type a value is given as:
//!
//! | encoding                         | value                                           |
//! |----------------------------------|-------------------------------------------------|
//! | `{"timestamp": "unix"}`          | `"YYYY-MM-DD"`, an ISO 8601 date-time with a zone, or Unix seconds; the leaf is the seconds (`int` 64) |
//! | `{"time": {"unit", "from", "to"}}` | the same, from the start of year `from` to the end of `to`; the leaf is the `unit`-second steps since the start, rounded down |
//! | `{"text": 31}`                   | a string, at most 31 UTF-8 bytes                |
//! | `{"choice": E}`                  | a variant name of enum `E`, or its position     |
//! | `{"set": E}`                     | a variant name, a list of them, or the raw mask |
//! | `{"bytes": K, "limbs": B}`       | a number, or a list of its little-endian bytes, split into `B`-bit limbs |
//! | `{"concat": [k…] \| "fields"}`   | `0x`-hex bytes, the fields' encodings back to back (`"sec1": true`: a leading `0x04` too) |
//! | `{"bytes": 32, "ed25519": true}` | a compressed Ed25519 point                      |
//!
//! Without an encoding a struct is an object of its fields. Field names may be
//! `snake_case` (as declared) or `camelCase` (as in a generated client).

pub mod time;

use std::collections::BTreeMap;

use ark_bn254::Fr;
use ark_ff::{BigInteger, PrimeField};
use num_bigint::{BigInt, BigUint, Sign};
use serde_json::{Map, Value, json};

/// A circuit's input description (`schema.json`).
pub struct Schema(Value);

/// One declared input: its name, visibility, Rust type, and a `--inputs` template value.
pub struct InputSummary {
    pub name: String,
    pub public: bool,
    /// The type as written in Rust (`Date`, `[u8; 13]`, `Bitfield<Country>`).
    pub ty: String,
    /// A placeholder value in its natural form, as JSON text.
    pub template: String,
}

type Leaves = BTreeMap<String, Fr>;

/// An input value the schema refuses: where (`id.document`; empty for the inputs as
/// a whole, such as an unknown or missing input) and why.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputError {
    pub path: String,
    pub message: String,
}

impl std::fmt::Display for InputError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.path.is_empty() {
            f.write_str(&self.message)
        } else {
            write!(f, "input `{}`: {}", self.path, self.message)
        }
    }
}

impl std::error::Error for InputError {}

impl InputError {
    /// The same error with a generated client's field names (`id.netWorth`), for a
    /// caller who wrote the value in camelCase.
    pub fn camel_case(&self) -> InputError {
        InputError {
            path: camel_path(&self.path),
            message: self.message.clone(),
        }
    }
}

/// An input path with each name in camelCase (`id.net_worth[2]` → `id.netWorth[2]`).
pub fn camel_path(path: &str) -> String {
    path.split('.')
        .map(|seg| {
            let (name, index) = seg.split_at(seg.find('[').unwrap_or(seg.len()));
            format!("{}{index}", camel(name))
        })
        .collect::<Vec<_>>()
        .join(".")
}

/// An error about the inputs as a whole.
impl From<String> for InputError {
    fn from(message: String) -> InputError {
        InputError {
            path: String::new(),
            message,
        }
    }
}

impl From<&str> for InputError {
    fn from(message: &str) -> InputError {
        message.to_string().into()
    }
}

impl Schema {
    pub fn parse(text: &str) -> Result<Schema, String> {
        let v: Value = serde_json::from_str(text).map_err(|e| format!("schema.json: {e}"))?;
        if v["version"].as_u64() != Some(2) {
            return Err(format!(
                "unsupported schema version {} (rebuild the circuit with this xark)",
                v["version"]
            ));
        }
        Ok(Schema(v))
    }

    fn inputs(&self) -> impl Iterator<Item = &Value> {
        self.0["inputs"].as_array().into_iter().flatten()
    }

    fn def(&self, name: &str) -> &Value {
        &self.0["types"][name]
    }

    /// The enum a `choice`/`set` encoding names, and its variant names.
    fn variants(&self, enc: &Value) -> Option<(String, Vec<String>)> {
        let e = enc["choice"].as_str().or_else(|| enc["set"].as_str())?;
        let names = self.def(e)["enum"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(|n| n.as_str().map(str::to_string))
            .collect();
        Some((e.to_string(), names))
    }

    /// `inputs` (a JSON object of the circuit's inputs, nested values in their
    /// natural forms) as every input leaf's value. A key may also be a leaf or a
    /// nested path (`msg[0]`, `id.born`), so flat inputs still work. Every leaf must be
    /// given exactly once.
    pub fn leaves(&self, inputs: &Value) -> Result<Leaves, InputError> {
        self.leaves_where(inputs, |_| true)
    }

    /// The public inputs' values, in proof order, from `inputs` (only the public ones
    /// need be given).
    pub fn public_inputs(&self, inputs: &Value) -> Result<Vec<Fr>, InputError> {
        let leaves = self.leaves_where(inputs, |i| i["visibility"] == "public")?;
        self.0["public_inputs"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|l| {
                let l = l.as_str().unwrap_or_default();
                leaves
                    .get(l)
                    .copied()
                    .ok_or_else(|| format!("missing public input `{l}`").into())
            })
            .collect()
    }

    fn leaves_where(
        &self,
        inputs: &Value,
        keep: impl Fn(&Value) -> bool,
    ) -> Result<Leaves, InputError> {
        let obj = inputs.as_object().ok_or("inputs must be a JSON object")?;
        let wanted: Vec<&Value> = self.inputs().filter(|i| keep(i)).collect();
        let mut out = Leaves::new();
        // Top-level inputs (by declared or camelCase name), then any path keys.
        let mut used = vec![false; obj.len()];
        let keys: Vec<(&String, &Value)> = obj.iter().collect();
        for input in &wanted {
            let name = input["name"].as_str().unwrap_or_default();
            if let Some(i) = keys
                .iter()
                .position(|(k, _)| *k == name || **k == camel(name))
            {
                used[i] = true;
                self.encode(&input["type"], keys[i].1, name, &mut out)?;
            }
        }
        for (i, (k, v)) in keys.iter().enumerate() {
            if used[i] {
                continue;
            }
            let ty = self
                .type_at(k)
                .ok_or_else(|| format!("unknown input `{k}`; expected {}", self.names(&wanted)))?;
            self.encode(&ty, v, k, &mut out)?;
        }
        // Every leaf of every wanted input, given.
        for input in &wanted {
            let name = input["name"].as_str().unwrap_or_default();
            let mut all = Vec::new();
            self.leaf_names(&input["type"], name, &mut all);
            if let Some(l) = all.iter().find(|l| !out.contains_key(*l)) {
                return Err(if *l == name {
                    format!("missing input `{name}`")
                } else {
                    format!("missing input `{name}` (no value for `{l}`)")
                }
                .into());
            }
        }
        Ok(out)
    }

    fn names(&self, inputs: &[&Value]) -> String {
        let n: Vec<&str> = inputs.iter().filter_map(|i| i["name"].as_str()).collect();
        format!("{n:?}")
    }

    /// The type at input path `path` (`id`, `id.born`, `msg[3]`).
    fn type_at(&self, path: &str) -> Option<Value> {
        let root = path.split(['.', '[']).next()?;
        let mut ty = self.inputs().find(|i| i["name"] == root)?["type"].clone();
        let rest = &path[root.len()..];
        let mut i = 0;
        while i < rest.len() {
            if rest[i..].starts_with('.') {
                let end = rest[i + 1..]
                    .find(['.', '['])
                    .map_or(rest.len(), |e| i + 1 + e);
                let f = &rest[i + 1..end];
                let def = self.def(ty["ref"].as_str()?);
                ty = def["struct"].as_array()?.iter().find(|x| {
                    x["name"] == f || camel(x["name"].as_str().unwrap_or_default()) == f
                })?["type"]
                    .clone();
                i = end;
            } else if rest[i..].starts_with('[') {
                let end = rest[i..].find(']')? + i;
                ty = ty["array"]["of"].clone();
                i = end + 1;
            } else {
                return None;
            }
        }
        Some(ty)
    }

    /// The leaf names of a value of `ty` at `prefix`, in flatten order.
    fn leaf_names(&self, ty: &Value, prefix: &str, out: &mut Vec<String>) {
        if ty == "field" || ty == "bool" || ty.get("uint").is_some() || ty.get("int").is_some() {
            out.push(prefix.to_string());
        } else if let Some(a) = ty.get("array") {
            for i in 0..a["len"].as_u64().unwrap_or(0) {
                self.leaf_names(&a["of"], &format!("{prefix}[{i}]"), out);
            }
        } else if let Some(t) = ty["tuple"].as_array() {
            for (i, e) in t.iter().enumerate() {
                self.leaf_names(e, &format!("{prefix}.{i}"), out);
            }
        } else if let Some(r) = ty["ref"].as_str() {
            let def = self.def(r);
            if def.get("newtype").is_some() {
                out.push(prefix.to_string());
            }
            for f in def["struct"].as_array().into_iter().flatten() {
                let n = f["name"].as_str().unwrap_or_default();
                self.leaf_names(&f["type"], &format!("{prefix}.{n}"), out);
            }
        }
    }

    /// Encode `v`, a value of `ty`, into its leaves under `at`.
    fn encode(&self, ty: &Value, v: &Value, at: &str, out: &mut Leaves) -> Result<(), InputError> {
        let err = |message: String| InputError {
            path: at.to_string(),
            message,
        };
        if ty == "field" {
            out.insert(at.into(), field(v).map_err(err)?);
        } else if ty == "bool" {
            let b = match v {
                Value::Bool(b) => *b,
                Value::Number(n) if n.as_u64() == Some(0) => false,
                Value::Number(n) if n.as_u64() == Some(1) => true,
                _ => return Err(err(format!("expected true or false, got {v}"))),
            };
            out.insert(at.into(), Fr::from(b as u8));
        } else if let Some(w) = ty["uint"].as_u64() {
            let n = integer(v).map_err(err)?;
            if n.bits() > w {
                return Err(err(format!("{n} is out of range for a u{w}")));
            }
            out.insert(at.into(), Fr::from(n));
        } else if let Some(w) = ty["int"].as_u64() {
            out.insert(
                at.into(),
                Fr::from(twos_complement(&signed(v).map_err(err)?, w).map_err(err)?),
            );
        } else if let Some(a) = ty.get("array") {
            let len = a["len"].as_u64().unwrap_or(0) as usize;
            let items: Vec<Value> = if a["of"]["uint"] == 8 && v.is_string() {
                bytes(v)
                    .map_err(err)?
                    .into_iter()
                    .map(Value::from)
                    .collect()
            } else {
                v.as_array()
                    .cloned()
                    .ok_or_else(|| err("expected an array".into()))?
            };
            if items.len() != len {
                return Err(err(format!("expected {len} elements, got {}", items.len())));
            }
            for (i, x) in items.iter().enumerate() {
                self.encode(&a["of"], x, &format!("{at}[{i}]"), out)?;
            }
        } else if let Some(t) = ty["tuple"].as_array() {
            let items = v.as_array().filter(|xs| xs.len() == t.len());
            let items = items.ok_or_else(|| err(format!("expected a {}-tuple", t.len())))?;
            for (i, (e, x)) in t.iter().zip(items).enumerate() {
                self.encode(e, x, &format!("{at}.{i}"), out)?;
            }
        } else if let Some(r) = ty["ref"].as_str() {
            let def = self.def(r);
            if def.get("encoding").is_some() && !v.is_object() {
                return self.encode_natural(r, v, at, out).map_err(err);
            }
            if def.get("newtype").is_some() {
                return self.encode(&def["newtype"], v, at, out);
            }
            let obj = v
                .as_object()
                .ok_or_else(|| err(format!("expected a `{r}` (an object of its fields)")))?;
            for f in def["struct"].as_array().into_iter().flatten() {
                let n = f["name"].as_str().unwrap_or_default();
                let x = obj
                    .get(n)
                    .or_else(|| obj.get(&camel(n)))
                    .ok_or_else(|| err(format!("missing field `{n}`")))?;
                self.encode(&f["type"], x, &format!("{at}.{n}"), out)?;
            }
            if let Some(k) = obj.keys().find(|k| {
                !def["struct"].as_array().into_iter().flatten().any(|f| {
                    f["name"] == **k || camel(f["name"].as_str().unwrap_or_default()) == **k
                })
            }) {
                return Err(err(format!("`{r}` has no field `{k}`")));
            }
        }
        Ok(())
    }

    /// A value in named type `r`'s natural encoding.
    fn encode_natural(&self, r: &str, v: &Value, at: &str, out: &mut Leaves) -> Result<(), String> {
        let enc = &self.def(r)["encoding"];
        if enc.get("timestamp").is_some() {
            out.insert(
                at.into(),
                Fr::from(twos_complement(&BigInt::from(moment(v)?), 64)?),
            );
        } else if let Some(t) = time_range(enc) {
            out.insert(at.into(), Fr::from(t.steps(moment(v)?)?));
        } else if enc.get("text").is_some() {
            let s = v.as_str().ok_or("expected a string")?;
            if s.len() > 31 {
                return Err(format!("{s:?} is longer than 31 bytes"));
            }
            out.insert(at.into(), Fr::from_le_bytes_mod_order(s.as_bytes()));
        } else if let Some((e, names)) = self.variants(enc) {
            let n = if enc.get("set").is_some() {
                set(&e, &names, v)?
            } else {
                BigUint::from(choice(&e, &names, v)?)
            };
            out.insert(at.into(), Fr::from(n));
        } else if enc.get("limbs").is_some() {
            // A list of bytes is little-endian, as every integer's bytes are here
            // (`Field::from_le_bytes`, a client's `Uint8Array`); a hex string is a
            // number, written most significant digit first.
            let n = match v {
                Value::Array(_) => BigUint::from_bytes_le(&bytes(v)?),
                _ => integer(v)?,
            };
            self.encode_number(r, &n, at, out)?;
        } else {
            self.encode_bytes(r, &bytes(v)?, at, out)?;
        }
        Ok(())
    }

    fn encode_number(
        &self,
        r: &str,
        n: &BigUint,
        at: &str,
        out: &mut Leaves,
    ) -> Result<(), String> {
        let bits = self.def(r)["encoding"]["limbs"].as_u64().unwrap_or(0);
        let mut leaves = Vec::new();
        self.leaf_names(&json!({ "ref": r }), at, &mut leaves);
        if n.bits() > bits * leaves.len() as u64 {
            return Err(format!(
                "{n} doesn't fit a {r} ({} × {bits}-bit limbs)",
                leaves.len()
            ));
        }
        let mask = (BigUint::from(1u8) << bits) - 1u8;
        for (i, l) in leaves.into_iter().enumerate() {
            out.insert(l, Fr::from((n >> (i as u64 * bits)) & &mask));
        }
        Ok(())
    }

    /// Named type `r`'s encoded length in bytes.
    fn encoded_len(&self, r: &str) -> Option<usize> {
        let enc = &self.def(r)["encoding"];
        if let Some(b) = enc["bytes"].as_u64() {
            return Some(b as usize);
        }
        self.concat_sizes(r).map(|s| s.iter().sum())
    }

    fn concat_sizes(&self, r: &str) -> Option<Vec<usize>> {
        let def = self.def(r);
        match &def["encoding"]["concat"] {
            Value::Array(xs) => xs.iter().map(|x| x.as_u64().map(|v| v as usize)).collect(),
            _ => def["struct"]
                .as_array()?
                .iter()
                .map(|f| self.encoded_len(f["type"]["ref"].as_str()?))
                .collect(),
        }
    }

    fn encode_bytes(&self, r: &str, b: &[u8], at: &str, out: &mut Leaves) -> Result<(), String> {
        let def = self.def(r);
        let enc = &def["encoding"];
        let len = self
            .encoded_len(r)
            .ok_or_else(|| format!("`{r}` has no byte length"))?;
        let b = if enc["sec1"] == true && b.len() == len + 1 && b[0] == 4 {
            &b[1..]
        } else {
            b
        };
        if b.len() != len {
            return Err(format!("a {r} is {len} bytes, got {}", b.len()));
        }
        if enc.get("limbs").is_some() {
            return self.encode_number(r, &BigUint::from_bytes_be(b), at, out);
        }
        let (sizes, b) = if enc["ed25519"] == true {
            let (x, y) = ed25519::decompress(b)?;
            (vec![32, 32], [be32(&x), be32(&y)].concat())
        } else {
            (
                self.concat_sizes(r)
                    .ok_or_else(|| format!("`{r}` has no field lengths"))?,
                b.to_vec(),
            )
        };
        let mut off = 0;
        for (f, size) in def["struct"].as_array().into_iter().flatten().zip(sizes) {
            let chunk = &b[off..off + size];
            off += size;
            let leaf = format!("{at}.{}", f["name"].as_str().unwrap_or_default());
            match f["type"]["ref"].as_str() {
                Some(r) => self.encode_bytes(r, chunk, &leaf, out)?,
                None => {
                    out.insert(leaf, field(&Value::String(format!("0x{}", hex(chunk))))?);
                }
            }
        }
        Ok(())
    }

    /// A value of the named type `name` (a struct, `Date`, …), in its natural form, as
    /// its field elements in input order: what `to_fields()` gives in Rust, so a client
    /// can hash a value as the circuit does.
    pub fn fields(&self, name: &str, value: &Value) -> Result<Vec<Fr>, InputError> {
        if self.def(name).is_null() {
            return Err(format!("no type `{name}` in this circuit's inputs").into());
        }
        let ty = json!({ "ref": name });
        let mut leaves = Leaves::new();
        self.encode(&ty, value, "value", &mut leaves)?;
        let mut names = Vec::new();
        self.leaf_names(&ty, "value", &mut names);
        names
            .iter()
            .map(|n| {
                leaves
                    .get(n)
                    .copied()
                    .ok_or_else(|| format!("missing `{}`", &n[6..]).into())
            })
            .collect()
    }

    /// The public inputs `values` (in proof order), decoded into their natural forms:
    /// an object of the public inputs, keyed `camelCase` when `camel`.
    pub fn decode_public(&self, values: &[Fr], camel_keys: bool) -> Result<Value, String> {
        let mut it = values.iter().copied();
        let mut out = Map::new();
        for input in self.inputs().filter(|i| i["visibility"] == "public") {
            let name = input["name"].as_str().unwrap_or_default();
            let key = if camel_keys {
                camel(name)
            } else {
                name.to_string()
            };
            out.insert(key, self.decode(&input["type"], &mut it, camel_keys)?);
        }
        if it.next().is_some() {
            return Err("more public input values than the circuit has".into());
        }
        Ok(Value::Object(out))
    }

    fn decode(
        &self,
        ty: &Value,
        it: &mut impl Iterator<Item = Fr>,
        camel_keys: bool,
    ) -> Result<Value, String> {
        let mut next = || {
            it.next()
                .ok_or_else(|| "too few public input values".to_string())
        };
        if ty == "field" {
            return Ok(Value::String(next()?.into_bigint().to_string()));
        }
        if ty == "bool" {
            let b = next()?;
            if b > Fr::from(1u8) {
                return Err(format!("{b} is not a bool"));
            }
            return Ok(Value::Bool(b == Fr::from(1u8)));
        }
        if let Some(w) = ty["uint"].as_u64() {
            let n = BigUint::from(next()?.into_bigint());
            return Ok(if w <= 53 {
                json!(n.to_u64_digits().first().copied().unwrap_or(0))
            } else {
                json!(n.to_string())
            });
        }
        if let Some(w) = ty["int"].as_u64() {
            let n = from_twos_complement(&BigUint::from(next()?.into_bigint()), w)?;
            return Ok(match i64::try_from(&n) {
                Ok(i) if w <= 53 => json!(i),
                _ => json!(n.to_string()),
            });
        }
        if let Some(a) = ty.get("array") {
            let len = a["len"].as_u64().unwrap_or(0);
            if a["of"]["uint"] == 8 {
                let b: Vec<u8> = (0..len)
                    .map(|_| next().map(|x| x.into_bigint().0[0] as u8))
                    .collect::<Result<_, _>>()?;
                return Ok(Value::String(format!("0x{}", hex(&b))));
            }
            return (0..len)
                .map(|_| self.decode(&a["of"], it, camel_keys))
                .collect();
        }
        if let Some(t) = ty["tuple"].as_array() {
            return t.iter().map(|e| self.decode(e, it, camel_keys)).collect();
        }
        let r = ty["ref"].as_str().unwrap_or_default();
        let def = self.def(r);
        let enc = &def["encoding"];
        if enc.get("timestamp").is_some() {
            let n = from_twos_complement(&BigUint::from(next()?.into_bigint()), 64)?;
            let secs = i64::try_from(&n).map_err(|_| format!("{n} is not a timestamp"))?;
            return Ok(json!(time::format(secs, false)));
        }
        if let Some(t) = time_range(enc) {
            return Ok(json!(t.format(&BigUint::from(next()?.into_bigint()))?));
        }
        if enc.get("text").is_some() {
            let b = next()?.into_bigint().to_bytes_le();
            let n = b.iter().rposition(|&x| x != 0).map_or(0, |i| i + 1);
            return Ok(Value::String(String::from_utf8_lossy(&b[..n]).into_owned()));
        }
        if let Some((e, names)) = self.variants(enc) {
            let b = BigUint::from(next()?.into_bigint());
            if enc.get("choice").is_some() {
                // A circuit that doesn't check its choice can prove one past the enum.
                let i = usize::try_from(&b).ok().filter(|i| *i < names.len());
                return i
                    .map(|i| json!(names[i]))
                    .ok_or_else(|| format!("{b} is not a {e} (there are {})", names.len()));
            }
            return Ok(Value::Array(
                names
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| b.bit(*i as u64))
                    .map(|(_, n)| json!(n))
                    .collect(),
            ));
        }
        if def.get("newtype").is_some() {
            return self.decode(&def["newtype"], it, camel_keys);
        }
        if enc.get("limbs").is_some() {
            return Ok(Value::String(self.decode_number(r, it)?.to_string()));
        }
        if enc.is_object() {
            return Ok(Value::String(format!(
                "0x{}",
                hex(&self.decode_bytes(r, it)?)
            )));
        }
        let mut obj = Map::new();
        for f in def["struct"].as_array().into_iter().flatten() {
            let n = f["name"].as_str().unwrap_or_default();
            let key = if camel_keys { camel(n) } else { n.to_string() };
            obj.insert(key, self.decode(&f["type"], it, camel_keys)?);
        }
        Ok(Value::Object(obj))
    }

    /// A limbed value (named type `r`), recomposed from its leaves.
    fn decode_number(&self, r: &str, it: &mut impl Iterator<Item = Fr>) -> Result<BigUint, String> {
        let bits = self.def(r)["encoding"]["limbs"].as_u64().unwrap_or(0);
        let mut leaves = Vec::new();
        self.leaf_names(&json!({ "ref": r }), "", &mut leaves);
        let mut n = BigUint::from(0u8);
        for i in 0..leaves.len() {
            let limb = BigUint::from(
                it.next()
                    .ok_or("too few public input values")?
                    .into_bigint(),
            );
            n |= limb << (i as u64 * bits);
        }
        Ok(n)
    }

    /// A value of named type `r` in its byte encoding, from its leaves.
    fn decode_bytes(&self, r: &str, it: &mut impl Iterator<Item = Fr>) -> Result<Vec<u8>, String> {
        let def = self.def(r);
        let enc = &def["encoding"];
        let len = self
            .encoded_len(r)
            .ok_or_else(|| format!("`{r}` has no byte length"))?;
        let fixed = |n: &BigUint, size: usize| -> Result<Vec<u8>, String> {
            let b = n.to_bytes_be();
            if b.len() > size {
                return Err(format!("a `{r}` value doesn't fit {size} bytes"));
            }
            Ok([vec![0u8; size - b.len()], b].concat())
        };
        if enc.get("limbs").is_some() {
            return fixed(&self.decode_number(r, it)?, len);
        }
        let sizes = if enc["ed25519"] == true {
            vec![32, 32]
        } else {
            self.concat_sizes(r)
                .ok_or_else(|| format!("`{r}` has no field lengths"))?
        };
        let mut out = Vec::new();
        for (f, size) in def["struct"].as_array().into_iter().flatten().zip(sizes) {
            match f["type"]["ref"].as_str() {
                Some(fr) => out.extend(self.decode_bytes(fr, it)?),
                None => {
                    let v = BigUint::from(
                        it.next()
                            .ok_or("too few public input values")?
                            .into_bigint(),
                    );
                    out.extend(fixed(&v, size)?);
                }
            }
        }
        if enc["ed25519"] == true {
            // Compress: `y` little-endian, `x`'s parity in the top bit.
            let (x, y) = (&out[..32], &out[32..]);
            let mut c: Vec<u8> = y.iter().rev().copied().collect();
            c[31] |= (x[31] & 1) << 7;
            return Ok(c);
        }
        Ok(out)
    }

    /// The declared inputs, for summaries and `--inputs` templates.
    pub fn summary(&self) -> Vec<InputSummary> {
        self.inputs()
            .map(|i| InputSummary {
                name: i["name"].as_str().unwrap_or_default().to_string(),
                public: i["visibility"] == "public",
                ty: describe(&i["type"]),
                template: self.template(&i["type"]),
            })
            .collect()
    }

    /// A placeholder for a value of `ty` in its natural form, as JSON text.
    fn template(&self, ty: &Value) -> String {
        let q = |s: &str| format!("{s:?}");
        if ty == "field" {
            return q("<field>");
        }
        if ty == "bool" {
            return "false".into();
        }
        if let Some(w) = ty["uint"].as_u64() {
            return q(&format!("<u{w}>"));
        }
        if let Some(w) = ty["int"].as_u64() {
            return q(&format!("<i{w}>"));
        }
        let list = |xs: Vec<String>| format!("[{}]", xs.join(", "));
        if let Some(a) = ty.get("array") {
            let n = a["len"].as_u64().unwrap_or(0);
            if a["of"]["uint"] == 8 {
                return q(&format!("0x<{n} bytes>"));
            }
            return list((0..n).map(|_| self.template(&a["of"])).collect());
        }
        if let Some(t) = ty["tuple"].as_array() {
            return list(t.iter().map(|e| self.template(e)).collect());
        }
        let r = ty["ref"].as_str().unwrap_or_default();
        let def = self.def(r);
        let enc = &def["encoding"];
        if enc.get("timestamp").is_some() {
            return q("YYYY-MM-DDTHH:MM:SSZ");
        }
        if let Some(t) = time_range(enc) {
            return q(if t.unit % time::DAY == 0 {
                "YYYY-MM-DD"
            } else {
                "YYYY-MM-DDTHH:MM:SSZ"
            });
        }
        if enc.get("text").is_some() {
            return q("<text>");
        }
        if let Some((e, names)) = self.variants(enc) {
            let first = names.first().map_or("", |s| s.as_str());
            return q(&if enc.get("set").is_some() {
                format!("<{first} or a list of {e} names>")
            } else {
                format!("<a {e}: {first}, …>")
            });
        }
        if enc.get("limbs").is_some() {
            return q("<number>");
        }
        if enc.is_object() {
            let len = self
                .encoded_len(r)
                .map_or("bytes".into(), |b| format!("{b} bytes"));
            return q(&format!("0x<{len}>"));
        }
        if let Some(n) = def.get("newtype") {
            return self.template(n);
        }
        let fields: Vec<String> = def["struct"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|f| {
                format!(
                    "{:?}: {}",
                    f["name"].as_str().unwrap_or_default(),
                    self.template(&f["type"])
                )
            })
            .collect();
        format!("{{{}}}", fields.join(", "))
    }
}

/// A schema type as Rust spells it.
fn describe(ty: &Value) -> String {
    if ty == "field" {
        return "Field".into();
    }
    if ty == "bool" {
        return "bool".into();
    }
    if let Some(w) = ty["uint"].as_u64() {
        return format!("u{w}");
    }
    if let Some(w) = ty["int"].as_u64() {
        return format!("i{w}");
    }
    if let Some(a) = ty.get("array") {
        return format!("[{}; {}]", describe(&a["of"]), a["len"]);
    }
    if let Some(t) = ty["tuple"].as_array() {
        let parts: Vec<String> = t.iter().map(describe).collect();
        return format!("({})", parts.join(", "));
    }
    ty["ref"].as_str().unwrap_or("?").to_string()
}

/// `born_before` → `bornBefore`. Underscores before the first letter or after the
/// last stay as written (`_reserved`, `__proto__`); a run between words is one break.
pub fn camel(s: &str) -> String {
    let start = s.len() - s.trim_start_matches('_').len();
    let end = s.trim_end_matches('_').len().max(start);
    let mut out = String::from(&s[..start]);
    let mut up = false;
    for c in s[start..end].chars() {
        if c == '_' {
            up = true;
        } else if up {
            out.extend(c.to_uppercase());
            up = false;
        } else {
            out.push(c);
        }
    }
    out.push_str(&s[end..]);
    out
}

/// A non-negative integer: a JSON number, or a decimal / `0x`-hex string.
fn integer(v: &Value) -> Result<BigUint, String> {
    match v {
        // `1e3` parses as a float; take it if it is a whole, exactly representable number.
        Value::Number(n) => {
            if let Some(u) = n.as_u64() {
                return Ok(BigUint::from(u));
            }
            let f = n.as_f64().unwrap_or(f64::NAN);
            if f < 0.0 {
                Err(format!("{n} is negative"))
            } else if f.fract() != 0.0 {
                Err(format!("{n} is not a whole number"))
            } else if f < 9.0e15 {
                Ok(BigUint::from(f as u64))
            } else {
                // Past 2^64 serde_json keeps only a float: the digits are already gone.
                Err(format!(
                    "{n} is too large to write as a JSON number exactly: put it in quotes \
                     (\"123…\", or \"0x…\")"
                ))
            }
        }
        // Decimal digits, or `0x`/`0X` and hex digits; nothing else (no `+`, no `_`):
        // the client's `Field` reads the same.
        Value::String(s) => {
            let t = s.trim();
            let (digits, radix) = match t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
                Some(h) => (h, 16),
                None => (t, 10),
            };
            Some(digits)
                .filter(|d| !d.is_empty() && d.chars().all(|c| c.is_digit(radix)))
                .and_then(|d| BigUint::parse_bytes(d.as_bytes(), radix))
                .ok_or_else(|| format!("{s:?} is not a decimal or 0x-hex number"))
        }
        other => Err(format!("expected a number, got {other}")),
    }
}

/// An integer of either sign: a JSON number, or a decimal / `0x`-hex string with an
/// optional leading `-`.
fn signed(v: &Value) -> Result<BigInt, String> {
    match v {
        Value::Number(n) if n.as_i64().is_some() => Ok(BigInt::from(n.as_i64().unwrap_or(0))),
        Value::Number(n) if n.as_f64().is_some_and(|f| f < 0.0) => {
            let f = n.as_f64().unwrap_or(f64::NAN);
            if f.fract() != 0.0 {
                Err(format!("{n} is not a whole number"))
            } else if f > -9.0e15 {
                Ok(BigInt::from(f as i64))
            } else {
                Err(format!(
                    "{n} is too large to write as a JSON number exactly: put it in quotes"
                ))
            }
        }
        Value::String(s) if s.trim().starts_with('-') => {
            let rest = Value::String(s.trim()[1..].to_string());
            let n =
                integer(&rest).map_err(|_| format!("{s:?} is not a decimal or 0x-hex number"))?;
            Ok(-BigInt::from(n))
        }
        _ => integer(v).map(BigInt::from),
    }
}

/// `n` as a `w`-bit two's complement word (`-1` as `2^w - 1`), or why it doesn't fit.
fn twos_complement(n: &BigInt, w: u64) -> Result<BigUint, String> {
    let half = BigInt::from(1u8) << (w - 1);
    if *n < -&half || *n >= half {
        return Err(format!("{n} is out of range for an i{w}"));
    }
    let word = if n.sign() == Sign::Minus {
        n + (&half << 1)
    } else {
        n.clone()
    };
    Ok(word.to_biguint().unwrap_or_default())
}

/// A `w`-bit two's complement word as the integer it stands for.
fn from_twos_complement(word: &BigUint, w: u64) -> Result<BigInt, String> {
    if word.bits() > w {
        return Err(format!("{word} is out of range for an i{w}"));
    }
    let n = BigInt::from(word.clone());
    Ok(if word.bit(w - 1) {
        n - (BigInt::from(1u8) << w)
    } else {
        n
    })
}

/// A field element, `0 <= x < p` (never reduced: a value that wraps would prove
/// another number).
fn field(v: &Value) -> Result<Fr, String> {
    let n = integer(v)?;
    if n >= BigUint::from(Fr::MODULUS) {
        return Err(format!("{n} is not a field element (it is p or more)"));
    }
    Ok(Fr::from(n))
}

/// Bytes: `0x`-hex, or a list of byte values.
fn bytes(v: &Value) -> Result<Vec<u8>, String> {
    match v {
        Value::String(s) => {
            let h = s
                .trim()
                .strip_prefix("0x")
                .or_else(|| s.trim().strip_prefix("0X"))
                .ok_or_else(|| format!("expected 0x-hex bytes, got {s:?}"))?;
            if h.len() % 2 != 0 {
                return Err(format!("{s:?} has an odd number of hex digits"));
            }
            (0..h.len())
                .step_by(2)
                .map(|i| {
                    u8::from_str_radix(&h[i..i + 2], 16).map_err(|_| format!("invalid hex {s:?}"))
                })
                .collect()
        }
        Value::Array(xs) => xs
            .iter()
            .map(|x| {
                x.as_u64()
                    .filter(|b| *b < 256)
                    .map(|b| b as u8)
                    .ok_or_else(|| format!("{x} is not a byte"))
            })
            .collect(),
        other => Err(format!("expected bytes (0x-hex or a list), got {other}")),
    }
}

/// A moment as Unix seconds: `"YYYY-MM-DD"`, an ISO 8601 date-time with a zone, or
/// a number of seconds (a JSON number or a decimal string, `-` allowed).
fn moment(v: &Value) -> Result<i64, String> {
    if let Value::String(t) = v {
        let t = t.trim();
        if t.len() >= 10 && t.as_bytes()[4] == b'-' {
            return time::parse(t);
        }
    }
    let n = signed(v).map_err(|e| {
        format!("{e} (a time is \"YYYY-MM-DD\", an ISO 8601 date-time, or Unix seconds)")
    })?;
    i64::try_from(&n).map_err(|_| format!("{n} seconds is out of range for a timestamp"))
}

/// A `time` encoding's range: steps of `unit` seconds from the start of year `from`
/// to the end of year `to`.
struct TimeRange {
    unit: i64,
    from: i64,
    to: i64,
}

fn time_range(enc: &Value) -> Option<TimeRange> {
    let t = enc.get("time")?;
    Some(TimeRange {
        unit: t["unit"].as_i64().filter(|u| *u > 0)?,
        from: t["from"].as_i64()?,
        to: t["to"].as_i64()?,
    })
}

impl TimeRange {
    fn start(&self) -> i64 {
        time::days_from_civil(self.from, 1, 1) * time::DAY
    }

    /// The step holding `secs`, rounded down, or why it's outside the range.
    fn steps(&self, secs: i64) -> Result<u64, String> {
        let end = time::days_from_civil(self.to + 1, 1, 1) * time::DAY;
        if secs < self.start() || secs >= end {
            return Err(format!(
                "{} is outside {}-01-01 to {}-12-31",
                time::format(secs, self.unit % time::DAY == 0),
                self.from,
                self.to
            ));
        }
        Ok(((secs - self.start()) / self.unit) as u64)
    }

    /// A step, as the moment it starts.
    fn format(&self, steps: &BigUint) -> Result<String, String> {
        let secs = u64::try_from(steps)
            .ok()
            .and_then(|n| i64::try_from(n).ok())
            .and_then(|n| n.checked_mul(self.unit))
            .and_then(|n| n.checked_add(self.start()))
            .ok_or_else(|| format!("{steps} steps is past every time"))?;
        Ok(time::format(secs, self.unit % time::DAY == 0))
    }
}

/// A variant's position in enum `e`, from its name.
fn variant(e: &str, names: &[String], v: &Value) -> Result<usize, String> {
    let s = v
        .as_str()
        .ok_or_else(|| format!("expected a {e} name, got {v}"))?;
    names
        .iter()
        .position(|x| x == s)
        .ok_or_else(|| format!("{s:?} is not a {e}"))
}

/// One variant: its name, or its position (a number).
fn choice(e: &str, names: &[String], v: &Value) -> Result<usize, String> {
    if v.is_string() {
        return variant(e, names, v);
    }
    let n = integer(v)?;
    usize::try_from(&n)
        .ok()
        .filter(|i| *i < names.len())
        .ok_or_else(|| format!("{n} is not a {e} (there are {})", names.len()))
}

/// A set of variants: a name, a list of names, or the raw mask (a number).
fn set(e: &str, names: &[String], v: &Value) -> Result<BigUint, String> {
    let bit = |x: &Value| variant(e, names, x).map(|i| BigUint::from(1u8) << i);
    match v {
        Value::Array(xs) => xs
            .iter()
            .try_fold(BigUint::from(0u8), |acc, x| Ok(acc | bit(x)?)),
        Value::String(_) => bit(v),
        _ => {
            let n = integer(v)?;
            if n.bits() > names.len() as u64 {
                return Err(format!("{n} sets a bit past the last {e}"));
            }
            Ok(n)
        }
    }
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn be32(v: &BigUint) -> Vec<u8> {
    let b = v.to_bytes_be();
    let mut out = vec![0u8; 32 - b.len()];
    out.extend(b);
    out
}

mod ed25519 {
    use num_bigint::BigUint;

    /// Decompress an Ed25519 point (`y` little-endian, `x`'s sign in the top bit) to
    /// affine `(x, y)`.
    pub fn decompress(comp: &[u8]) -> Result<(BigUint, BigUint), String> {
        let dec = |s: &str| BigUint::parse_bytes(s.as_bytes(), 10).expect("constant");
        let p = (BigUint::from(1u8) << 255u32) - 19u32;
        let d =
            dec("37095705934669439343138083508754565189542113879843219016388785533085940283555");
        let sqrt_m1 =
            dec("19681161376707505956807079304988542015446066515923890162744021073123829784752");
        let mut yb = comp.to_vec();
        let sign = (yb[31] >> 7) & 1;
        yb[31] &= 0x7f;
        let y = BigUint::from_bytes_le(&yb);
        if y >= p {
            return Err("not an Ed25519 point".into());
        }
        let y2 = (&y * &y) % &p;
        let u = (&y2 + &p - 1u32) % &p;
        let v = (&d * &y2 + 1u32) % &p;
        let pw = ((&u * v.modpow(&BigUint::from(7u32), &p)) % &p).modpow(&((&p - 5u32) / 8u32), &p);
        let mut x = (((&u * v.modpow(&BigUint::from(3u32), &p)) % &p) * pw) % &p;
        if (&v * (&x * &x % &p)) % &p != u {
            x = (x * sqrt_m1) % &p;
        }
        if (&v * (&x * &x % &p)) % &p != u {
            return Err("not an Ed25519 point".into());
        }
        if (x.bit(0) as u8) != sign {
            x = (&p - &x) % &p;
        }
        Ok((x, y))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn schema() -> Schema {
        Schema::parse(
            r#"{"version": 2,
              "inputs": [
                {"name": "id", "visibility": "private", "type": {"ref": "Identity"}},
                {"name": "born_before", "visibility": "public", "type": {"ref": "Timestamp"}},
                {"name": "allowed", "visibility": "public", "type": {"ref": "Bitfield<Country>"}},
                {"name": "home", "visibility": "public", "type": {"ref": "Choice<Country>"}},
                {"name": "k", "visibility": "private", "type": {"ref": "Fq"}},
                {"name": "h", "visibility": "public", "type": {"ref": "Hash"}},
                {"name": "msg", "visibility": "private", "type": {"array": {"of": {"uint": 8}, "len": 2}}},
                {"name": "ok", "visibility": "public", "type": "bool"}
              ],
              "types": {
                "Identity": {"struct": [
                    {"name": "document", "type": {"ref": "Text"}},
                    {"name": "born", "type": {"ref": "Days<1900,2100>"}},
                    {"name": "net_worth", "type": {"uint": 64}}]},
                "Days<1900,2100>": {"newtype": {"uint": 17},
                    "encoding": {"time": {"unit": 86400, "from": 1900, "to": 2100}}},
                "Timestamp": {"newtype": {"int": 64}, "encoding": {"timestamp": "unix"}},
                "Text": {"newtype": "field", "encoding": {"text": 31}},
                "Bitfield<Country>": {"newtype": "field", "encoding": {"set": "Country"}},
                "Choice<Country>": {"newtype": "field", "encoding": {"choice": "Country"}},
                "Country": {"enum": ["AD", "FR", "US"]},
                "Fq": {"struct": [{"name": "limbs", "type": {"array": {"of": "field", "len": 3}}}],
                       "encoding": {"bytes": 32, "limbs": 86}},
                "Hash": {"struct": [{"name": "hi", "type": "field"}, {"name": "lo", "type": "field"}],
                         "encoding": {"bytes": 32, "concat": [16, 16]}}
              },
              "public_inputs": ["born_before", "allowed", "home", "h.hi", "h.lo", "ok"]}"#,
        )
        .unwrap()
    }

    fn inputs() -> Value {
        json!({
            "id": {"document": "AB", "born": "1990-01-02", "netWorth": 7},
            "bornBefore": "2008-10-20",
            "allowed": ["US", "FR"],
            "home": "FR",
            "k": "77371252455336267181195264",
            "h": format!("0x{}{}", "00".repeat(15) + "02", "00".repeat(15) + "03"),
            "msg": "0x6162",
            "ok": true,
        })
    }

    #[test]
    fn natural_values_become_leaves() {
        let l = schema().leaves(&inputs()).unwrap();
        let d = |k: &str| l[k].into_bigint().to_string();
        assert_eq!(d("id.document"), (0x4241u32).to_string()); // "AB", little-endian
        let day = |y, m, d| time::days_from_civil(y, m, d);
        assert_eq!(
            d("id.born"),
            (day(1990, 1, 2) - day(1900, 1, 1)).to_string()
        );
        assert_eq!(d("id.net_worth"), "7");
        assert_eq!(
            d("born_before"),
            (day(2008, 10, 20) * time::DAY).to_string()
        );
        assert_eq!(d("allowed"), "6"); // FR (bit 1) | US (bit 2)
        assert_eq!(d("home"), "1");
        assert_eq!((d("k.limbs[0]"), d("k.limbs[1]")), ("0".into(), "1".into())); // 2^86
        assert_eq!((d("h.hi"), d("h.lo")), ("2".into(), "3".into()));
        assert_eq!((d("msg[0]"), d("msg[1]")), ("97".into(), "98".into()));
    }

    #[test]
    fn camel_keeps_outer_underscores() {
        for (snake, want) in [
            ("born_before", "bornBefore"),
            ("net_worth_2", "netWorth2"),
            ("a__b", "aB"),
            ("_reserved", "_reserved"),
            ("__proto__", "__proto__"),
            ("x_", "x_"),
            ("_", "_"),
            ("naïve_é", "naïveÉ"),
            ("ü_", "ü_"),
        ] {
            assert_eq!(camel(snake), want, "{snake}");
        }
    }

    #[test]
    fn json_numbers_say_what_is_wrong() {
        let n = |text: &str| integer(&serde_json::from_str(text).unwrap());
        assert_eq!(n("1e6").unwrap(), BigUint::from(1_000_000u32));
        assert_eq!(n("18446744073709551615").unwrap(), BigUint::from(u64::MAX));
        assert_eq!(n("-1").unwrap_err(), "-1 is negative");
        assert_eq!(n("1.5").unwrap_err(), "1.5 is not a whole number");
        // Past u64, the digits are gone before the codec sees them: ask for quotes.
        for big in ["18446744073709551616", "1e20"] {
            assert!(n(big).unwrap_err().contains("put it in quotes"), "{big}");
        }
        assert_eq!(
            n("\"18446744073709551616\"").unwrap(),
            BigUint::from(1u128 << 64)
        );
        // A string: decimal, or 0x/0X hex, spaces around it ignored; nothing else.
        for (s, v) in [("\" 27 \"", 27u32), ("\"0x1b\"", 27), ("\"0X1B\"", 27)] {
            assert_eq!(n(s).unwrap(), BigUint::from(v), "{s}");
        }
        for s in [
            "\"1_000\"",
            "\"+27\"",
            "\"0x\"",
            "\"\"",
            "\"0x1g\"",
            "\"-1\"",
        ] {
            assert!(
                n(s).unwrap_err()
                    .contains("is not a decimal or 0x-hex number"),
                "{s}"
            );
        }
    }

    #[test]
    fn times_are_steps_in_their_range() {
        let s = Schema::parse(
            r#"{"version": 2,
              "inputs": [
                {"name": "day", "visibility": "public", "type": {"ref": "Days<1900,2100>"}},
                {"name": "min", "visibility": "public", "type": {"ref": "Time<60,2020,2060>"}},
                {"name": "at", "visibility": "public", "type": {"ref": "Timestamp"}}],
              "types": {
                "Days<1900,2100>": {"newtype": {"uint": 17},
                    "encoding": {"time": {"unit": 86400, "from": 1900, "to": 2100}}},
                "Time<60,2020,2060>": {"newtype": {"uint": 25},
                    "encoding": {"time": {"unit": 60, "from": 2020, "to": 2060}}},
                "Timestamp": {"newtype": {"int": 64}, "encoding": {"timestamp": "unix"}}},
              "public_inputs": ["day", "min", "at"]}"#,
        )
        .unwrap();
        let leaves = |day: Value, min: Value, at: Value| {
            s.public_inputs(&json!({"day": day, "min": min, "at": at}))
        };
        let d = |v: Vec<Fr>| {
            v.iter()
                .map(|x| x.into_bigint().to_string())
                .collect::<Vec<_>>()
        };
        let days = |y, m, dd| time::days_from_civil(y, m, dd) - time::days_from_civil(1900, 1, 1);
        // A day, its noon, and its Unix seconds are all that day; a minute rounds down too.
        let noon = time::days_from_civil(1990, 1, 1) * time::DAY + 43_200;
        for day in [
            json!("1990-01-01"),
            json!("1990-01-01T12:00:00Z"),
            json!(noon),
        ] {
            let l = d(leaves(day.clone(), json!("2020-01-01T00:01:59Z"), json!(-1)).unwrap());
            assert_eq!(
                l,
                [
                    days(1990, 1, 1).to_string(),
                    "1".into(),
                    (u64::MAX).to_string()
                ],
                "{day}"
            );
        }
        // Leap days are days.
        let l = d(leaves(json!("2024-03-01"), json!("2020-01-01T00:00:00Z"), json!(0)).unwrap());
        assert_eq!(l[0], (days(2024, 2, 28) + 2).to_string());
        // The ends, and past them.
        assert_eq!(
            d(leaves(json!("1900-01-01"), json!(1577836800), json!(0)).unwrap())[0],
            "0"
        );
        for (day, min, why) in [
            (
                json!("1899-12-31"),
                json!(1577836800),
                "1899-12-31 is outside 1900-01-01 to 2100-12-31",
            ),
            (
                json!("2101-01-01"),
                json!(1577836800),
                "2101-01-01 is outside 1900-01-01 to 2100-12-31",
            ),
            (
                json!("1990-01-01"),
                json!("2019-12-31T23:59:59Z"),
                "2019-12-31T23:59:59Z is outside 2020-01-01 to 2060-12-31",
            ),
            (json!("1990-02-30"), json!(1577836800), "not a calendar day"),
            (
                json!("1990-01-01T00:00:00"),
                json!(1577836800),
                "no time zone",
            ),
            (json!(true), json!(1577836800), "Unix seconds"),
        ] {
            let e = leaves(day.clone(), min, json!(0)).unwrap_err();
            assert!(e.message.contains(why), "{day}: {e}");
        }
        // Back: a day as its date, a minute and a timestamp as date-times.
        let pubs = leaves(
            json!("2024-02-29"),
            json!("2030-06-01T08:30:45+02:00"),
            json!(-1),
        )
        .unwrap();
        assert_eq!(
            s.decode_public(&pubs, false).unwrap(),
            json!({"day": "2024-02-29", "min": "2030-06-01T06:30:00Z", "at": "1969-12-31T23:59:59Z"})
        );
    }

    #[test]
    fn signed_integers_are_twos_complement() {
        let s = Schema::parse(
            r#"{"version": 2,
              "inputs": [
                {"name": "a", "visibility": "public", "type": {"int": 8}},
                {"name": "t", "visibility": "public", "type": {"int": 64}}],
              "types": {}, "public_inputs": ["a", "t"]}"#,
        )
        .unwrap();
        let leaves = |a: Value, t: Value| s.public_inputs(&json!({"a": a, "t": t}));
        let d = |v: Vec<Fr>| {
            v.iter()
                .map(|x| x.into_bigint().to_string())
                .collect::<Vec<_>>()
        };
        assert_eq!(d(leaves(json!(-1), json!(5)).unwrap()), ["255", "5"]);
        assert_eq!(
            d(leaves(json!(-128), json!("-9223372036854775808")).unwrap()),
            ["128", (1u64 << 63).to_string().as_str()]
        );
        assert_eq!(
            d(leaves(json!(127), json!("9223372036854775807")).unwrap()),
            ["127", i64::MAX.to_string().as_str()]
        );
        // `-1` round trips; a 64-bit value comes back as a string.
        let pubs = leaves(json!(-1), json!(-86_400)).unwrap();
        assert_eq!(
            s.decode_public(&pubs, false).unwrap(),
            json!({"a": -1, "t": "-86400"})
        );
        for (a, t, why) in [
            (json!(128), json!(0), "128 is out of range for an i8"),
            (json!(-129), json!(0), "-129 is out of range for an i8"),
            (
                json!(0),
                json!("9223372036854775808"),
                "out of range for an i64",
            ),
            (
                json!(0),
                json!("-9223372036854775809"),
                "out of range for an i64",
            ),
            (json!(-1.5), json!(0), "-1.5 is not a whole number"),
            (json!("-x"), json!(0), "is not a decimal or 0x-hex number"),
        ] {
            let e = leaves(a.clone(), t).unwrap_err();
            assert!(e.message.contains(why), "{a}: {e}");
        }
        // A leaf past the width (a proof can't carry one, but a caller can pass one).
        assert!(
            s.decode_public(&[Fr::from(256u32), Fr::from(0u8)], false)
                .unwrap_err()
                .contains("out of range for an i8")
        );
    }

    #[test]
    fn a_number_as_bytes_is_little_endian() {
        // 2^86, as its little-endian bytes: byte 10 holds bit 86 (0x40).
        let mut le = vec![0u64; 32];
        le[10] = 0x40;
        let mut v = inputs();
        v["k"] = json!(le);
        let l = schema().leaves(&v).unwrap();
        let d = |k: &str| l[k].into_bigint().to_string();
        assert_eq!((d("k.limbs[0]"), d("k.limbs[1]")), ("0".into(), "1".into()));
        // A hex string is a number, most significant digit first.
        v["k"] = json!(format!("0x{:x}", 1u128 << 86));
        assert_eq!(
            schema().leaves(&v).unwrap()["k.limbs[1]"]
                .into_bigint()
                .to_string(),
            "1"
        );
    }

    #[test]
    fn public_inputs_round_trip_to_natural_forms() {
        let s = schema();
        let pubs = s.public_inputs(&inputs()).unwrap();
        let back = s.decode_public(&pubs, true).unwrap();
        assert_eq!(back["bornBefore"], "2008-10-20T00:00:00Z");
        assert_eq!(back["allowed"], json!(["FR", "US"]));
        assert_eq!(back["home"], "FR");
        assert_eq!(back["ok"], true);
        let mut bad = pubs.clone();
        bad[2] = Fr::from(3u8); // `home`, past the three countries
        assert!(
            s.decode_public(&bad, true)
                .unwrap_err()
                .contains("3 is not a Country")
        );
        assert_eq!(
            back["h"],
            json!(format!(
                "0x{}{}",
                "00".repeat(15) + "02",
                "00".repeat(15) + "03"
            ))
        );
    }

    #[test]
    fn values_as_fields() {
        let f = schema()
            .fields("Identity", &inputs()["id"])
            .unwrap()
            .iter()
            .map(|x| x.into_bigint().to_string())
            .collect::<Vec<_>>();
        let born = time::days_from_civil(1990, 1, 2) - time::days_from_civil(1900, 1, 1);
        assert_eq!(f, [(0x4241u32).to_string(), born.to_string(), "7".into()]);
        assert!(schema().fields("Nope", &json!({})).is_err());
    }

    #[test]
    fn mistakes_are_named() {
        let s = schema();
        let with = |k: &str, v: Value| {
            let mut i = inputs();
            i[k] = v;
            s.leaves(&i).unwrap_err()
        };
        // Each names the input at fault (empty: the inputs as a whole) and why.
        for (key, value, path, why) in [
            (
                "bornBefore",
                json!("2023-02-29"),
                "born_before",
                "not a calendar day",
            ),
            (
                "allowed",
                json!(["XX"]),
                "allowed",
                "\"XX\" is not a Country",
            ),
            ("home", json!("XX"), "home", "\"XX\" is not a Country"),
            ("home", json!(3), "home", "3 is not a Country (there are 3)"),
            ("msg", json!("0x61"), "msg", "expected 2 elements"),
            ("typo", json!(1), "", "unknown input `typo`"),
            ("ok", json!("yes"), "ok", "expected true or false"),
        ] {
            let e = with(key, value);
            assert_eq!(e.path, path, "{e}");
            assert!(e.message.contains(why), "{e}");
        }
        let mut i = inputs();
        i["id"].as_object_mut().unwrap().remove("born");
        let e = s.leaves(&i).unwrap_err();
        assert_eq!(
            (e.path.as_str(), e.message.as_str()),
            ("id", "missing field `born`")
        );
        assert_eq!(e.to_string(), "input `id`: missing field `born`");
    }

    #[test]
    fn templates_are_natural() {
        let t: Vec<String> = schema()
            .summary()
            .into_iter()
            .map(|i| format!("{}: {} = {}", i.name, i.ty, i.template))
            .collect();
        assert_eq!(
            t[0],
            r#"id: Identity = {"document": "<text>", "born": "YYYY-MM-DD", "net_worth": "<u64>"}"#
        );
        assert_eq!(
            t[2],
            r#"allowed: Bitfield<Country> = "<AD or a list of Country names>""#
        );
    }

    #[test]
    fn ed25519_points_round_trip() {
        let s = Schema::parse(
            r#"{"version": 2,
              "inputs": [{"name": "pk", "visibility": "public", "type": {"ref": "PointL"}}],
              "types": {
                "FpL": {"struct": [{"name": "limbs", "type": {"array": {"of": "field", "len": 3}}}],
                        "encoding": {"bytes": 32, "limbs": 85}},
                "PointL": {"struct": [{"name": "x", "type": {"ref": "FpL"}}, {"name": "y", "type": {"ref": "FpL"}}],
                           "encoding": {"bytes": 32, "ed25519": true}}
              },
              "public_inputs": ["pk.x.limbs[0]", "pk.x.limbs[1]", "pk.x.limbs[2]",
                                "pk.y.limbs[0]", "pk.y.limbs[1]", "pk.y.limbs[2]"]}"#,
        )
        .unwrap();
        // RFC 8032 test 1's public key.
        let pk = "0xd75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a";
        let values = s.public_inputs(&json!({ "pk": pk })).unwrap();
        assert_eq!(s.decode_public(&values, true).unwrap()["pk"], pk);
    }

    #[test]
    fn ed25519_base_point() {
        let mut comp = [0x66u8; 32];
        comp[0] = 0x58;
        let (x, _) = ed25519::decompress(&comp).unwrap();
        assert_eq!(
            x.to_string(),
            "15112221349535400772501151409588531511454012693041857206046113283949847762202"
        );
    }
}
