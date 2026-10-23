//! The TypeScript target: one `.ts` file holding what's specific to the circuit, over
//! the shared runtime `@blueshift-gg/xark-wasm/client` (`Field`, `Proof`, `Circuit`).
//!
//! * per enum, its variants as constants and their type (`Country.US`, or `"US"`);
//! * an interface per input struct, every value in its natural TypeScript form;
//! * the inputs, the public inputs as given, and as decoded from a proof;
//! * the circuit, a runtime `Circuit` that makes its provers and verifiers
//!   (`Zkyc.prover(wasm, url)`), with their types (`ZkycProver`, `ZkycProof`);
//! * the crate's Rust functions (`#[input] impl`), run from `client.wasm`.
//!
//! | standard type          | as given                      | decoded       |
//! |------------------------|-------------------------------|---------------|
//! | field                  | `FieldInput` (`Field`, an integer) | `Field`  |
//! | `uN`                   | `number` (`bigint` past 32)   | `number`/`bigint` |
//! | bool                   | `boolean`                     | `boolean`     |
//! | bytes                  | `Uint8Array`                  | `Uint8Array`  |
//! | number (limbed)        | an integer, or bytes          | `bigint`      |
//! | date                   | `Date` (its UTC day)          | `Date`        |
//! | text                   | `string`                      | `string`      |
//! | choice of `E`          | `E` (a variant name)          | `E`           |
//! | set of `E`             | `E \| readonly E[]`           | `E[]`         |
//! | array, tuple, struct   | arrays, an interface          | the same      |

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use anyhow::Result;
use xark_schema::camel;

use super::MARKER;
use super::model::{Model, Ty};

/// `zkyc_circuit` → `ZkycCircuit`.
pub fn pascal(s: &str) -> String {
    let c = camel(s);
    let mut chars = c.chars();
    match chars.next() {
        Some(f) => f.to_uppercase().chain(chars).collect(),
        None => "Circuit".into(),
    }
}

/// A TS property key for a field: `camelCase`, bare when it's an identifier, quoted
/// otherwise (tuple-struct `0`).
fn ts_key(name: &str) -> String {
    prop(&camel(name))
}

/// Property `key` (a [`ts_key`]) of `obj`: `obj.key`, or `obj["0"]` for a quoted one.
fn member(obj: &str, key: &str) -> String {
    if key.starts_with('"') {
        format!("{obj}[{key}]")
    } else {
        format!("{obj}.{key}")
    }
}

/// `name` as a TS property key, unchanged: bare when it's an identifier.
fn prop(name: &str) -> String {
    let ident = name
        .chars()
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_' || c == '$')
        && name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$');
    if ident {
        name.into()
    } else {
        format!("{name:?}")
    }
}

/// The TS type a caller passes for `ty`.
fn input(ty: &Ty) -> String {
    match ty {
        Ty::Field => "FieldInput".into(),
        Ty::Uint(w @ (8 | 16 | 32 | 64 | 128)) => format!("U{w}"),
        Ty::Uint(w) if *w <= 32 => "number".into(),
        Ty::Uint(_) => "bigint | number".into(),
        Ty::Bool => "boolean".into(),
        Ty::Bytes { .. } => "Uint8Array".into(),
        Ty::Number { .. } => "bigint | number | string | Uint8Array".into(),
        Ty::Date => "Day".into(),
        Ty::Text { max: TEXT } => "Text".into(),
        Ty::Text { .. } => "string".into(),
        Ty::Choice(e) => e.clone(),
        Ty::Set(e) => format!("{e} | readonly {e}[]"),
        Ty::Array(t, n) if *n as usize <= TUPLE => {
            format!("readonly [{}]", vec![input(t); *n as usize].join(", "))
        }
        Ty::Array(t, _) => format!("readonly {}[]", paren(&input(t))),
        Ty::Tuple(ts) => {
            let parts: Vec<String> = ts.iter().map(input).collect();
            format!("readonly [{}]", parts.join(", "))
        }
        Ty::Struct(r) => r.clone(),
    }
}

/// The TS type of `ty` decoded from a proof; notes the structs it needs decoders for.
fn value(ty: &Ty, structs: &mut BTreeSet<String>) -> String {
    match ty {
        Ty::Field => "Field".into(),
        Ty::Number { .. } => "bigint".into(),
        Ty::Uint(w) if *w <= 53 => "number".into(),
        Ty::Uint(_) => "bigint".into(),
        Ty::Bool => "boolean".into(),
        Ty::Bytes { .. } => "Uint8Array".into(),
        Ty::Date => "Day".into(),
        Ty::Text { max: TEXT } => "Text".into(),
        Ty::Text { .. } => "string".into(),
        Ty::Choice(e) => e.clone(),
        Ty::Set(e) => format!("{e}[]"),
        Ty::Array(t, n) if *n as usize <= TUPLE => {
            format!("[{}]", vec![value(t, structs); *n as usize].join(", "))
        }
        Ty::Array(t, _) => format!("{}[]", paren(&value(t, structs))),
        Ty::Tuple(ts) => {
            let parts: Vec<String> = ts.iter().map(|t| value(t, structs)).collect();
            format!("[{}]", parts.join(", "))
        }
        Ty::Struct(r) => {
            structs.insert(r.clone());
            format!("{r}Value")
        }
    }
}

/// An expression converting `e` (the decoded JSON for `ty`) to its TS value.
fn revive(ty: &Ty, e: &str) -> String {
    match ty {
        Ty::Field => format!("new Field({e})"),
        Ty::Number { .. } => format!("BigInt({e})"),
        Ty::Uint(w) if *w > 53 => format!("BigInt({e})"),
        Ty::Uint(_) | Ty::Bool | Ty::Text { .. } | Ty::Choice(_) | Ty::Set(_) => e.into(),
        Ty::Bytes { .. } => format!("fromHex({e})"),
        Ty::Date => format!("new Date({e})"),
        // Element by element, so a fixed length stays a tuple.
        Ty::Array(t, n) if *n as usize <= TUPLE => {
            let parts: Vec<String> = (0..*n).map(|i| revive(t, &format!("{e}[{i}]"))).collect();
            format!("[{}]", parts.join(", "))
        }
        Ty::Array(t, _) => format!("{e}.map((x) => {})", revive(t, "x")),
        Ty::Tuple(ts) => {
            let parts: Vec<String> = ts
                .iter()
                .enumerate()
                .map(|(i, t)| revive(t, &format!("{e}[{i}]")))
                .collect();
            format!("[{}]", parts.join(", "))
        }
        Ty::Struct(r) => format!("decode{r}({e})"),
    }
}

/// A doc line for what the TS type doesn't say (widths, lengths, limits).
fn note(ty: &Ty) -> Option<String> {
    Some(match ty {
        // Named aliases (`U64`, `Day`, `Text`) carry their own docs, and a tuple its length.
        Ty::Uint(8 | 16 | 32 | 64 | 128) | Ty::Date | Ty::Text { max: TEXT } => return None,
        Ty::Array(_, n) if *n as usize <= TUPLE => return None,
        Ty::Choice(_) => return None,
        Ty::Uint(w) => format!("`u{w}`: an integer in [0, 2^{w})."),
        Ty::Bytes {
            of: None,
            len: Some(n),
        } => format!("`[u8; {n}]`: exactly {n} bytes."),
        Ty::Bytes {
            of: Some(r),
            len: Some(n),
        } => format!("`{r}`: its {n} bytes."),
        Ty::Bytes {
            of: Some(r),
            len: None,
        } => format!("`{r}`: its bytes."),
        Ty::Bytes { .. } => return None,
        Ty::Number { of } => format!("`{of}`: the number, or its little-endian bytes."),
        Ty::Text { max } => format!("Text: at most {max} UTF-8 bytes."),
        Ty::Set(e) => format!("A set of `{e}`: one, or a list of them."),
        Ty::Array(_, n) => format!("Exactly {n} elements."),
        Ty::Field | Ty::Bool | Ty::Tuple(_) | Ty::Struct(_) => return None,
    })
}

/// The client functions (`#[input]` on an `impl`): per type, an object of typed functions
/// running the Rust code in `client.wasm` (`Policy.default()`). Also returned: per type,
/// its `self` methods as class members of its decoded value, so they chain on
/// whatever a function returns (`Policy.default().on(day).minAge(18)`).
fn exports_ts(
    m: &Model,
    value_structs: &mut BTreeSet<String>,
) -> (String, BTreeMap<String, String>) {
    let mut out = String::new();
    let mut methods: BTreeMap<String, String> = BTreeMap::new();
    let circuit = pascal(&m.circuit);
    let mut types: Vec<&str> = Vec::new();
    for e in &m.exports {
        if !types.contains(&e.ty.as_str()) {
            types.push(&e.ty);
        }
    }
    let jsdoc = |doc: &str, indent: &str| {
        if doc.is_empty() {
            return String::new();
        }
        let mut d = format!("{indent}/**\n");
        for line in doc.lines() {
            let _ = writeln!(d, "{indent} * {line}");
        }
        let _ = writeln!(d, "{indent} */");
        d
    };
    for t in types {
        let this = camel(&t.to_lowercase());
        let _ = writeln!(
            out,
            "/** `{t}`'s Rust functions (`#[input] impl {t}`), run from `client.wasm`. */\nexport const {t} = {{"
        );
        for e in m.exports.iter().filter(|e| e.ty == t) {
            let params: Vec<String> = e
                .params
                .iter()
                .map(|p| format!("{}: {}", ts_key(&p.name), input(&p.ty)))
                .collect();
            let names: Vec<String> = e.params.iter().map(|p| ts_key(&p.name)).collect();
            let mut all_params = params.clone();
            let mut all_names = names.clone();
            if e.receiver.is_some() {
                all_params.insert(0, format!("{this}: {t}"));
                all_names.insert(0, this.clone());
            }
            let ret = value(&e.returns, value_structs);
            let call = format!(
                "{circuit}.call<Json<{ret}>>({:?}, [{}])",
                e.export,
                all_names.join(", ")
            );
            out.push_str(&jsdoc(&e.doc, "  "));
            let _ = writeln!(
                out,
                "  {}({}): {ret} {{\n    return {};\n  }},",
                camel(&e.name),
                all_params.join(", "),
                revive(&e.returns, &call)
            );
            // A method named like one of the type's fields can't sit on a value beside
            // it (in Rust they don't clash): it stays `Type.method(value, …)` only,
            // and `xark client` says so.
            if e.receiver.is_some() && !m.shares_field_name(e) {
                let body = methods.entry(t.to_string()).or_default();
                body.push_str(&jsdoc(&e.doc, "  "));
                let _ = writeln!(
                    body,
                    "  {n}({p}): {ret} {{\n    return {t}.{n}(this{a});\n  }}\n",
                    n = camel(&e.name),
                    p = params.join(", "),
                    a = names.iter().map(|n| format!(", {n}")).collect::<String>(),
                );
            }
        }
        out.push_str("};\n\n");
    }
    (out, methods)
}

/// `a | b` → `(a | b)` where it needs the parentheses (an array element).
fn paren(t: &str) -> String {
    if t.contains(' ') {
        format!("({t})")
    } else {
        t.into()
    }
}

/// The generated TypeScript module for `m`.
/// The circuit's `schema.json` as a module the client imports: the same JSON as its
/// default export, so the client needs no JSON-import settings.
pub fn schema_module(circuit: &str, schema: &serde_json::Value) -> Result<String> {
    Ok(format!(
        "// {MARKER}: the `{circuit}` circuit's schema.json, which its client imports.\n\
         const schema = {};\n\
         export default schema;\n",
        serde_json::to_string_pretty(schema)?
    ))
}

/// The client, importing its schema from `schema_import` (`./zkyc.schema`, the `.ts`).
pub fn generate(m: &Model, schema_import: &str) -> Result<String> {
    let circuit = m.circuit.as_str();
    let name = pascal(circuit);
    let mut out = String::new();

    // Where this came from.
    let sig: Vec<String> = m
        .inputs
        .iter()
        .map(|(f, public)| {
            let vis = if *public { "Public" } else { "Private" };
            format!("{}: {vis}<{}>", f.name, f.rust)
        })
        .collect();
    let _ = writeln!(
        out,
        "// {MARKER} from `schema.json`: a typed client for the `{circuit}` circuit.\n\
         //\n\
         //   #[circuit]\n\
         //   fn {circuit}({})\n\
         //\n\
         // `xark build` records the circuit's parameter types in target/xark/{circuit}/schema.json\n\
         // and `xark client` turns them into the types below. Don't edit this file: change\n\
         // the circuit, then rebuild and rerun `xark client`. Values go in their natural\n\
         // forms (dates, strings, variant names, bytes); xark-wasm encodes them against the\n\
         // schema (in `{schema_import}.ts`, written with this file), exactly as `xark prove\n\
         // --inputs` does.\n",
        sig.join(", "),
    );

    // The runtime's imports go here, once the body says which it uses.
    let head = std::mem::take(&mut out);

    // Enums: the variants as constants (`Country.US`) and their type (`"AD" | …`), so
    // a value is checked, and either form passes.
    for (e, variants) in &m.enums {
        let _ = writeln!(
            out,
            "/** A `{e}` (an enum in the circuit): `{e}.{v}`, or its name, `{v:?}`. */\n\
             export const {e} = {{",
            v = variants.first().map_or("", String::as_str),
        );
        for chunk in variants.chunks(8) {
            let row: Vec<String> = chunk
                .iter()
                .map(|v| format!("{}: {v:?},", prop(v)))
                .collect();
            let _ = writeln!(out, "  {}", row.join(" "));
        }
        let _ = writeln!(
            out,
            "}} as const;\nexport type {e} = (typeof {e})[keyof typeof {e}];\n"
        );
    }

    // Input structs.
    for (r, fields) in &m.structs {
        let _ = writeln!(
            out,
            "/** {} `{r}` (an input struct). */\nexport interface {r} {{",
            article(r)
        );
        for f in fields {
            if let Some(n) = note(&f.ty) {
                let _ = writeln!(out, "  /** {n} */");
            }
            let _ = writeln!(out, "  {}: {};", ts_key(&f.name), input(&f.ty));
        }
        out.push_str("}\n\n");
    }

    // The inputs.
    let fields = |out: &mut String, public_only: bool| {
        for (f, public) in &m.inputs {
            if public_only && !public {
                continue;
            }
            if let Some(n) = note(&f.ty) {
                let _ = writeln!(out, "  /** {n} */");
            }
            let _ = writeln!(out, "  {}: {};", ts_key(&f.name), input(&f.ty));
        }
    };
    let _ = writeln!(
        out,
        "/** Every input of `{circuit}`. */\nexport interface {name}Inputs {{"
    );
    fields(&mut out, false);
    out.push_str("}\n\n");
    let _ = writeln!(
        out,
        "/** The public inputs: what a verifier supplies, and what a proof reveals. */\n\
         export interface {name}PublicInputs {{"
    );
    fields(&mut out, true);
    out.push_str("}\n\n");

    // The public inputs as decoded.
    let mut value_structs = BTreeSet::new();
    let mut body = String::new();
    let _ = writeln!(
        body,
        "/** The public inputs, decoded from a proof. */\nexport interface {name}PublicValues {{"
    );
    let mut decode = String::new();
    let _ = writeln!(
        decode,
        "function decodePublic(v: Json<{name}PublicValues>): {name}PublicValues {{\n  return {{"
    );
    for f in m.public() {
        let k = ts_key(&f.name);
        let _ = writeln!(body, "  {k}: {};", value(&f.ty, &mut value_structs));
        let _ = writeln!(decode, "    {k}: {},", revive(&f.ty, &member("v", &k)));
    }
    body.push_str("}\n\n");
    decode.push_str("  };\n}\n\n");
    // The client functions (their decoders join the ones below).
    let (exports, methods) = exports_ts(m, &mut value_structs);

    // Decoded structs (closed over what the public inputs and exports reach): a
    // class when the type has Rust methods, so they chain on its values.
    let mut done = BTreeSet::new();
    let mut structs = String::new();
    while let Some(r) = value_structs.iter().find(|r| !done.contains(*r)).cloned() {
        done.insert(r.clone());
        let mut fields = String::new();
        let mut revived = String::new();
        for f in &m.structs[&r] {
            let k = ts_key(&f.name);
            let _ = writeln!(fields, "  {k}: {};", value(&f.ty, &mut value_structs));
            let _ = writeln!(revived, "    {k}: {},", revive(&f.ty, &member("v", &k)));
        }
        let (doc, open, close) = match methods.get(&r) {
            Some(_) => (
                format!("A `{r}`, decoded, with its Rust methods"),
                format!("new {r}Value({{"),
                "})",
            ),
            None => (format!("A `{r}`, decoded"), "{".to_string(), "}"),
        };
        let _ = writeln!(
            decode,
            "function decode{r}(v: Json<{r}Value>): {r}Value {{\n  return {open}\n{revived}  }}{};\n}}\n",
            &close[1..],
        );
        match methods.get(&r) {
            Some(_)
                if m.structs[&r]
                    .iter()
                    .any(|f| ts_key(&f.name) == "constructor") =>
            {
                anyhow::bail!(
                    "`{r}` has a field named `constructor` and Rust methods: its client \
                     class can't have that field. Rename the field"
                );
            }
            Some(body) => {
                let assign: String = m.structs[&r]
                    .iter()
                    .map(|f| {
                        let k = ts_key(&f.name);
                        format!("    {} = {};\n", member("this", &k), member("v", &k))
                    })
                    .collect();
                let _ = writeln!(
                    structs,
                    "/** {doc}. */\nexport class {r}Value {{\n{fields}\n  \
                     constructor(v: {{\n{inner}  }}) {{\n{assign}  }}\n\n{body}}}\n",
                    inner = fields
                        .lines()
                        .map(|l| format!("  {l}\n"))
                        .collect::<String>(),
                    body = body.trim_end_matches('\n').to_string() + "\n",
                );
            }
            None => {
                let _ = writeln!(
                    structs,
                    "/** {doc}. */\nexport interface {r}Value {{\n{fields}}}\n"
                );
            }
        }
    }
    out.push_str(&structs);
    out.push_str(&body);

    // The structs `fields` takes, by name.
    let structs = if m.structs.is_empty() {
        "{}".to_string()
    } else {
        let _ = writeln!(
            out,
            "/** The input structs, by name: what `fields` takes. */\nexport interface {name}Structs {{"
        );
        for r in m.structs.keys() {
            let _ = writeln!(out, "  {}: {r};", prop(r));
        }
        out.push_str("}\n\n");
        format!("{name}Structs")
    };

    // The circuit.
    let _ = writeln!(
        out,
        "/**\n \
         * `{circuit}`: make a prover or verifier from a URL serving a copy of\n \
         * `target/xark/{circuit}/` (relative to the page in a browser) or from the bytes:\n \
         *\n \
         * ```ts\n \
         * const prover = await {name}.prover(\"/circuits/{circuit}/\");\n \
         * const proof = prover.prove(inputs);\n \
         * send(proof.toBytes()); // the proof; an exported Solana verifier reads it as is\n \
         * const verifier = await {name}.verifier(vkBytes);\n \
         * verifier.verify(bytes, publicInputs); // true: it proves the public inputs you require\n \
         * ```\n \
         */\n\
         export const {name} = new Circuit<{name}Inputs, {name}PublicInputs, {name}PublicValues, {structs}>({{\n  \
         name: {circuit:?},\n  \
         schema,\n  \
         decodePublic,\n  \
         client: {},\n{}\
         }});\n\n\
         export type {name}Prover = Prover<{name}Inputs, {name}PublicInputs, {name}PublicValues, {structs}>;\n\
         export type {name}Verifier = Verifier<{name}PublicInputs, {name}PublicValues, {structs}>;\n\
         export type {name}Proof = Proof<{name}PublicValues>;\n",
        !m.exports.is_empty(),
        m.digest
            .as_ref()
            .map_or(String::new(), |d| format!("  digest: {d:?},\n")),
    );
    out.push_str(&exports);
    out.push_str(&decode);
    let out = out.trim_end().to_string() + "\n";

    // Import what the body uses from the runtime, and re-export `Field`.
    let values = [
        "CheckFailed",
        "Circuit",
        "Field",
        "InputError",
        "fromHex",
        "toHex",
    ];
    // The runtime's types the body names (outside comments).
    let code: String = out
        .lines()
        .filter(|l| !l.trim_start().starts_with("//") && !l.trim_start().starts_with('*'))
        .collect::<Vec<_>>()
        .join("\n");
    let names = |name: &str| {
        code.match_indices(name).any(|(i, _)| {
            let ident = |c: char| c.is_ascii_alphanumeric() || c == '_' || c == '$';
            !code[..i].ends_with(ident) && !code[i + name.len()..].starts_with(ident)
        })
    };
    let mut types: Vec<&str> = [
        "Day",
        "FieldInput",
        "Json",
        "Proof",
        "Prover",
        "Text",
        "U128",
        "U16",
        "U32",
        "U64",
        "U8",
        "Verifier",
    ]
    .into_iter()
    .filter(|t| matches!(*t, "Json" | "Proof" | "Prover" | "Verifier") || names(t))
    .collect();
    types.sort();
    let imports: Vec<String> = values
        .iter()
        .map(|v| v.to_string())
        .chain(types.iter().map(|t| format!("type {t}")))
        .collect();
    Ok(format!(
        "{head}\
         import {{ {} }} from \"{RUNTIME}\";\n\
         import schema from \"./{schema_import}\";\n\
         export {{ CheckFailed, Field, InputError, fromHex, toHex }};\n\n\
         {out}",
        imports.join(", ")
    ))
}

/// "A" or "An", for a name.
fn article(name: &str) -> &'static str {
    match name.chars().next().map(|c| c.to_ascii_lowercase()) {
        Some('a' | 'e' | 'i' | 'o' | 'u') => "An",
        _ => "A",
    }
}

/// `Text`'s length, the standard one the runtime's `Text` alias documents.
const TEXT: u64 = 31;
/// Arrays up to this long are tuples (`readonly [Field, Field, Field, Field]`), so a
/// wrong length doesn't compile; longer ones are arrays checked when encoded.
const TUPLE: usize = 16;

/// The module every generated client imports: `Field`, `Proof`, `Circuit`.
const RUNTIME: &str = "@blueshift-gg/xark-wasm/client";

#[cfg(test)]
mod tests {
    use super::*;

    const SCHEMA: &str = r#"{
      "version": 2,
      "circuit": "kyc_check",
      "inputs": [
        {"name": "id", "visibility": "private", "type": {"ref": "Identity"}},
        {"name": "born_before", "visibility": "public", "type": {"ref": "Date"}},
        {"name": "allowed", "visibility": "public", "type": {"ref": "Bitfield<Country>"}},
        {"name": "doc", "visibility": "private", "type": {"array": {"of": {"uint": 8}, "len": 4}}},
        {"name": "commitment", "visibility": "public", "type": "field"}
      ],
      "types": {
        "Identity": {"struct": [
          {"name": "net_worth", "type": {"uint": 64}},
          {"name": "salt", "type": "field"},
          {"name": "active", "type": "bool"},
          {"name": "home", "type": {"ref": "Choice<Country>"}},
          {"name": "tier", "type": {"ref": "Choice<Tier>"}},
          {"name": "pair", "type": {"tuple": ["field", {"uint": 16}]}}]},
        "Date": {"newtype": "field", "encoding": {"date": "yyyymmdd"}},
        "Bitfield<Country>": {"newtype": "field", "encoding": {"set": "Country"}},
        "Choice<Country>": {"newtype": "field", "encoding": {"choice": "Country"}},
        "Choice<Tier>": {"newtype": "field", "encoding": {"choice": "Tier"}},
        "Country": {"enum": ["AD", "US"]},
        "Tier": {"enum": ["Retail", "Not_Set"]}
      },
      "public_inputs": ["born_before", "allowed", "commitment"]
    }"#;

    #[test]
    fn names() {
        assert_eq!(pascal("zkyc_circuit"), "ZkycCircuit");
        assert_eq!(ts_key("net_worth"), "netWorth");
        assert_eq!(ts_key("0"), "\"0\"");
    }

    #[test]
    fn generates_natural_types() {
        let m = Model::new(&serde_json::from_str(SCHEMA).unwrap()).unwrap();
        let ts = generate(&m, "kyc_check.schema").unwrap();
        for want in [
            "fn kyc_check(id: Private<Identity>, born_before: Public<Date>, allowed: Public<Bitfield<Country>>, doc: Private<[u8; 4]>, commitment: Public<Field>)",
            "export const Country = {\n  AD: \"AD\", US: \"US\",\n} as const;\nexport type Country = (typeof Country)[keyof typeof Country];",
            "/** An `Identity` (an input struct). */\nexport interface Identity {\n  netWorth: U64;",
            "  home: Country;",
            "  Retail: \"Retail\", Not_Set: \"Not_Set\",",
            "  pair: readonly [FieldInput, U16];",
            "  active: boolean;",
            "  bornBefore: Day;",
            "  allowed: Country | readonly Country[];",
            "  doc: Uint8Array;",
            "export interface KycCheckPublicValues {\n  bornBefore: Day;\n  allowed: Country[];\n  commitment: Field;\n}",
            "    bornBefore: new Date(v.bornBefore),",
            "    commitment: new Field(v.commitment),",
            "import { CheckFailed, Circuit, Field, InputError, fromHex, toHex, type Day, type FieldInput, type Json, type Proof, type Prover, type U16, type U64, type Verifier } from \"@blueshift-gg/xark-wasm/client\";\nimport schema from \"./kyc_check.schema\";\nexport { CheckFailed, Field, InputError, fromHex, toHex };",
            "  name: \"kyc_check\",\n  schema,\n",
            "export interface KycCheckStructs {\n  Identity: Identity;\n}",
            "export const KycCheck = new Circuit<KycCheckInputs, KycCheckPublicInputs, KycCheckPublicValues, KycCheckStructs>({\n  name: \"kyc_check\",",
            "  client: false,\n});",
            "export type KycCheckProof = Proof<KycCheckPublicValues>;",
        ] {
            assert!(ts.contains(want), "missing {want:?} in:\n{ts}");
        }
        assert!(ts.starts_with("// Generated by `xark client`"));
        assert!(!ts.contains("__NAME__") && !ts.contains("__SCHEMA__"));
        // No `any`: every value the runtime hands back is typed as `Json<…>`.
        for any in [": any", "<any>", "as any"] {
            assert!(!ts.contains(any), "{any:?} in:\n{ts}");
        }
    }
}
