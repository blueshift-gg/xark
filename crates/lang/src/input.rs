//! Circuit inputs: the [`Input`] trait, and the [`Type`] vocabulary every client
//! language maps to its own types.
//!
//! A type is a circuit input when it implements [`Input`], usually through
//! `#[input]`:
//!
//! ```ignore
//! #[input]
//! pub struct Identity { pub born: Date, pub net_worth: u64, pub salt: Field }
//! ```
//!
//! An impl says three things, and the same impl serves the circuit build and the
//! host:
//!
//! * [`Input::TYPE`]: what the value looks like to clients, built from the standard
//!   types below. `xark build` writes it to `schema.json`, and each client
//!   generator (`xark client`) maps it to that language's types.
//! * [`Input::read`]: build the value from its field elements, in order (the circuit's
//!   inputs in a circuit build, known values on the host).
//! * [`Input::write`]: the value's field elements, in the same order (for hashing in
//!   the circuit, for the prover on the host).
//!
//! By hand, for a gadget type:
//!
//! ```ignore
//! impl Input for Hash {
//!     const TYPE: Type = Type::Named(
//!         &Type::named("Hash", Layout::fields(&[Member::new("hi", Type::Field), Member::new("lo", Type::Field)]))
//!             .encoded(Encoding::Bytes(Bytes::Split(&[16, 16]))),
//!     );
//!     fn read(r: &mut Reader) -> Self { Hash { hi: r.field(), lo: r.field() } }
//!     fn write(&self, w: &mut Writer) { w.field(self.hi); w.field(self.lo) }
//! }
//! ```
//!
//! `read` and `write` must visit the leaves `TYPE` names, in its order: the circuit
//! build checks the count, and the host build too.
//!
//! ## The standard types
//!
//! | `Type`                     | Rust              | value, as JSON (`schema.json`, `--inputs`) |
//! |----------------------------|-------------------|--------------------------------------------|
//! | `Field`                    | `Field`           | a decimal or `0x`-hex string, or a number  |
//! | `Uint(n)`                  | `u8` … `u128`     | a number, or a decimal string              |
//! | `Bool`                     | `bool`            | `true` / `false` (or `1` / `0`)            |
//! | `Array(Uint(8), n)`        | `[u8; N]`         | `0x`-hex, or an array of numbers           |
//! | `Array`, `Tuple`           | `[T; N]`, `(A, B)`| an array                                   |
//! | named, [`Encoding::Fields`]| a struct          | an object of its fields                    |
//! | [`Encoding::Date`]         | [`Date`](crate::Date) | `"YYYY-MM-DD"`                         |
//! | [`Encoding::Text`]         | [`Text`](crate::Text) | a string                               |
//! | [`Encoding::Choice`]       | [`Choice<E>`](crate::Choice) | a variant name: `"US"`          |
//! | [`Encoding::Set`]          | [`Bitfield<E>`](crate::Bitfield) | a list of variant names     |
//! | [`Encoding::Number`]       | a limbed number   | a decimal or `0x`-hex string               |
//! | [`Encoding::Bytes`]        | a curve point, a hash | `0x`-hex bytes                         |
//!
//! The leaves are named by the layout: `id.born`, `msg[3]`, `pair.0`, `q.x.limbs[2]`.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use crate::lang::Field;

/// A circuit input type: how it looks to clients, and how its value maps to field
/// elements. `#[input]` implements it for a struct of inputs.
pub trait Input: Sized {
    /// The type as clients see it.
    const TYPE: Type;
    /// The number of field elements (the circuit's input leaves) a value takes.
    const LEN: usize = Self::TYPE.leaves();
    /// Build a value from its field elements, read in order.
    fn read(r: &mut Reader<'_>) -> Self;
    /// Write the value's field elements, in the order [`Input::read`] reads them.
    fn write(&self, w: &mut Writer<'_>);
}

/// A fieldless enum usable as a [`Choice`](crate::Choice) (one variant) or a
/// [`Bitfield`](crate::Bitfield) (a set of them): `#[input]` on the enum
/// implements it. Append variants only, never reorder: a variant's position is its
/// value.
///
/// A Rust enum's variant is fixed when the code runs, so in a circuit an unknown
/// one is always a `Choice<E>` or `Bitfield<E>`; the enum itself names constants
/// (`Country::US`).
pub trait Enum: Copy + 'static {
    /// The enum's name and variant names, in order.
    const VARIANTS: Variants;
    /// This variant's position.
    fn index(self) -> usize;
    /// The variant at `index`.
    fn from_index(index: usize) -> Option<Self>;

    /// This variant's name.
    fn name(self) -> &'static str {
        Self::VARIANTS.names[self.index()]
    }
    /// The variant named `name`.
    fn from_name(name: &str) -> Option<Self> {
        let i = Self::VARIANTS.names.iter().position(|n| *n == name)?;
        Self::from_index(i)
    }
}

/// An enum's name and variant names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Variants {
    pub name: &'static str,
    pub names: &'static [&'static str],
}

/// A circuit input type's shape, as clients see it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Type {
    /// One field element.
    Field,
    /// An unsigned integer of this many bits, range-checked on entry.
    Uint(u32),
    /// `true` or `false`: one field element, `0` or `1`, checked on entry.
    Bool,
    /// `N` values of one type, named `name[i]`.
    Array(&'static Type, usize),
    /// Values of different types, named `name.0`, `name.1`, …
    Tuple(&'static [Type]),
    /// A named type: a struct, or a standard type such as `Date`.
    Named(&'static Named),
}

/// A named input type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Named {
    /// The type's name (`Identity`, `Bitfield`).
    pub name: &'static str,
    /// A type argument shown in the name: `Bitfield<Country>`.
    pub arg: Option<&'static str>,
    /// Its leaves.
    pub layout: Layout,
    /// How a client gives a value of it.
    pub encoding: Encoding,
}

/// A named type's leaves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Layout {
    /// The leaves of one inner type, at the value's own name (`Date` is one field).
    Newtype(Type),
    /// Named fields, each at `name.field`.
    Struct(&'static [Member]),
}

/// A struct field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Member {
    pub name: &'static str,
    pub ty: Type,
}

/// How a client gives a value of a named type. Each is a standard type every
/// client language maps to one of its own.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Encoding {
    /// An object of its fields (a struct), or its inner type's form (a newtype).
    Fields,
    /// A calendar day, `"YYYY-MM-DD"`; one field holding `YYYYMMDD`.
    Date,
    /// A string of at most this many UTF-8 bytes; one field, little-endian.
    Text(usize),
    /// One variant of an enum, by name; one field holding its position.
    Choice(&'static Variants),
    /// A set of an enum's variants; one field, bit `i` for variant `i`.
    Set(&'static Variants),
    /// A whole number, split into the layout's leaves as little-endian limbs of
    /// this many bits.
    Number { bits: usize },
    /// A byte string, split into the layout's leaves.
    Bytes(Bytes),
}

/// How a byte-encoded type's bytes split into its leaves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Bytes {
    /// Each field's own byte encoding, back to back (a point's `x ‖ y`).
    Concat,
    /// [`Bytes::Concat`], also accepting a SEC1 `0x04` prefix.
    Sec1,
    /// Big-endian chunks of these sizes, one per field (`Hash`: 16 + 16).
    Split(&'static [usize]),
    /// A compressed Ed25519 point (32 bytes), decompressed into `x`, `y`.
    Ed25519,
}

impl Type {
    /// A named type with this layout, given as an object of its fields.
    pub const fn named(name: &'static str, layout: Layout) -> Named {
        Named {
            name,
            arg: None,
            layout,
            encoding: Encoding::Fields,
        }
    }

    /// The number of leaves a value of this type takes.
    pub const fn leaves(&self) -> usize {
        match self {
            Type::Field | Type::Uint(_) | Type::Bool => 1,
            Type::Array(t, n) => t.leaves() * *n,
            Type::Tuple(ts) => {
                let (mut n, mut i) = (0, 0);
                while i < ts.len() {
                    n += ts[i].leaves();
                    i += 1;
                }
                n
            }
            Type::Named(n) => n.layout.leaves(),
        }
    }
}

impl Named {
    /// This type, given in `encoding`.
    pub const fn encoded(self, encoding: Encoding) -> Named {
        Named { encoding, ..self }
    }

    /// This type, named with a type argument (`Bitfield<Country>`).
    pub const fn with_arg(self, arg: &'static str) -> Named {
        Named {
            arg: Some(arg),
            ..self
        }
    }
}

impl Layout {
    /// Named fields: `Layout::fields(&[("x", Fp::TYPE), ("y", Fp::TYPE)])`.
    pub const fn fields(members: &'static [Member]) -> Layout {
        Layout::Struct(members)
    }

    pub const fn leaves(&self) -> usize {
        match self {
            Layout::Newtype(t) => t.leaves(),
            Layout::Struct(ms) => {
                let (mut n, mut i) = (0, 0);
                while i < ms.len() {
                    n += ms[i].ty.leaves();
                    i += 1;
                }
                n
            }
        }
    }
}

impl Member {
    pub const fn new(name: &'static str, ty: Type) -> Member {
        Member { name, ty }
    }
}

// ---- reading and writing ----------------------------------------------------------

/// Reads a value's field elements in order: the circuit's inputs (in a circuit
/// build), or known values (on the host). See [`Input::read`].
pub struct Reader<'a> {
    src: Source<'a>,
    at: usize,
}

enum Source<'a> {
    /// Bind circuit inputs with these leaf names.
    #[cfg_attr(not(all(xark, target_arch = "wasm32")), allow(dead_code))]
    Inputs { names: &'a [String], public: bool },
    /// Read these values.
    #[cfg_attr(all(xark, target_arch = "wasm32"), allow(dead_code))]
    Values(&'a [Field]),
}

impl<'a> Reader<'a> {
    /// A reader over known values (`Input::LEN` of them).
    pub fn new(values: &'a [Field]) -> Reader<'a> {
        Reader {
            src: Source::Values(values),
            at: 0,
        }
    }

    /// The next value.
    pub fn read<T: Input>(&mut self) -> T {
        T::read(self)
    }

    /// The next leaf, a field element.
    pub fn field(&mut self) -> Field {
        let at = self.next();
        match &self.src {
            #[cfg(all(xark, target_arch = "wasm32"))]
            Source::Inputs { names, public } => crate::wasm::bind_field(leaf(names, at), *public),
            Source::Values(v) => v[at],
            #[allow(unreachable_patterns)]
            _ => unreachable!(),
        }
    }

    /// The next leaf, an unsigned integer of `bits ≤ 64` bits (range-checked when
    /// it is a circuit input).
    pub fn uint(&mut self, bits: u32) -> u64 {
        let at = self.next();
        match &self.src {
            #[cfg(all(xark, target_arch = "wasm32"))]
            Source::Inputs { names, public } => {
                crate::wasm::bind_uint(leaf(names, at), *public, bits)
            }
            Source::Values(v) => {
                let _ = bits;
                v[at].to_limbs()[0]
            }
            #[allow(unreachable_patterns)]
            _ => unreachable!(),
        }
    }

    /// The next leaf, a `bool` (checked to be `0` or `1` when it is a circuit input).
    pub fn bool(&mut self) -> bool {
        let at = self.next();
        match &self.src {
            #[cfg(all(xark, target_arch = "wasm32"))]
            Source::Inputs { names, public } => crate::wasm::bind_bool(leaf(names, at), *public),
            Source::Values(v) => !v[at].is_zero(),
            #[allow(unreachable_patterns)]
            _ => unreachable!(),
        }
    }

    /// The next leaf, a `u128` (range-checked when it is a circuit input).
    pub fn u128(&mut self) -> u128 {
        let at = self.next();
        match &self.src {
            #[cfg(all(xark, target_arch = "wasm32"))]
            Source::Inputs { names, public } => crate::wasm::bind_u128(leaf(names, at), *public),
            Source::Values(v) => {
                let l = v[at].to_limbs();
                (l[1] as u128) << 64 | l[0] as u128
            }
            #[allow(unreachable_patterns)]
            _ => unreachable!(),
        }
    }

    fn next(&mut self) -> usize {
        self.at += 1;
        self.at - 1
    }
}

/// Leaf `at`'s name, without a panicking branch (an impl reading past its `TYPE` is
/// reported after the body, by [`Binder::finish`]).
#[cfg(all(xark, target_arch = "wasm32"))]
#[inline(always)]
fn leaf(names: &[String], at: usize) -> &str {
    names.get(at).map_or("", String::as_str)
}

/// Collects a value's field elements in order. See [`Input::write`].
pub struct Writer<'a> {
    out: &'a mut [Field],
    at: usize,
}

impl<'a> Writer<'a> {
    /// A writer filling `out` (`Input::LEN` long).
    pub fn new(out: &'a mut [Field]) -> Writer<'a> {
        Writer { out, at: 0 }
    }

    /// Write `value`'s field elements.
    pub fn write<T: Input>(&mut self, value: &T) {
        value.write(self)
    }

    /// Write one field element.
    pub fn field(&mut self, f: Field) {
        self.out[self.at] = f;
        self.at += 1;
    }
}

/// `value`'s field elements, in input order (what `#[input]`'s `to_fields`
/// returns): `out` must be `T::LEN` long.
pub fn write_fields<T: Input>(value: &T, out: &mut [Field]) {
    value.write(&mut Writer::new(out))
}

/// A value from its field elements (`T::LEN` of them), in input order.
pub fn from_fields<T: Input>(values: &[Field]) -> T {
    T::read(&mut Reader::new(values))
}

// ---- the standard impls ------------------------------------------------------------

impl Input for Field {
    const TYPE: Type = Type::Field;
    fn read(r: &mut Reader<'_>) -> Self {
        r.field()
    }
    fn write(&self, w: &mut Writer<'_>) {
        w.field(*self)
    }
}

macro_rules! uint_input {
    ($($t:ty => $w:literal),*) => {$(
        impl Input for $t {
            const TYPE: Type = Type::Uint($w);
            fn read(r: &mut Reader<'_>) -> Self {
                r.uint($w) as $t
            }
            fn write(&self, w: &mut Writer<'_>) {
                w.field(Field::from(*self))
            }
        }
    )*};
}
uint_input!(u8 => 8, u16 => 16, u32 => 32, u64 => 64);

impl Input for u128 {
    const TYPE: Type = Type::Uint(128);
    fn read(r: &mut Reader<'_>) -> Self {
        r.u128()
    }
    fn write(&self, w: &mut Writer<'_>) {
        w.field(Field::from(*self))
    }
}

impl Input for bool {
    const TYPE: Type = Type::Bool;
    fn read(r: &mut Reader<'_>) -> Self {
        r.bool()
    }
    fn write(&self, w: &mut Writer<'_>) {
        w.field(Field::from(*self))
    }
}

impl<T: Input, const N: usize> Input for [T; N] {
    const TYPE: Type = Type::Array(&T::TYPE, N);
    fn read(r: &mut Reader<'_>) -> Self {
        core::array::from_fn(|_| T::read(r))
    }
    fn write(&self, w: &mut Writer<'_>) {
        let mut i = 0;
        while i < N {
            self[i].write(w);
            i += 1;
        }
    }
}

macro_rules! tuple_input {
    ($(($($i:tt $t:ident),+))*) => {$(
        impl<$($t: Input),+> Input for ($($t,)+) {
            const TYPE: Type = Type::Tuple(&[$($t::TYPE),+]);
            fn read(r: &mut Reader<'_>) -> Self {
                ($($t::read(r),)+)
            }
            fn write(&self, w: &mut Writer<'_>) {
                $(self.$i.write(w);)+
            }
        }
    )*};
}
tuple_input!((0 A) (0 A, 1 B) (0 A, 1 B, 2 C) (0 A, 1 B, 2 C, 3 D));

// ---- leaf names and the schema -----------------------------------------------------

/// The leaf names of a `ty` value named `prefix`, in input order: `id.born`,
/// `msg[3]`, `q.x.limbs[2]`.
pub fn leaf_names(ty: &Type, prefix: &str) -> Vec<String> {
    let mut out = Vec::with_capacity(ty.leaves());
    let mut name = String::from(prefix);
    names_into(ty, &mut name, &mut out);
    out
}

fn names_into(ty: &Type, name: &mut String, out: &mut Vec<String>) {
    let at = name.len();
    match ty {
        Type::Field | Type::Uint(_) | Type::Bool => out.push(name.clone()),
        Type::Array(t, n) => {
            for i in 0..*n {
                name.push('[');
                push_usize(name, i);
                name.push(']');
                names_into(t, name, out);
                name.truncate(at);
            }
        }
        Type::Tuple(ts) => {
            for (i, t) in ts.iter().enumerate() {
                name.push('.');
                push_usize(name, i);
                names_into(t, name, out);
                name.truncate(at);
            }
        }
        Type::Named(n) => match n.layout {
            Layout::Newtype(t) => names_into(&t, name, out),
            Layout::Struct(ms) => {
                for m in ms {
                    name.push('.');
                    name.push_str(m.name);
                    names_into(&m.ty, name, out);
                    name.truncate(at);
                }
            }
        },
    }
}

fn push_usize(s: &mut String, mut n: usize) {
    let mut digits = [0u8; 20];
    let mut len = 0;
    loop {
        digits[len] = b'0' + (n % 10) as u8;
        len += 1;
        n /= 10;
        if n == 0 {
            break;
        }
    }
    while len > 0 {
        len -= 1;
        s.push(digits[len] as char);
    }
}

fn push_str_json(s: &mut String, v: &str) {
    s.push('"');
    for c in v.chars() {
        match c {
            '"' => s.push_str("\\\""),
            '\\' => s.push_str("\\\\"),
            c => s.push(c),
        }
    }
    s.push('"');
}

/// One `#[circuit]` parameter: its name, whether it is public, and its type.
pub type Param = (&'static str, bool, Type);

/// The circuit's `schema.json` (version 2): the xark version that wrote it, its inputs
/// in declaration order, every named type they reach under `types`, and the public
/// leaves in proof order.
///
/// ```text
/// {"version": 2, "xark": "0.3.0", "circuit": "zkyc",
///  "inputs": [{"name": "id", "visibility": "private", "type": {"ref": "Identity"}}, …],
///  "types": {"Identity": {"struct": [{"name": "born", "type": {"ref": "Date"}}, …]},
///            "Date": {"newtype": "field", "encoding": {"date": "yyyymmdd"}},
///            "Bitfield<Country>": {"newtype": "field", "encoding": {"set": "Country"}},
///            "Country": {"enum": ["AD", "AE", …]}, …},
///  "public_inputs": ["commitment", "born_before", …]}
/// ```
///
/// Panics if one name stands for two different types (two widths of a generic
/// `Bignum`, two crates' `Point`s): clients look types up by name.
pub fn schema_json(circuit: &str, params: &[Param]) -> String {
    let mut defs = Defs::default();
    // `xark`: the version that wrote it, so a client runtime can tell it was made for
    // another release.
    let mut s = String::from(concat!(
        "{\"version\":2,\"xark\":\"",
        env!("CARGO_PKG_VERSION"),
        "\",\"circuit\":"
    ));
    push_str_json(&mut s, circuit);
    s.push_str(",\"inputs\":[");
    for (i, (name, public, ty)) in params.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        s.push_str("{\"name\":");
        push_str_json(&mut s, name);
        s.push_str(if *public {
            ",\"visibility\":\"public\",\"type\":"
        } else {
            ",\"visibility\":\"private\",\"type\":"
        });
        type_json(ty, &mut defs, &mut s);
        s.push('}');
    }
    s.push_str("],\"types\":{");
    for (i, (name, def)) in defs.json.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        push_str_json(&mut s, name);
        s.push(':');
        s.push_str(def);
    }
    s.push_str("},\"public_inputs\":[");
    let mut first = true;
    for (name, _, ty) in params.iter().filter(|p| p.1) {
        for leaf in leaf_names(ty, name) {
            if !first {
                s.push(',');
            }
            first = false;
            push_str_json(&mut s, &leaf);
        }
    }
    s.push_str("]}");
    s
}

/// A named type's name in `schema.json`: `Identity`, `Bitfield<Country>`.
pub fn type_name(n: &Named) -> String {
    let mut s = String::from(n.name);
    if let Some(a) = n.arg {
        s.push('<');
        s.push_str(a);
        s.push('>');
    }
    s
}

/// The named types described so far.
#[derive(Default)]
struct Defs {
    /// Each one's `schema.json` definition.
    json: BTreeMap<String, String>,
    /// What each name first stood for, to refuse a second, different meaning.
    seen: BTreeMap<String, Seen>,
}

#[derive(Clone, Copy, PartialEq)]
enum Seen {
    Named(Named),
    Enum(Variants),
}

impl Defs {
    /// Claim `name` for `what`: `true` the first time, `false` when it already
    /// stands for exactly `what`.
    fn claim(&mut self, name: &str, what: Seen) -> bool {
        match self.seen.get(name) {
            None => {
                self.seen.insert(String::from(name), what);
                true
            }
            Some(w) if *w == what => false,
            Some(_) => panic!(
                "`{name}` names two different types among this circuit's inputs, and \
                 clients look types up by name: give one its own name (for a limbed number, \
                 an `fp!` type rather than a second width of `Bignum`)"
            ),
        }
    }
}

fn type_json(ty: &Type, defs: &mut Defs, s: &mut String) {
    match ty {
        Type::Field => s.push_str("\"field\""),
        Type::Bool => s.push_str("\"bool\""),
        Type::Uint(w) => {
            s.push_str("{\"uint\":");
            push_usize(s, *w as usize);
            s.push('}');
        }
        Type::Array(t, n) => {
            s.push_str("{\"array\":{\"of\":");
            type_json(t, defs, s);
            s.push_str(",\"len\":");
            push_usize(s, *n);
            s.push_str("}}");
        }
        Type::Tuple(ts) => {
            s.push_str("{\"tuple\":[");
            for (i, t) in ts.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                type_json(t, defs, s);
            }
            s.push_str("]}");
        }
        Type::Named(n) => {
            let name = type_name(n);
            // Claimed before it is described, so a type reached twice is described once.
            if defs.claim(&name, Seen::Named(**n)) {
                let def = named_json(n, defs);
                defs.json.insert(name.clone(), def);
            }
            s.push_str("{\"ref\":");
            push_str_json(s, &name);
            s.push('}');
        }
    }
}

fn named_json(n: &Named, defs: &mut Defs) -> String {
    let mut s = String::from("{");
    match n.layout {
        Layout::Newtype(t) => {
            s.push_str("\"newtype\":");
            type_json(&t, defs, &mut s);
        }
        Layout::Struct(ms) => {
            s.push_str("\"struct\":[");
            for (i, m) in ms.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                s.push_str("{\"name\":");
                push_str_json(&mut s, m.name);
                s.push_str(",\"type\":");
                type_json(&m.ty, defs, &mut s);
                s.push('}');
            }
            s.push(']');
        }
    }
    if n.encoding != Encoding::Fields {
        s.push_str(",\"encoding\":");
        encoding_json(n, defs, &mut s);
    }
    s.push('}');
    s
}

fn encoding_json(n: &Named, defs: &mut Defs, s: &mut String) {
    let mut variants = |v: &Variants, kind: &str, s: &mut String| {
        s.push_str("{\"");
        s.push_str(kind);
        s.push_str("\":");
        push_str_json(s, v.name);
        s.push('}');
        let mut d = String::from("{\"enum\":[");
        for (i, name) in v.names.iter().enumerate() {
            if i > 0 {
                d.push(',');
            }
            push_str_json(&mut d, name);
        }
        d.push_str("]}");
        if defs.claim(v.name, Seen::Enum(*v)) {
            defs.json.insert(String::from(v.name), d);
        }
    };
    match n.encoding {
        Encoding::Fields => s.push_str("null"),
        Encoding::Date => s.push_str("{\"date\":\"yyyymmdd\"}"),
        Encoding::Text(max) => {
            s.push_str("{\"text\":");
            push_usize(s, max);
            s.push('}');
        }
        Encoding::Choice(v) => variants(v, "choice", s),
        Encoding::Set(v) => variants(v, "set", s),
        Encoding::Number { bits } => {
            s.push_str("{\"bytes\":");
            push_usize(s, crate::natural_bytes(n.layout.leaves(), bits));
            s.push_str(",\"limbs\":");
            push_usize(s, bits);
            s.push('}');
        }
        Encoding::Bytes(Bytes::Concat) => s.push_str("{\"concat\":\"fields\"}"),
        Encoding::Bytes(Bytes::Sec1) => s.push_str("{\"concat\":\"fields\",\"sec1\":true}"),
        Encoding::Bytes(Bytes::Split(sizes)) => {
            s.push_str("{\"bytes\":");
            push_usize(s, sizes.iter().sum());
            s.push_str(",\"concat\":[");
            for (i, k) in sizes.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                push_usize(s, *k);
            }
            s.push_str("]}");
        }
        Encoding::Bytes(Bytes::Ed25519) => s.push_str("{\"bytes\":32,\"ed25519\":true}"),
    }
}

// ---- binding (circuit build) and the prover's leaves (host) -------------------------

/// The entry shim's input binding (circuit build): the schema is recorded and every
/// parameter's leaf names worked out before any input is bound, and the leaf counts
/// checked only after the body has run, so nothing but the input imports runs
/// between binding an input and using it. (Code in between can make LLVM carry a
/// small value, such as `[u8; 3]`, packed into one integer; the compiler unpacks
/// that for free, but the shim keeps the circuit as written anyway.)
#[cfg(all(xark, target_arch = "wasm32"))]
#[doc(hidden)]
pub struct Binder<const N: usize> {
    names: [Vec<String>; N],
    read: [usize; N],
}

#[cfg(all(xark, target_arch = "wasm32"))]
impl<const N: usize> Binder<N> {
    /// Hand the compiler the schema and work out every leaf name.
    #[inline(never)]
    pub fn new(circuit: &str, params: &[Param; N]) -> Binder<N> {
        crate::wasm::install_panic_hook();
        crate::wasm::record_schema(&schema_json(circuit, params));
        Binder {
            names: core::array::from_fn(|i| leaf_names(&params[i].2, params[i].0)),
            read: [0; N],
        }
    }

    /// Bind parameter `I`: every leaf of a `T`, in order.
    #[inline(always)]
    pub fn bind<const I: usize, T: Input>(&mut self, public: bool) -> T {
        let mut r = Reader {
            src: Source::Inputs {
                names: &self.names[I],
                public,
            },
            at: 0,
        };
        let v = T::read(&mut r);
        self.read[I] = r.at;
        v
    }

    /// Every parameter is bound: the compiler range-checks the `uN` inputs.
    #[inline(never)]
    pub fn inputs_done(&self) {
        crate::wasm::inputs_done();
    }

    /// After the body: check each `Input` impl read the leaves its `TYPE` names. Plain
    /// code, no compiler calls: the body may end inside a branch on a witness value,
    /// where those aren't allowed.
    #[inline(never)]
    pub fn finish(self, params: &[Param; N]) {
        for (i, (name, _, _)) in params.iter().enumerate() {
            assert!(
                self.read[i] == self.names[i].len(),
                "the `Input` impl of parameter `{name}` reads {} leaves, but its `TYPE` names {}",
                self.read[i],
                self.names[i].len()
            );
        }
    }
}

/// `value`'s `(leaf name, value)` pairs under `name`, for the prover.
#[cfg(not(xark))]
#[doc(hidden)]
pub fn leaves<T: Input>(value: &T, name: &str) -> Vec<(String, ark_bn254::Fr)> {
    let mut fields = alloc::vec![Field::zero(); T::LEN];
    let mut w = Writer::new(&mut fields);
    value.write(&mut w);
    assert!(
        w.at == T::LEN,
        "an `Input` impl writes a different number of leaves than its `TYPE` describes"
    );
    leaf_names(&T::TYPE, name)
        .into_iter()
        .zip(fields)
        .map(|(n, f)| (n, f.into()))
        .collect()
}

#[cfg(all(test, not(xark)))]
mod tests {
    use super::*;

    #[test]
    fn names_follow_the_layout() {
        const P: Named = Type::named(
            "P",
            Layout::Struct(&[
                Member::new("x", Type::Field),
                Member::new("t", <[(u8, Field); 2]>::TYPE),
            ]),
        );
        let ty = Type::Named(&P);
        assert_eq!(ty.leaves(), 5);
        assert_eq!(
            leaf_names(&ty, "p"),
            ["p.x", "p.t[0].0", "p.t[0].1", "p.t[1].0", "p.t[1].1"]
        );
        let s = schema_json("c", &[("p", true, ty), ("k", false, Type::Uint(64))]);
        assert_eq!(
            s,
            concat!(
                r#"{"version":2,"xark":""#,
                env!("CARGO_PKG_VERSION"),
                r#"","circuit":"c","inputs":[{"name":"p","visibility":"public","type":{"ref":"P"}},{"name":"k","visibility":"private","type":{"uint":64}}],"types":{"P":{"struct":[{"name":"x","type":"field"},{"name":"t","type":{"array":{"of":{"tuple":[{"uint":8},"field"]},"len":2}}}]}},"public_inputs":["p.x","p.t[0].0","p.t[0].1","p.t[1].0","p.t[1].1"]}"#
            )
        );
    }

    #[test]
    #[should_panic(expected = "`B` names two different types")]
    fn one_name_one_type() {
        const B3: Named = Type::named("B", Layout::Newtype(Type::Array(&Type::Field, 3)));
        const B4: Named = Type::named("B", Layout::Newtype(Type::Array(&Type::Field, 4)));
        let same = [("a", true, Type::Named(&B3)), ("b", true, Type::Named(&B3))];
        assert!(schema_json("c", &same).contains(r#""B":{"newtype""#));
        schema_json(
            "c",
            &[("a", true, Type::Named(&B3)), ("b", true, Type::Named(&B4))],
        );
    }

    #[test]
    fn values_round_trip() {
        let v: (u64, [Field; 2]) = (7, [Field::from(1u8), Field::from(2u8)]);
        let mut f = [Field::zero(); 3];
        write_fields(&v, &mut f);
        let back: (u64, [Field; 2]) = from_fields(&f);
        assert_eq!(back.0, 7);
        assert_eq!(back.1[1].to_decimal(), "2");
        assert_eq!(leaves(&v, "v")[0].0, "v.0");
    }
}
