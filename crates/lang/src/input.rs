//! Circuit inputs: the [`Input`] trait, and the [`Type`] vocabulary every client
//! language maps to its own types.
//!
//! A type is a circuit input when it implements [`Input`], usually through
//! `#[input]`:
//!
//! ```ignore
//! #[input]
//! pub struct Identity { pub born: Days<1900, 2100>, pub net_worth: u64, pub salt: Field }
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
//! | `Int(n)`                   | `i8` … `i128`     | a number, or a decimal string (`-` allowed)|
//! | `Bool`                     | `bool`            | `true` / `false` (or `1` / `0`)            |
//! | `Array(Uint(8), n)`        | `[u8; N]`         | `0x`-hex, or an array of numbers           |
//! | `Array`, `Tuple`           | `[T; N]`, `(A, B)`| an array                                   |
//! | named, [`Encoding::Fields`]| a struct          | an object of its fields                    |
//! | [`Encoding::Timestamp`]    | [`Timestamp`](crate::Timestamp) | `"YYYY-MM-DD"`, an ISO date-time, or Unix seconds |
//! | [`Encoding::Time`]         | [`Time`](crate::Time), [`Days`](crate::Days) | the same, in its range |
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
    /// A signed integer of this many bits: one field element holding its two's
    /// complement (`-1i8` is `255`), range-checked on entry as a `Uint` of that width.
    Int(u32),
    /// `true` or `false`: one field element, `0` or `1`, checked on entry.
    Bool,
    /// `N` values of one type, named `name[i]`.
    Array(&'static Type, usize),
    /// Values of different types, named `name.0`, `name.1`, …
    Tuple(&'static [Type]),
    /// A named type: a struct, or a standard type such as `Timestamp`.
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
    /// The leaves of one inner type, at the value's own name (`Timestamp` is one `Int(64)`).
    Newtype(Type),
    /// Named fields, each at `name.field`.
    Struct(&'static [Member]),
}

/// A struct field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Member {
    pub name: &'static str,
    pub ty: Type,
    /// Whether it may share a field element with its neighbours (see [`Pack`]).
    pub pack: bool,
}

/// How a client gives a value of a named type. Each is a standard type every
/// client language maps to one of its own.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Encoding {
    /// An object of its fields (a struct), or its inner type's form (a newtype).
    Fields,
    /// A moment, Unix seconds (an `Int(64)`): `"YYYY-MM-DD"`, an ISO 8601 date-time, or
    /// a number of seconds.
    Timestamp,
    /// A moment from the start of year `from` to the end of year `to`, in whole
    /// `unit`-second steps since the start (a `Uint`): given as a [`Encoding::Timestamp`]
    /// is, rounded down to its step.
    Time { unit: u32, from: u16, to: u16 },
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

    /// The width of a value of this type when it is packed ([`Pack`]), or `None` for
    /// one that isn't packable: an integer's width, 1 for a `bool`, enough bits for an
    /// enum's variants in a `Choice`, one per variant in a `Bitfield`, and a time's
    /// integer's. A `Field`, a `Text`, an array or a struct has its own leaves.
    pub const fn bits(&self) -> Option<u32> {
        match self {
            Type::Uint(n) | Type::Int(n) => Some(*n),
            Type::Bool => Some(1),
            Type::Named(n) => match (n.layout, n.encoding) {
                (Layout::Newtype(_), Encoding::Choice(v)) => {
                    let len = v.names.len();
                    Some(if len <= 2 {
                        1
                    } else {
                        usize::BITS - (len - 1).leading_zeros()
                    })
                }
                (Layout::Newtype(_), Encoding::Set(v)) if !v.names.is_empty() => {
                    Some(v.names.len() as u32)
                }
                (
                    Layout::Newtype(t),
                    Encoding::Fields | Encoding::Timestamp | Encoding::Time { .. },
                ) => t.bits(),
                _ => None,
            },
            _ => None,
        }
    }

    /// The number of leaves a value of this type takes.
    pub const fn leaves(&self) -> usize {
        match self {
            Type::Field | Type::Uint(_) | Type::Int(_) | Type::Bool => 1,
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
                    let p = pack_of(ms, i);
                    if !p.packed() {
                        n += ms[i].ty.leaves();
                    } else if p.offset == 0 {
                        n += 1;
                    }
                    i += 1;
                }
                n
            }
        }
    }
}

impl Member {
    /// A field with its own leaves.
    pub const fn new(name: &'static str, ty: Type) -> Member {
        Member {
            name,
            ty,
            pack: false,
        }
    }

    /// A field that shares a field element with its packable neighbours (see
    /// [`Pack`]): what `#[input]` makes of every field not marked `#[unpacked]`. An
    /// impl with packed members reads and writes them with [`Reader::member`] and
    /// [`Writer::member`].
    pub const fn packed(name: &'static str, ty: Type) -> Member {
        Member {
            name,
            ty,
            pack: true,
        }
    }
}

// ---- packing ------------------------------------------------------------------------

/// The most bits a packed field element holds: every value below `2^253` is a
/// distinct BN254 scalar, so a packed element splits back one way only.
pub const PACK_BITS: u32 = 253;

/// Where a struct field sits in its packed field element. `#[input]` packs a struct's
/// fields in declaration order: consecutive packable fields (each of known width:
/// [`Type::bits`]) share one field element, the first in its lowest bits, until the
/// next would take it past [`PACK_BITS`]. A field that isn't packable (a `Field`, a
/// `Text`, an array, a nested struct, or one marked `#[unpacked]`) has its own leaves
/// and starts a new run, and a field packed with no neighbour stays as it is.
///
/// In the circuit a packed element is split into its bits once, which is also each
/// field's range check; each field reads its own bits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Pack {
    /// The field's lowest bit in the element.
    pub offset: u32,
    /// The field's width.
    pub bits: u32,
    /// The element's width (0: the field isn't packed).
    pub total: u32,
    /// Whether the field is the element's last.
    pub last: bool,
    /// Whether a value written must be checked to fit its width (a `Choice` or
    /// `Bitfield`, one field element; an integer fits its width already).
    pub check: bool,
}

impl Pack {
    /// Not packed: its own leaves.
    pub const ALONE: Pack = Pack {
        offset: 0,
        bits: 0,
        total: 0,
        last: true,
        check: false,
    };

    /// Whether the field shares a packed element.
    pub const fn packed(&self) -> bool {
        self.total > 0
    }
}

const fn packable(m: &Member) -> Option<u32> {
    if m.pack { m.ty.bits() } else { None }
}

/// Where field `i` of a struct with these fields sits ([`Pack`]).
pub const fn pack_of(ms: &[Member], i: usize) -> Pack {
    let mut start = 0;
    while start < ms.len() {
        let w0 = match packable(&ms[start]) {
            Some(w) => w,
            None => {
                start += 1;
                continue;
            }
        };
        let (mut end, mut total) = (start + 1, w0);
        while end < ms.len() {
            match packable(&ms[end]) {
                Some(w) if total + w <= PACK_BITS => {
                    total += w;
                    end += 1;
                }
                _ => break,
            }
        }
        if i < start {
            break;
        }
        if i < end {
            if end - start == 1 {
                return Pack::ALONE;
            }
            let (mut offset, mut j) = (0, start);
            while j < i {
                offset += match packable(&ms[j]) {
                    Some(w) => w,
                    None => 0,
                };
                j += 1;
            }
            let check = matches!(
                ms[i].ty,
                Type::Named(Named {
                    encoding: Encoding::Choice(_) | Encoding::Set(_),
                    ..
                })
            );
            return Pack {
                offset,
                bits: match packable(&ms[i]) {
                    Some(w) => w,
                    None => 0,
                },
                total,
                last: i + 1 == end,
                check,
            };
        }
        start = end;
    }
    Pack::ALONE
}

/// Where each of a struct type's `N` fields sits ([`pack_of`]): what `#[input]`
/// reads and writes them by.
pub const fn pack_plan<const N: usize>(ty: Type) -> [Pack; N] {
    let mut plan = [Pack::ALONE; N];
    if let Type::Named(Named {
        layout: Layout::Struct(ms),
        encoding: Encoding::Fields,
        ..
    }) = ty
    {
        let mut i = 0;
        while i < N && i < ms.len() {
            plan[i] = pack_of(ms, i);
            i += 1;
        }
    }
    plan
}

/// `2^k` (`k < 256`).
const fn pow2(k: u32) -> Field {
    let mut b = [0u8; 32];
    b[(k / 8) as usize] = 1 << (k % 8);
    Field::from_le_bytes(&b)
}

/// The bits a packed value is made of, to read its fields off.
#[derive(Clone, Copy)]
struct Group {
    /// In the circuit: the element's bits (proven, so each field's range check).
    #[cfg(xark)]
    bits: [Field; 253],
    /// On the host: the element's value.
    #[cfg(not(xark))]
    limbs: [u64; 4],
}

impl Group {
    const EMPTY: Group = Group {
        #[cfg(xark)]
        bits: [Field::zero(); 253],
        #[cfg(not(xark))]
        limbs: [0; 4],
    };

    fn of(f: Field, total: u32) -> Group {
        #[cfg(xark)]
        return Group {
            bits: f.to_bits_n(total as usize),
        };
        #[cfg(not(xark))]
        {
            let limbs = f.to_limbs();
            assert!(
                fits(limbs, total),
                "a packed value past its {total} bits isn't one this type packs"
            );
            Group { limbs }
        }
    }

    /// The `bits` bits from `offset`, as a field element.
    fn slice(&self, offset: u32, bits: u32) -> Field {
        #[cfg(xark)]
        {
            let (mut acc, mut pow, mut j) = (Field::zero(), Field::from_u8(1), 0);
            while j < bits {
                acc = acc + self.bits[(offset + j) as usize] * pow;
                pow = pow + pow;
                j += 1;
            }
            acc
        }
        #[cfg(not(xark))]
        {
            let mut b = [0u8; 32];
            let mut j = 0;
            while j < bits {
                let k = offset + j;
                if self.limbs[(k / 64) as usize] >> (k % 64) & 1 == 1 {
                    b[(j / 8) as usize] |= 1 << (j % 8);
                }
                j += 1;
            }
            Field::from_le_bytes(&b)
        }
    }
}

/// Whether a value's limbs fit `bits` bits.
#[cfg(not(xark))]
fn fits(limbs: [u64; 4], bits: u32) -> bool {
    (0..256u32).all(|k| k < bits || limbs[(k / 64) as usize] >> (k % 64) & 1 == 0)
}

// ---- reading and writing ----------------------------------------------------------

/// Reads a value's field elements in order: the circuit's inputs (in a circuit
/// build), or known values (on the host). See [`Input::read`].
pub struct Reader<'a> {
    src: Source<'a>,
    at: usize,
    /// The packed element being read, and the next field's bits in it.
    group: Group,
    slot: Option<(u32, u32)>,
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
            group: Group::EMPTY,
            slot: None,
        }
    }

    /// The next value.
    pub fn read<T: Input>(&mut self) -> T {
        T::read(self)
    }

    /// The next struct field, packed as `p` says ([`pack_plan`]): from its bits in a
    /// packed element (the first field of one reads the element), or its own leaves.
    pub fn member<T: Input>(&mut self, p: Pack) -> T {
        if !p.packed() {
            return T::read(self);
        }
        if p.offset == 0 {
            let f = self.field();
            self.group = Group::of(f, p.total);
        }
        self.slot = Some((p.offset, p.bits));
        let v = T::read(self);
        assert!(
            self.slot.is_none(),
            "a packed field's `Input` impl reads no leaf"
        );
        v
    }

    /// The packed field being read, if one is: its bits, as a field element.
    fn packed(&mut self) -> Option<(Field, u32)> {
        let (offset, bits) = self.slot.take()?;
        Some((self.group.slice(offset, bits), bits))
    }

    /// The next leaf, a field element.
    pub fn field(&mut self) -> Field {
        if let Some((f, _)) = self.packed() {
            return f;
        }
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
        if let Some((f, w)) = self.packed() {
            debug_assert!(w <= bits);
            return field_to_uint(f, w);
        }
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
        if let Some((f, _)) = self.packed() {
            #[cfg(all(xark, target_arch = "wasm32"))]
            return crate::wasm::field_to_bool(f);
            #[cfg(not(all(xark, target_arch = "wasm32")))]
            return !f.is_zero();
        }
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
        if let Some((offset, bits)) = self.slot.take() {
            let lo = self.group.slice(offset, bits.min(64));
            let hi = self.group.slice(offset + 64, bits.saturating_sub(64));
            return (field_to_uint(hi, bits.saturating_sub(64)) as u128) << 64
                | field_to_uint(lo, bits.min(64)) as u128;
        }
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

/// A field element known to fit `bits ≤ 64` bits (a packed field's slice) as an
/// integer: in the circuit the same wire, at that width.
fn field_to_uint(f: Field, bits: u32) -> u64 {
    #[cfg(all(xark, target_arch = "wasm32"))]
    return crate::wasm::field_to_uint(f, bits);
    #[cfg(not(all(xark, target_arch = "wasm32")))]
    {
        let _ = bits;
        f.to_limbs()[0]
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
    /// The packed element being written.
    acc: Field,
}

impl<'a> Writer<'a> {
    /// A writer filling `out` (`Input::LEN` long).
    pub fn new(out: &'a mut [Field]) -> Writer<'a> {
        Writer {
            out,
            at: 0,
            acc: Field::zero(),
        }
    }

    /// Write `value`'s field elements.
    pub fn write<T: Input>(&mut self, value: &T) {
        value.write(self)
    }

    /// Write a struct field, packed as `p` says ([`pack_plan`]): into its bits of a
    /// packed element (written out after its last field), or as its own leaves.
    pub fn member<T: Input>(&mut self, p: Pack, value: &T) {
        if !p.packed() {
            return value.write(self);
        }
        let mut one = [Field::zero()];
        let mut w = Writer::new(&mut one);
        value.write(&mut w);
        assert!(w.at == 1, "a packed field's `Input` impl writes one leaf");
        let f = one[0];
        // An integer's value fits its width already; a `Choice` or `Bitfield` (a field
        // element) is checked, which is free for one read off a packed element.
        #[cfg(xark)]
        if p.check {
            let _ = f.to_bits_n(p.bits as usize);
        }
        #[cfg(not(xark))]
        assert!(
            fits(f.to_limbs(), p.bits),
            "a value past its {} bits can't be packed",
            p.bits
        );
        if p.offset == 0 {
            self.acc = Field::zero();
        }
        self.acc += f * pow2(p.offset);
        if p.last {
            let acc = self.acc;
            self.field(acc);
        }
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

// A signed integer is its two's complement bits: bound and range-checked as the
// unsigned integer of its width, which is what the circuit's registers hold anyway.
macro_rules! int_input {
    ($($t:ty, $u:ty => $w:literal),*) => {$(
        impl Input for $t {
            const TYPE: Type = Type::Int($w);
            fn read(r: &mut Reader<'_>) -> Self {
                r.uint($w) as $u as $t
            }
            fn write(&self, w: &mut Writer<'_>) {
                w.field(Field::from(*self as $u))
            }
        }
    )*};
}
int_input!(i8, u8 => 8, i16, u16 => 16, i32, u32 => 32, i64, u64 => 64);

impl Input for i128 {
    const TYPE: Type = Type::Int(128);
    fn read(r: &mut Reader<'_>) -> Self {
        r.u128() as i128
    }
    fn write(&self, w: &mut Writer<'_>) {
        w.field(Field::from(*self as u128))
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
        Type::Field | Type::Uint(_) | Type::Int(_) | Type::Bool => out.push(name.clone()),
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
                for (i, m) in ms.iter().enumerate() {
                    let p = pack_of(ms, i);
                    if !p.packed() {
                        name.push('.');
                        name.push_str(m.name);
                        names_into(&m.ty, name, out);
                        name.truncate(at);
                    } else if p.offset == 0 {
                        // A packed element: named by its fields, `id.{born,net_worth}`.
                        name.push_str(".{");
                        let mut j = i;
                        loop {
                            name.push_str(ms[j].name);
                            if pack_of(ms, j).last {
                                break;
                            }
                            name.push(',');
                            j += 1;
                        }
                        name.push('}');
                        out.push(name.clone());
                        name.truncate(at);
                    }
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
///  "types": {"Identity": {"struct": [{"name": "born", "type": {"ref": "Days<1900,2100>"}}, …]},
///            "Days<1900,2100>": {"newtype": {"uint": 17},
///                                "encoding": {"time": {"unit": 86400, "from": 1900, "to": 2100}}},
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

/// A named type's name in `schema.json`: `Identity`, `Bitfield<Country>`,
/// `Days<1900,2100>` (a `Time` is named by its parameters, so two ranges are two
/// types).
pub fn type_name(n: &Named) -> String {
    if let Encoding::Time { unit, from, to } = n.encoding {
        return if unit == crate::time::DAY {
            alloc::format!("Days<{from},{to}>")
        } else {
            alloc::format!("Time<{unit},{from},{to}>")
        };
    }
    let mut s = String::from(n.name);
    if let Some(a) = n.arg {
        s.push('<');
        s.push_str(a);
        s.push('>');
    }
    s
}

/// A piece of an exported function's description (what `#[input]` on an `impl`
/// writes to `client.wasm`'s `xark.exports` section): text, or a type written as
/// its name, the way a client generator reads it (`Days<1900,2100>`, `[u8;32]`,
/// `(u64,Field)`). From the type itself, so an alias of it is followed.
#[doc(hidden)]
pub enum Describe {
    Text(&'static str),
    Type(Type),
}

/// The length of [`describe`]'s bytes.
#[doc(hidden)]
pub const fn describe_len(parts: &[Describe]) -> usize {
    describe_into(parts, &mut [])
}

/// `parts` as bytes, `N` ([`describe_len`]) of them.
#[doc(hidden)]
pub const fn describe<const N: usize>(parts: &[Describe]) -> [u8; N] {
    let mut out = [0; N];
    assert!(describe_into(parts, &mut out) == N);
    out
}

/// Write `parts` to `out` as far as it reaches; the length they take.
const fn describe_into(parts: &[Describe], out: &mut [u8]) -> usize {
    let (mut at, mut i) = (0, 0);
    while i < parts.len() {
        at = match &parts[i] {
            Describe::Text(t) => put(out, at, t),
            Describe::Type(t) => put_type(out, at, t),
        };
        i += 1;
    }
    at
}

const fn put(out: &mut [u8], mut at: usize, s: &str) -> usize {
    let s = s.as_bytes();
    let mut i = 0;
    while i < s.len() {
        if at < out.len() {
            out[at] = s[i];
        }
        at += 1;
        i += 1;
    }
    at
}

const fn put_num(out: &mut [u8], at: usize, n: usize) -> usize {
    let at = if n >= 10 {
        put_num(out, at, n / 10)
    } else {
        at
    };
    if at < out.len() {
        out[at] = b'0' + (n % 10) as u8;
    }
    at + 1
}

/// `t`'s name, as [`type_name`] writes a named one.
const fn put_type(out: &mut [u8], at: usize, t: &Type) -> usize {
    match t {
        Type::Field => put(out, at, "Field"),
        Type::Bool => put(out, at, "bool"),
        Type::Uint(n) => {
            let at = put(out, at, "u");
            put_num(out, at, *n as usize)
        }
        Type::Int(n) => {
            let at = put(out, at, "i");
            put_num(out, at, *n as usize)
        }
        Type::Array(of, n) => {
            let at = put(out, at, "[");
            let at = put_type(out, at, of);
            let at = put(out, at, ";");
            let at = put_num(out, at, *n);
            put(out, at, "]")
        }
        Type::Tuple(ts) => {
            let mut at = put(out, at, "(");
            let mut i = 0;
            while i < ts.len() {
                if i > 0 {
                    at = put(out, at, ",");
                }
                at = put_type(out, at, &ts[i]);
                i += 1;
            }
            put(out, at, ")")
        }
        Type::Named(n) => match n.encoding {
            Encoding::Time { unit, from, to } => {
                let mut at = if unit == crate::time::DAY {
                    put(out, at, "Days<")
                } else {
                    let at = put(out, at, "Time<");
                    let at = put_num(out, at, unit as usize);
                    put(out, at, ",")
                };
                at = put_num(out, at, from as usize);
                at = put(out, at, ",");
                at = put_num(out, at, to as usize);
                put(out, at, ">")
            }
            _ => {
                let at = put(out, at, n.name);
                match n.arg {
                    Some(a) => {
                        let at = put(out, at, "<");
                        let at = put(out, at, a);
                        put(out, at, ">")
                    }
                    None => at,
                }
            }
        },
    }
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
        Type::Int(w) => {
            s.push_str("{\"int\":");
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
            let packing = n.encoding == Encoding::Fields;
            for (i, m) in ms.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                s.push_str("{\"name\":");
                push_str_json(&mut s, m.name);
                s.push_str(",\"type\":");
                type_json(&m.ty, defs, &mut s);
                let p = pack_of(ms, i);
                if packing && p.packed() {
                    // Its bits in the packed element it shares (offset 0 starts one).
                    s.push_str(",\"packed\":{\"offset\":");
                    push_usize(&mut s, p.offset as usize);
                    s.push_str(",\"bits\":");
                    push_usize(&mut s, p.bits as usize);
                    s.push('}');
                }
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
        Encoding::Timestamp => s.push_str("{\"timestamp\":\"unix\"}"),
        Encoding::Time { unit, from, to } => {
            s.push_str("{\"time\":{\"unit\":");
            push_usize(s, unit as usize);
            s.push_str(",\"from\":");
            push_usize(s, from as usize);
            s.push_str(",\"to\":");
            push_usize(s, to as usize);
            s.push_str("}}");
        }
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
            group: Group::EMPTY,
            slot: None,
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
    fn exports_name_types_as_the_schema_does() {
        use crate::time::MINUTE;
        use crate::{Bitfield, Choice, Country, Days, Text, Time, Timestamp};
        fn name<T: Input>() -> String {
            const MAX: usize = 64;
            let parts = [Describe::Type(T::TYPE)];
            let mut out = [0u8; MAX];
            let n = describe_into(&parts, &mut out);
            assert_eq!(n, describe_len(&parts));
            String::from_utf8(out[..n].to_vec()).unwrap()
        }
        fn named<T: Input>() -> String {
            let Type::Named(n) = T::TYPE else { panic!() };
            type_name(n)
        }
        assert_eq!(name::<Field>(), "Field");
        assert_eq!(name::<[u8; 32]>(), "[u8;32]");
        assert_eq!(name::<(u64, i8, bool)>(), "(u64,i8,bool)");
        assert_eq!(name::<[(u16, Field); 3]>(), "[(u16,Field);3]");
        assert_eq!(name::<Days<1900, 2100>>(), "Days<1900,2100>");
        assert_eq!(name::<Time<MINUTE, 2020, 2060>>(), "Time<60,2020,2060>");
        assert_eq!(name::<Timestamp>(), "Timestamp");
        assert_eq!(name::<Bitfield<Country>>(), "Bitfield<Country>");
        for (a, b) in [
            (name::<Days<1900, 2100>>(), named::<Days<1900, 2100>>()),
            (
                name::<Time<MINUTE, 2020, 2060>>(),
                named::<Time<MINUTE, 2020, 2060>>(),
            ),
            (name::<Timestamp>(), named::<Timestamp>()),
            (name::<Text>(), named::<Text>()),
            (name::<Choice<Country>>(), named::<Choice<Country>>()),
            (name::<Bitfield<Country>>(), named::<Bitfield<Country>>()),
        ] {
            assert_eq!(a, b);
        }
        // Built at compile time.
        const PARTS: [Describe; 3] = [
            Describe::Text("{\"type\":\""),
            Describe::Type(<Days<1900, 2100> as Input>::TYPE),
            Describe::Text("\"}"),
        ];
        const BYTES: [u8; describe_len(&PARTS)] = describe(&PARTS);
        assert_eq!(&BYTES, br#"{"type":"Days<1900,2100>"}"#);
    }

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
