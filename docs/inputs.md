# Inputs

How a circuit's parameters map to field elements, and the input types xark ships.

Every circuit parameter's type implements `xark::Input`, which says how its value
maps to field elements and how clients see it. Group inputs into structs with
`#[input]` (which also derives `Clone`, `Copy` and `Debug` unless the type lists
them; `#[input(no_derive)]` for a type with its own), including gadget types:
`examples/grumpkin_ivc` takes a few
`Instance { cw, ce, u, x }` values instead of twenty separate parameters, and
`to_fields()` hashes one in a single call. The generated `<Fn>Inputs` struct
holds the same values for `xark::prover::circuit(..).check(..)`, `.prove(..)`
and friends; a proof's `to_instruction_data()` is the bytes an exported Solana
verifier reads. Its `to_json()` is the values as `xark prove --inputs` takes them,
named as declared (`net_worth`) like `inputs.example.json`; `--inputs` also takes
the camelCase names a TypeScript client uses (`netWorth`). A circuit crate needs only the `xark` dependency.

## Everyday input types

`xark` ships the types most credential-style circuits need, each one field wide
and each with its natural form in tests, `--inputs` and the TypeScript client:

- `Days<FROM, TO>`: a day from the start of year `FROM` to the end of `TO` (UTC),
  in the circuit its day count, just wide enough for the range
  (`Days<1900, 2100>` is 17 bits). It's `"1990-01-01"` in Rust and `--inputs` and a
  JS `Date` in TypeScript, and any moment of a day is that day. `Time<UNIT, FROM, TO>`
  is the same in other steps (`Time<MINUTE, 2020, 2060>`).
- `Timestamp`: any moment, as Unix seconds (an `i64`, as Solana's `Clock` and a JS
  `Date` hold it), compared as a signed 64-bit integer.
- `Text`: a short string, up to 31 bytes (a document number, a name).
- `Choice<E>` and `Bitfield<E>`: one variant of an enum, or a set of them, such
  as a nationality and the allowed countries: `choice == Country::US`,
  `require_in`, `require_one_of`, `contains`. Any fieldless enum with `#[input]` works;
  `xark` ships ISO 3166 `Country`.

An `#[input]` struct's narrow fields are packed: consecutive integers, flags, days
and enum values share one field element (up to 253 bits) in declaration order, so
`Identity` below is 3 leaves and `Policy` 2 public inputs. Keep narrow fields
together, and mark a field `#[unpacked]` to give it its own leaf.

```rust
#[input]
pub struct Identity { document: Text, born: Days<1900, 2100>, nationality: Choice<Country>, net_worth: u64, expires: Days<1900, 2100>, salt: Field }

/// A verifier's rules, a public input: one circuit serves every policy.
#[input]
pub struct Policy { today: Days<1900, 2100>, born_by: Days<1900, 2100>, min_net_worth: u64, allowed: Bitfield<Country> }

#[circuit]
fn zkyc(id: Private<Identity>, commitment: Public<Field>, policy: Public<Policy>) {
    require_eq(id.commitment(), commitment);
    require(id.born <= policy.born_by);
    require(id.net_worth >= policy.min_net_worth);
    require(id.expires >= policy.today);
    id.nationality.require_in(policy.allowed);
}

// In a test:
// let policy = Policy::default().on("2026-10-20").min_age(18).worth_at_least(500_000).nationalities([US, GB, FR, DE]);
// zkyc(id, id.commitment(), policy)
```

`examples/zkyc` is this circuit in full. A `bool` input works too: one field
element, checked to be 0 or 1.

A type `#[input]` doesn't cover implements `Input` by hand, in one impl that
serves the circuit and the host alike:

```rust
impl Input for Hash {
    const TYPE: Type = Type::Named(
        &Type::named("Hash", Layout::fields(&[Member::new("hi", Type::Field), Member::new("lo", Type::Field)]))
            .encoded(Encoding::Bytes(Bytes::Split(&[16, 16]))), // clients give its 32 bytes
    );
    fn read(r: &mut Reader) -> Self { Hash { hi: r.field(), lo: r.field() } }
    fn write(&self, w: &mut Writer) { w.field(self.hi); w.field(self.lo) }
}
```

A `TYPE` is built from the standard types (field, `uN`, bytes, number, date,
text, choice, set, arrays, tuples, structs), and those are what client
generators map: adding a language means mapping that fixed list, never a
circuit's own types.
