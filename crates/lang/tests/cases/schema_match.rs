// One circuit, read two ways by `input_derive.rs`: included in the host test (for
// `SchemaMatchInputs::schema()`) and built by the compiler (for `schema.json`).

/// A holder's standing.
#[input]
pub enum Standing {
    Retail,
    Accredited,
}

#[input]
pub struct Holder {
    pub doc: Text,
    pub born: Date,
    pub standing: Choice<Standing>,
    pub tags: [u8; 2],
    pub pair: (u64, Field),
}

#[circuit]
pub fn schema_match(
    h: Private<Holder>,
    allowed: Public<Bitfield<Country>>,
    home: Private<Choice<Country>>,
    min: Public<u32>,
    salt: Private<[Field; 2]>,
) {
    home.require_in(allowed);
    require(h.standing == Standing::Accredited);
    require(h.pair.0 >= min as u64);
    require_eq(h.doc, Text::new("x"));
    require_eq(h.born, h.born);
    require_eq(Field::from(h.tags[0]) + salt[0] + salt[1], h.pair.1);
}
