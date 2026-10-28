use xark::{Field, Private, Public, bind, circuit, require_eq};

/// `recipient` is in no constraint: only the verifier supplies it. `bind` keeps the
/// proof to the recipient it was made for.
///
/// A 32-byte address is two field elements, its first and last 16 bytes, each
/// big-endian: `Field::from_be_bytes(&key[..16])` and `Field::from_be_bytes(&key[16..])`.
/// As public inputs to the verifier, each half is zero-padded on the left to 32
/// bytes, so the address goes in unchanged. (One `Field` would be reduced mod p,
/// which most addresses are larger than, and the program would have to reduce
/// it the same way.)
#[circuit]
pub fn bound_recipient(x: Private<Field>, y: Public<Field>, recipient: Public<[Field; 2]>) {
    require_eq(x * x, y);
    bind(recipient);
}

#[cfg(test)]
mod tests {
    use super::bound_recipient;
    use xark::Field;

    fn halves(key: [u8; 32]) -> [Field; 2] {
        [
            Field::from_be_bytes(&key[..16]),
            Field::from_be_bytes(&key[16..]),
        ]
    }

    #[test]
    fn any_recipient_proves() {
        bound_recipient(3, 9, halves([0xff; 32])).unwrap();
        bound_recipient(3, 9, halves([0; 32])).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(bound_recipient(3, 10, halves([7; 32])).is_err());
    }
}
