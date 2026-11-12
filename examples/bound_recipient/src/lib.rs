use xark::{Address, Field, Private, Public, bind, circuit, require_eq};

/// `recipient` is in no constraint: only the verifier supplies it. `bind` keeps the
/// proof to the recipient it was made for.
///
/// An `Address` is two field elements, its first and last 16 bytes, each big-endian,
/// so no address is reduced mod p (one `Field` would reduce most of them, and the
/// program would have to reduce its own the same way). A client gives it in base58;
/// an exported verifier's `PublicInputs` takes its `[u8; 32]` and splits it.
#[circuit]
pub fn bound_recipient(x: Private<Field>, y: Public<Field>, recipient: Public<Address>) {
    require_eq(x * x, y);
    bind(recipient);
}

#[cfg(test)]
mod tests {
    use super::bound_recipient;

    #[test]
    fn any_recipient_proves() {
        bound_recipient(3, 9, [0xff; 32]).unwrap();
        bound_recipient(3, 9, "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA").unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(bound_recipient(3, 10, [7; 32]).is_err());
    }
}
