use xark::{Field, Private, Public, bind, circuit, require_eq};

/// `recipient` is in no constraint: only the verifier supplies it. `bind` keeps the
/// proof to the recipient it was made for.
#[circuit]
pub fn bound_recipient(x: Private<Field>, y: Public<Field>, recipient: Public<Field>) {
    require_eq(x * x, y);
    bind(recipient);
}

#[cfg(test)]
mod tests {
    use super::bound_recipient;

    #[test]
    fn any_recipient_proves() {
        bound_recipient(3, 9, 5).unwrap();
        bound_recipient(3, 9, 0).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(bound_recipient(3, 10, 5).is_err());
    }
}
