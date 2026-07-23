use xark::prelude::*;

/// Decompose a private `x` into 8 bits and expose two of them publicly.
#[circuit]
pub fn bit_decompose(x: Private<Field>, bit0: Public<Field>, bit7: Public<Field>) {
    let bits = x.to_bits::<8>();
    require_eq(bits[0], bit0);
    require_eq(bits[7], bit7);
}

#[cfg(test)]
mod tests {
    use super::bit_decompose;

    #[test]
    fn accepts_valid() {
        // 129 = 0b1000_0001 → bit0=1, bit7=1
        bit_decompose("129".into(), "1".into(), "1".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(bit_decompose("129".into(), "0".into(), "1".into()).is_err());
    }
}
