use xark::prelude::*;

// all-Field, called many times → gadget by default, UNLESS the user opts out.
#[inline(never)]
fn sq(x: Field) -> Field {
    x * x
}

#[circuit]
pub fn optout(inp: Private<[u8; 8]>, out: Public<Field>) {
    let mut acc = inp[0];
    let mut i = 1;
    while i < 8 {
        acc = sq(acc) + inp[i];
        i += 1;
    }
    require_eq(acc, out);
}

#[cfg(test)]
mod tests {
    use super::optout;

    #[test]
    fn accepts_valid() {
        optout(
            [1, 2, 3, 4, 5, 6, 7, 8],
            "53086056457022411804685755744397384".into(),
        )
        .unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(optout([1, 2, 3, 4, 5, 6, 7, 8], "1".into()).is_err());
    }
}
