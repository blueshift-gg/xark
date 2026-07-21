#![cfg_attr(xark, no_std)]

use xark::{circuit, require_eq, Field, Private, Public};

// memory_var: a dynamic `arr[idx]` read. xark has no runtime
// memory, so the variable-index read is modelled as a 4-way select/mux over
// `arr` driven by a one-hot witness selector: exactly one `sel_i` is 1, and the
// output is `Σ sel_i · arr_i`, constrained equal to the public `y`.
#[circuit]
pub fn memory_var(
    arr0: Private<Field>,
    arr1: Private<Field>,
    arr2: Private<Field>,
    arr3: Private<Field>,
    sel0: Private<Field>,
    sel1: Private<Field>,
    sel2: Private<Field>,
    sel3: Private<Field>,
    y: Public<Field>,
) {
    // Each selector bit is boolean: sel_i * sel_i == sel_i.
    require_eq(sel0 * sel0, sel0);
    require_eq(sel1 * sel1, sel1);
    require_eq(sel2 * sel2, sel2);
    require_eq(sel3 * sel3, sel3);
    // One-hot: exactly one selector is set.
    require_eq(sel0 + sel1 + sel2 + sel3, Field::constant("1"));
    // Selected element = Σ sel_i · arr_i.
    let selected = sel0 * arr0 + sel1 * arr1 + sel2 * arr2 + sel3 * arr3;
    require_eq(selected, y);
}

#[cfg(test)]
mod tests {
    use super::memory_var;

    #[test]
    fn accepts_valid() {
        // one-hot sel1 → arr[1] = 20
        memory_var(
            "10".into(),
            "20".into(),
            "30".into(),
            "40".into(),
            "0".into(),
            "1".into(),
            "0".into(),
            "0".into(),
            "20".into(),
        )
        .unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(memory_var(
            "10".into(),
            "20".into(),
            "30".into(),
            "40".into(),
            "0".into(),
            "1".into(),
            "0".into(),
            "0".into(),
            "21".into()
        )
        .is_err());
    }
}
