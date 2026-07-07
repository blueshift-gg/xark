#![no_std]

use xark::{assert_eq, Field, Private, Public};

// memory_var: a dynamic `arr[idx]` read. xark has no runtime
// memory, so the variable-index read is modelled as a 4-way select/mux over
// `arr` driven by a one-hot witness selector: exactly one `sel_i` is 1, and the
// output is `Σ sel_i · arr_i`, constrained equal to the public `y`.
pub fn circuit(
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
    assert_eq(sel0 * sel0, sel0);
    assert_eq(sel1 * sel1, sel1);
    assert_eq(sel2 * sel2, sel2);
    assert_eq(sel3 * sel3, sel3);
    // One-hot: exactly one selector is set.
    assert_eq(sel0 + sel1 + sel2 + sel3, Field::constant("1"));
    // Selected element = Σ sel_i · arr_i.
    let selected = sel0 * arr0 + sel1 * arr1 + sel2 * arr2 + sel3 * arr3;
    assert_eq(selected, y);
}
