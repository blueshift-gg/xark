// Variable-index read. Noir's SSA optimizer keeps the array as memory
// when the index isn't a compile-time constant.
fn main(arr: [Field; 4], idx: Field, y: pub Field) {
    let mut mutable = arr;
    // Force a write at constant index so the array stays in memory:
    mutable[0] = arr[0];
    assert(mutable[idx as u32] == y);
}
