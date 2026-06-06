// Exercises constant-index ACIR memory ops (ROADMAP step WS-C.4,
// design note in `docs/memory.md`).
//
// Using mutable array writes after initialization forces Noir to emit
// `MemoryInit` and `MemoryOp[write]`/`MemoryOp[read]` opcodes instead of
// constant-folding the whole array.
fn main(x: Field, y: pub Field) {
    let mut arr: [Field; 3] = [0, 0, 0];
    arr[0] = x;
    arr[1] = x * 2;
    arr[2] = x * 3;
    assert(arr[0] + arr[1] + arr[2] == y);
}
