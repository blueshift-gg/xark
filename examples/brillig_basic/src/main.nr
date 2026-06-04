// Exercises Noir's `BrilligCall` opcode (ROADMAP step WS-C.2).
//
// Field division emits a Brillig hint for `1/b` plus an `AssertZero`
// that pins the relationship `a == b * (1/b) * a`. See `docs/brillig.md`
// for the soundness argument behind xark's trust-outputs strategy.
fn main(a: Field, b: Field, out: pub Field) {
    assert(a / b == out);
}
