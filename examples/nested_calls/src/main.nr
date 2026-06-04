// Two-level nested cross-circuit Call. `main` calls `square_plus_one`
// (which itself calls `square`). Both helpers are marked `#[fold]` so
// Noir keeps them as separate ACIR functions and emits real
// `Opcode::Call` instructions, with the inner call appearing inside the
// outer callee's body. Exercises the nested-call branch of ROADMAP step
// WS-B.5.
fn main(x: Field, y: pub Field) {
    assert(square_plus_one(x) == y);
}

#[fold]
fn square_plus_one(x: Field) -> Field {
    square(x) + 1
}

#[fold]
fn square(x: Field) -> Field {
    x * x
}
