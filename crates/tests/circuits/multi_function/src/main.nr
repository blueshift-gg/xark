fn main(x: Field, y: pub Field) {
    assert(square(x) == y);
}

#[fold]
fn square(x: Field) -> Field {
    x * x
}
