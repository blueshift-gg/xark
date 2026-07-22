//! Host-side (`cfg(not(xark))`) compile check for `#[circuit]` with native `uN` params.
//! The macro must generate a `<Fn>Inputs` struct whose fields take the native integer
//! (not a `String`), plus the `ProveInputs` fan-out — all of which must type-check in a
//! normal build. Constructing the struct here is the assertion; the driver-side lowering
//! is covered by the `native_u64_*` tests in `snapshot.rs`.

use xark::prelude::*;

#[circuit]
pub fn cmp(a: Private<u64>, b: Private<u64>, c: Public<u8>) {
    require(a < b);
    let _ = c;
}

#[test]
fn generated_inputs_struct_takes_native_ints() {
    // The generated `CmpInputs` mirrors the entry params with their native integer
    // types (u64/u8) — not `String`. Constructing it proves the host output
    // type-checks; `ProveInputs` (the decimal fan-out) is generated alongside.
    let inputs = CmpInputs {
        a: 42u64,
        b: 99u64,
        c: 3u8,
    };
    assert_eq!(inputs.a, 42);
}
