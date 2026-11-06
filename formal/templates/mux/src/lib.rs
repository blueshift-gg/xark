use xark::{Field, Private, circuit};

/// `xark_ed25519::mux` on fresh inputs.
#[circuit]
pub fn mux(s: Private<Field>, a: Private<[[Field; 8]; 3]>, b: Private<[[Field; 8]; 3]>) {
    let _ = xark_ed25519::mux(s, a, b);
}
