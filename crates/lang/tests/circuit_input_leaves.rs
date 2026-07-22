//! `#[derive(CircuitInput)]` generates the host-side `NativeInput` fan-out directly:
//! `Native = Self` (the `Field`-composed struct, built host-side with `Field` values),
//! and `leaves` renders each field to a decimal under the compiler's structural-flatten
//! names — no parallel `String` mirror. These tests pin the generated leaf names, order,
//! and decimal values, which must match the compiler's input-var order exactly.

use xark::{CircuitInput, Field};
use xark_prover::NativeInput;

/// Scalars + a fixed array — `Field`s (host-built) rendered to decimals, `<prefix>.f[i]`
/// for array elements.
#[derive(CircuitInput)]
struct Account {
    id: Field,
    tags: [Field; 3],
    balance: Field,
}

#[test]
fn circuit_input_leaves_are_decimals_in_flatten_order() {
    let acct = Account {
        id: Field::from(7u64),
        tags: [Field::from(10u64), Field::from(11u64), Field::from(12u64)],
        balance: Field::from(999u64),
    };
    let leaves = <Account as NativeInput>::leaves(&acct, "user");
    assert_eq!(
        leaves,
        vec![
            ("user.id".to_string(), "7".to_string()),
            ("user.tags[0]".to_string(), "10".to_string()),
            ("user.tags[1]".to_string(), "11".to_string()),
            ("user.tags[2]".to_string(), "12".to_string()),
            ("user.balance".to_string(), "999".to_string()),
        ]
    );
}

#[test]
fn circuit_input_leaf_count_matches_flatten_arity() {
    // `From<Account> for [Field; 5]` (id + 3 tags + balance) — the leaf fan-out and the
    // flatten agree on the count leaf-for-leaf.
    let flat: [Field; 5] = Account {
        id: Field::from(0u8),
        tags: [Field::from(0u8); 3],
        balance: Field::from(0u8),
    }
    .into();
    let acct = Account {
        id: Field::from(1u64),
        tags: [Field::from(2u64); 3],
        balance: Field::from(3u64),
    };
    assert_eq!(
        <Account as NativeInput>::leaves(&acct, "x").len(),
        flat.len()
    );
}
