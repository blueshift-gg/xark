//! The payoff of `xark`'s `native` feature: the *exact same* Poseidon2 gadget
//! source that the compiler lowers to R1CS also runs as ordinary Rust on the
//! host. A wallet computes the same hash the circuit does — no hand-mirrored
//! copy, no drift. Run with `--features native`.
#![cfg(feature = "native")]

use xark::Field;

/// `poseidon2_perm([1, 2, 3])` evaluated natively must equal the circuit gadget's
/// known-answer vector (from `tests/vec.rs`, the canonical Horizen Labs bn256
/// constants). Same source, same value — in-circuit and on-host.
#[test]
fn native_permutation_matches_circuit_kat() {
    let out = xark_poseidon2::poseidon2_perm([
        Field::from(1u64),
        Field::from(2u64),
        Field::from(3u64),
    ]);
    assert_eq!(
        out[0].to_decimal(),
        "4737982494702600552753609419126955242994596445692557044681458296415162795880"
    );
    assert_eq!(
        out[1].to_decimal(),
        "9698155156890762076414037574068404457164720954413259397447872502075783415658"
    );
    assert_eq!(
        out[2].to_decimal(),
        "18259628997120261506554896720810362547891614655348127750921457211768261324825"
    );
}

/// `hash2` (the 2-to-1 compression a Merkle tree / commitment uses) natively
/// equals `zeros[1] = hash2(0, 0)` — the value the shielded-pool circuit and its
/// on-chain empty root are built from.
#[test]
fn native_hash2_matches_zero_subtree() {
    let h = xark_poseidon2::hash2(Field::from(0u64), Field::from(0u64));
    assert_eq!(
        h.to_decimal(),
        "21177166670744647784289648293577786481357446166129397094207318338605633126018"
    );
}
