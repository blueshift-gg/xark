//! Spend a nullifier once: insert it into an indexed Merkle tree, proving it
//! wasn't there. A program keeps only the tree's root and its next free slot; the
//! proof moves the root from `old_root` to `new_root` with `nullifier` added at
//! slot `index`, and fails for a nullifier already in the tree. The paths are
//! private, so the proof doesn't say which leaf it rewrote.
use xark_merkle::poseidon2::prelude::*;

/// The tree's depth: 2^4 slots, the first the list's head.
pub const DEPTH: usize = 4;

/// Nullifiers here are 64-bit integers. Up to 252 bits work the same way; 64 keeps
/// the comparisons to 64-bit range checks.
pub const BITS: usize = 64;

/// A slot's authentication path: its sibling at each height and its index's bits,
/// both leaf level first. (`indexed_insert` constrains each bit to 0 or 1.)
#[input]
pub struct Path {
    pub siblings: [Field; 4],
    pub index_bits: [Field; 4],
}

#[circuit]
pub fn nullifier_tree(
    low: Private<IndexedLeaf>,
    low_path: Private<Path>,
    new_path: Private<Path>,
    old_root: Public<Field>,
    new_root: Public<Field>,
    nullifier: Public<Field>,
    index: Public<Field>,
) {
    // The program's next free slot is where the nullifier goes.
    require_eq(Field::from_bits(new_path.index_bits), index);
    let root = indexed_insert::<DEPTH, BITS>(
        old_root,
        nullifier,
        low,
        low_path.siblings,
        low_path.index_bits,
        new_path.siblings,
        new_path.index_bits,
    );
    require_eq(root, new_root);
}

#[cfg(test)]
mod tests {
    use super::*;
    use xark_merkle::tree::{IndexedTree, Insertion};

    fn path(p: xark_merkle::tree::Path<DEPTH>) -> Path {
        Path {
            siblings: p.siblings,
            index_bits: p.index_bits(),
        }
    }

    fn spend(ins: &Insertion<DEPTH>, index: u64) -> Result<(), xark::prover::ProveError> {
        nullifier_tree(
            ins.low,
            path(ins.low_path),
            path(ins.new_path),
            ins.old_root,
            ins.new_root,
            ins.value,
            Field::from(index),
        )
    }

    #[test]
    fn each_nullifier_spends_once() {
        let mut tree = IndexedTree::<DEPTH>::new();
        for n in [30u64, 10, 20, u64::MAX] {
            let ins = tree.insert(Field::from(n)).unwrap();
            spend(&ins, ins.new_path.index as u64).unwrap();
        }
        // Spent already: the tree has no low leaf for it.
        assert!(tree.non_membership(Field::from(20u64)).is_none());
    }

    #[test]
    fn a_proof_holds_only_for_its_nullifier_and_slot() {
        let mut tree = IndexedTree::<DEPTH>::new();
        tree.insert(Field::from(10u64)).unwrap();
        let ins = tree.insert(Field::from(20u64)).unwrap();
        spend(&ins, 2).unwrap();
        assert!(spend(&ins, 3).is_err());
        let other = Insertion {
            value: Field::from(21u64),
            ..ins
        };
        assert!(spend(&other, 2).is_err());
        // Spending 10 again, through the head.
        let again = Insertion {
            value: Field::from(10u64),
            ..ins
        };
        assert!(spend(&again, 2).is_err());
    }
}
