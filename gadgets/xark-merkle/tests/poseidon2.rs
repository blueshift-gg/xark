//! The Poseidon2 trees (`xark_merkle::poseidon2`) and their host builders
//! (`xark_merkle::tree`).
//!
//! * Known answers: roots `merkle_ref.py` computes from the Python Poseidon2, with
//!   no Rust in the loop, and a dense tree hashed over `ark_bn254::Fr`.
//! * Round trips: every path the builders give folds, in the compiled circuits, to
//!   the builder's root; every insertion they give proves.
//! * Rejections: a wrong sibling, a flipped or non-boolean index bit, an append
//!   over a written slot, a present value claimed absent, a low leaf whose range
//!   misses the value; and in the honest witness each derived value tampered.
//! * Soundness: at depth 2 an exhaustive witness search finds exactly one witness
//!   for honest inputs and none for the forgeries.
//! * Cost: the constraint counts at depth 20.
//!
//! On the host `xark::Field` is the field itself, so the circuit functions run
//! natively too: the builders' tests call them directly.

use std::collections::BTreeMap;
use std::sync::OnceLock;

use xark::Field;
use xark_ir::primitive::PrimitiveProgram;
use xark_ir::solver;
use xark_ir::witness_search::{WitnessSearch, search_witnesses};
use xark_merkle::poseidon2::{IndexedLeaf, merkle_root};
use xark_merkle::tree::{IndexedTree, InsertError, Tree};
use xark_poseidon2::hash2;

/// ASCII `xarkzero`, the empty leaf the xark examples use.
const XARKZERO: u64 = 0x7861_726b_7a65_726f;

fn dec(s: &str) -> Field {
    Field::from(s)
}

// ---------------------------------------------------------------------------
// Host builders
// ---------------------------------------------------------------------------

/// `merkle_ref.py`'s roots: the builders agree with an implementation sharing no
/// code with them.
#[test]
fn roots_match_the_python_reference() {
    assert_eq!(
        Tree::<20>::poseidon2(Field::zero()).root(),
        dec("18553456084907201795502236692379304745578284738051224296916325877031987337886")
    );
    let empty = Tree::<20>::poseidon2(Field::from(XARKZERO));
    assert_eq!(
        empty.root(),
        dec("1439767887670316961635979754996450100497196647340639303074942446247161859835")
    );
    let mut five = empty.clone();
    five.extend((1..=5u64).map(Field::from));
    assert_eq!(
        five.root(),
        dec("20251182879592738375146236982648858122303955567650466182211075151162712376037")
    );
    let mut small = Tree::<4>::poseidon2(Field::zero());
    small.extend((1..=5u64).map(Field::from));
    assert_eq!(
        small.root(),
        dec("11358102659771694108819058690687192069591111345103563893532564930130201729122")
    );

    let mut indexed = IndexedTree::<20>::new();
    let roots = [
        "12906252769921838844593760299554799502078510945125833922079135609842941673596",
        "9964590121663308782928188684835273497692772914542409550436262642366149967957",
        "17624178846835818688836360869163263253848733445771306473776187989017522050853",
        "8371828697726696993876613131682221292178853304826461177718210156689063267756",
    ];
    assert_eq!(indexed.root(), dec(roots[0]));
    for (v, root) in [30u64, 10, 20].into_iter().zip(&roots[1..]) {
        let ins = indexed.insert(Field::from(v)).unwrap();
        assert_eq!(ins.new_root, dec(root), "after inserting {v}");
    }
}

/// The root of `leaves` in a depth-`depth` tree, every node hashed over
/// `ark_bn254::Fr` from the full bottom level: no empty-subtree shortcut, no
/// incremental update.
fn dense_root(leaves: &[Field], depth: usize, empty: Field) -> Field {
    use std::str::FromStr;
    use xark_poseidon2::native::{Fr, hash2};
    let fr = |x: Field| Fr::from_str(&x.to_decimal()).ok().unwrap();
    let mut level: Vec<Fr> = (0..1usize << depth)
        .map(|i| fr(leaves.get(i).copied().unwrap_or(empty)))
        .collect();
    while level.len() > 1 {
        level = level.chunks(2).map(|p| hash2(p[0], p[1])).collect();
    }
    Field::from(level[0])
}

#[test]
fn every_path_folds_to_the_dense_root() {
    const D: usize = 5;
    let empty = Field::from(XARKZERO);
    let leaves: Vec<Field> = (0..1u64 << D).map(|i| Field::from(i * 7 + 3)).collect();
    // Grow the tree by pushes and uneven extends; after each, the root is the
    // dense one and every slot's path, written or not, folds to it.
    let mut tree = Tree::<D>::poseidon2(empty);
    let mut n = 0;
    for chunk in [0usize, 1, 2, 3, 1, 5, 8, 12] {
        if chunk == 1 {
            tree.push(leaves[n]);
        } else {
            tree.extend(leaves[n..n + chunk].iter().copied());
        }
        n += chunk;
        assert_eq!(tree.len(), n);
        let root = dense_root(&leaves[..n], D, empty);
        assert_eq!(tree.root(), root, "{n} leaves");
        for i in 0..tree.capacity() {
            let p = tree.path(i);
            assert_eq!(merkle_root(tree.leaf(i), p.siblings, p.index_bits()), root);
        }
    }
    assert_eq!(n, tree.capacity());
    // Rewriting a leaf moves the root as rebuilding would.
    let mut changed = leaves.clone();
    changed[9] = Field::from(1234u64);
    tree.set(9, changed[9]);
    assert_eq!(tree.root(), dense_root(&changed, D, empty));
    assert_eq!(tree.empty_subtrees().len(), D + 1);
    assert_eq!(
        Tree::<D>::poseidon2(empty).path(0).siblings,
        tree.empty_subtrees()[..D]
    );
}

/// The Poseidon (v1) builder folds as `xark_merkle::merkle_root` does.
#[test]
fn the_poseidon_builder_matches_merkle_root() {
    let mut tree = Tree::<6>::poseidon(Field::from(XARKZERO));
    tree.extend((0..11u64).map(Field::from));
    for i in [0, 5, 10, 11, 63] {
        let p = tree.path(i);
        assert_eq!(
            xark_merkle::merkle_root(tree.leaf(i), p.siblings, p.index_bits()),
            tree.root()
        );
    }
}

#[test]
#[should_panic(expected = "the tree is full")]
fn a_full_tree_refuses_a_push() {
    let mut tree = Tree::<2>::poseidon2(Field::zero());
    tree.extend((1..=5u64).map(Field::from));
}

/// Insert values in a scrambled order; after each, the list is sorted, every
/// absent value has a low leaf that proves it absent, every present one has none,
/// and each insertion's witness reaches its new root (all by the circuit
/// functions, run on the host).
#[test]
fn the_indexed_tree_stays_a_sorted_list() {
    const D: usize = 5;
    let mut tree = IndexedTree::<D>::new();
    let values: Vec<u64> = (1..=20u64).map(|i| (i * 37) % 101 + 1).collect();
    let mut present = vec![0u64];
    for &v in &values {
        let x = Field::from(v);
        let ins = tree.insert(x).unwrap();
        assert_eq!(ins.old_root, {
            let p = ins.low_path;
            merkle_root(ins.low.hash(), p.siblings, p.index_bits())
        });
        let new_root = xark_merkle::poseidon2::indexed_insert::<D, 8>(
            ins.old_root,
            x,
            ins.low,
            ins.low_path.siblings,
            ins.low_path.index_bits(),
            ins.new_path.siblings,
            ins.new_path.index_bits(),
        );
        assert_eq!(new_root, tree.root());
        assert_eq!(ins.new_path.index, tree.len() - 1);
        present.push(v);
        present.sort();

        // The list: from the head, each leaf points at the next larger value.
        let mut at = 0usize;
        for w in present.windows(2) {
            let leaf = tree.leaf(at).unwrap();
            assert_eq!(leaf.value, Field::from(w[0]));
            assert_eq!(leaf.next_value, Field::from(w[1]));
            at = tree.find(Field::from(w[1])).unwrap();
            assert_eq!(leaf.next_index, Field::from(at as u64));
        }
        assert_eq!(tree.leaf(at).unwrap().next_value, Field::zero());

        for probe in 0..110u64 {
            let x = Field::from(probe);
            match tree.non_membership(x) {
                Some(nm) => {
                    assert!(!present.contains(&probe));
                    let p = nm.path;
                    xark_merkle::poseidon2::indexed_non_membership::<D, 8>(
                        x,
                        nm.low,
                        p.siblings,
                        p.index_bits(),
                        tree.root(),
                    );
                }
                None => assert!(present.contains(&probe), "{probe} has no low leaf"),
            }
        }
    }
    assert_eq!(
        tree.insert(Field::from(values[3])),
        Err(InsertError::Present)
    );
    assert_eq!(tree.insert(Field::zero()), Err(InsertError::Present));
    let mut fill = 200u64;
    while tree.len() < 1 << D {
        tree.insert(Field::from(fill)).unwrap();
        fill += 1;
    }
    assert_eq!(tree.insert(Field::from(fill)), Err(InsertError::Full));
}

// ---------------------------------------------------------------------------
// Circuits
// ---------------------------------------------------------------------------

fn verify_src(d: usize) -> String {
    format!(
        "use xark::prelude::*;\n\
         use xark_merkle::poseidon2::merkle_verify;\n\
         pub const D: usize = {d};\n\
         pub fn circuit(leaf: Private<Field>, siblings: Private<[Field; D]>,\n\
           index_bits: Private<[Field; D]>, root: Public<Field>) {{\n\
           merkle_verify(leaf, siblings, index_bits, root);\n\
         }}\n"
    )
}

fn append_src(d: usize) -> String {
    format!(
        "use xark::prelude::*;\n\
         use xark_merkle::poseidon2::merkle_append;\n\
         pub const D: usize = {d};\n\
         pub fn circuit(leaf: Private<Field>, siblings: Private<[Field; D]>,\n\
           index_bits: Private<[Field; D]>, old_root: Public<Field>, new_root: Public<Field>) {{\n\
           require_eq(merkle_append(old_root, Field::from({XARKZERO}u64), leaf, siblings, index_bits), new_root);\n\
         }}\n"
    )
}

fn absent_src(d: usize, bits: usize) -> String {
    format!(
        "use xark::prelude::*;\n\
         use xark_merkle::poseidon2::{{IndexedLeaf, indexed_non_membership}};\n\
         pub const D: usize = {d};\n\
         pub fn circuit(x: Public<Field>, low: Private<IndexedLeaf>, siblings: Private<[Field; D]>,\n\
           index_bits: Private<[Field; D]>, root: Public<Field>) {{\n\
           indexed_non_membership::<D, {bits}>(x, low, siblings, index_bits, root);\n\
         }}\n"
    )
}

fn insert_src(d: usize, bits: usize) -> String {
    format!(
        "use xark::prelude::*;\n\
         use xark_merkle::poseidon2::{{IndexedLeaf, indexed_insert}};\n\
         pub const D: usize = {d};\n\
         pub fn circuit(x: Public<Field>, low: Private<IndexedLeaf>,\n\
           low_siblings: Private<[Field; D]>, low_index_bits: Private<[Field; D]>,\n\
           new_siblings: Private<[Field; D]>, new_index_bits: Private<[Field; D]>,\n\
           old_root: Public<Field>, new_root: Public<Field>) {{\n\
           let root = indexed_insert::<D, {bits}>(old_root, x, low, low_siblings, low_index_bits,\n\
             new_siblings, new_index_bits);\n\
           require_eq(root, new_root);\n\
         }}\n"
    )
}

fn compile(name: &str, src: &str) -> PrimitiveProgram {
    let c = xark_test_harness::compile_source(name, src, "bn254");
    assert!(c.status_success, "compiling {name} failed: {}", c.stderr);
    c.program()
}

/// The depth-4 circuits the round trips and rejections run, compiled once.
fn verify4() -> &'static PrimitiveProgram {
    static P: OnceLock<PrimitiveProgram> = OnceLock::new();
    P.get_or_init(|| compile("xark_merkle_p2_verify4", &verify_src(4)))
}
fn append4() -> &'static PrimitiveProgram {
    static P: OnceLock<PrimitiveProgram> = OnceLock::new();
    P.get_or_init(|| compile("xark_merkle_p2_append4", &append_src(4)))
}
fn absent4() -> &'static PrimitiveProgram {
    static P: OnceLock<PrimitiveProgram> = OnceLock::new();
    P.get_or_init(|| compile("xark_merkle_p2_absent4", &absent_src(4, 252)))
}
fn insert4() -> &'static PrimitiveProgram {
    static P: OnceLock<PrimitiveProgram> = OnceLock::new();
    P.get_or_init(|| compile("xark_merkle_p2_insert4", &insert_src(4, 252)))
}

/// A circuit's named inputs, as the solver takes them.
#[derive(Clone, Default)]
struct Inputs(Vec<(String, Field)>);

impl Inputs {
    fn set(mut self, name: &str, v: Field) -> Self {
        self.0.retain(|(n, _)| n != name);
        self.0.push((name.to_string(), v));
        self
    }
    fn array(mut self, name: &str, vs: &[Field]) -> Self {
        for (i, v) in vs.iter().enumerate() {
            self = self.set(&format!("{name}[{i}]"), *v);
        }
        self
    }
    fn leaf(self, name: &str, l: IndexedLeaf) -> Self {
        self.set(&format!("{name}.value"), l.value)
            .set(&format!("{name}.next_index"), l.next_index)
            .set(&format!("{name}.next_value"), l.next_value)
    }
    fn ids(&self, p: &PrimitiveProgram) -> BTreeMap<u32, String> {
        self.0
            .iter()
            .map(|(n, v)| {
                let id = p
                    .vars
                    .iter()
                    .find(|x| x.name == *n)
                    .unwrap_or_else(|| panic!("no input `{n}`"))
                    .id;
                (id, v.to_decimal())
            })
            .collect()
    }
}

fn accepts(p: &PrimitiveProgram, i: &Inputs) -> bool {
    solver::solve_and_check(p, &i.ids(p)).is_ok()
}

/// The honest witness is accepted, fully pinned, and each derived value tampered
/// alone (`+1`) breaks a row: no prover-chosen value is free. The honest witness
/// satisfies every row, so only the rows reading the tampered value are checked.
fn accepts_only_the_honest_witness(p: &PrimitiveProgram, i: &Inputs) {
    let honest = solver::solve_and_check(p, &i.ids(p)).expect("the honest witness");
    let holes = solver::analyze_underconstrained(p, &honest);
    assert!(holes.is_empty(), "under-constrained: {holes:?}");
    let mut rows: BTreeMap<u32, Vec<usize>> = BTreeMap::new();
    for (r, e) in p.constraints.iter().enumerate() {
        let muls = e.mul_terms.iter().flat_map(|t| [t.left, t.right]);
        for v in muls.chain(e.linear_terms.iter().map(|t| t.var)) {
            let at = rows.entry(v).or_default();
            if at.last() != Some(&r) {
                at.push(r);
            }
        }
    }
    let mut sub = PrimitiveProgram {
        constraints: Vec::new(),
        ..p.clone()
    };
    let mut tampered = 0;
    for v in &p.vars {
        let Some(at) = rows.get(&v.id) else { continue };
        if v.role != xark_ir::primitive::VarRole::Derived {
            continue;
        }
        sub.constraints = at.iter().map(|&r| p.constraints[r].clone()).collect();
        let mut forged = honest.clone();
        let x = Field::from(forged[&v.id].to_decimal().as_str()) + Field::one();
        forged.insert(v.id, solver::fp_from_decimal(&x.to_decimal(), p));
        assert!(
            solver::check(&sub, &forged).is_err(),
            "`{}` tampered is accepted",
            v.name
        );
        tampered += 1;
    }
    assert!(tampered > 0);
}

/// A depth-4 tree with leaves 1..=5 and its path to `index`.
fn tree4() -> Tree<4> {
    let mut t = Tree::<4>::poseidon2(Field::from(XARKZERO));
    t.extend((1..=5u64).map(|i| Field::from(i * 1000 + 1)));
    t
}

#[test]
fn verify_round_trips_and_rejects_forgeries() {
    let p = verify4();
    let tree = tree4();
    for index in [0, 3, 4, 5, 15] {
        let path = tree.path(index);
        let ok = Inputs::default()
            .set("leaf", tree.leaf(index))
            .array("siblings", &path.siblings)
            .array("index_bits", &path.index_bits())
            .set("root", tree.root());
        assert!(accepts(p, &ok), "slot {index}");

        // A wrong sibling, a flipped bit, a wrong leaf: each misses the root.
        let mut sib = path.siblings;
        sib[2] += Field::one();
        assert!(!accepts(p, &ok.clone().array("siblings", &sib)));
        assert!(!accepts(p, &ok.clone().set("leaf", Field::from(77u64))));
        for level in 0..4 {
            let mut bits = path.index_bits();
            bits[level] = Field::one() - bits[level];
            // Where a node and its sibling are both empty subtrees, the swap
            // changes nothing: an empty slot's path proves any empty slot.
            let same = tree.empty_subtrees()[level] == path.siblings[level]
                && (index >> level) << level >= tree.len();
            let flipped = ok.clone().array("index_bits", &bits);
            assert_eq!(accepts(p, &flipped), same, "slot {index}, level {level}");
        }
    }
}

/// A bit of 2 swaps a level into `(2·sib − node, 2·node − sib)`, neither child
/// order. With the root that fold reaches, every row but the bit's booleanity
/// holds, so that row is what refuses it.
#[test]
fn verify_refuses_a_non_boolean_bit() {
    let p = verify4();
    let tree = tree4();
    let path = tree.path(2);
    let mut bits = path.index_bits();
    bits[0] = Field::from(2u64);
    // The fold with the forged bit, by hand (the circuit function would refuse it).
    let mut node = tree.leaf(2);
    for (bit, sib) in bits.iter().zip(path.siblings) {
        let left = node + *bit * (sib - node);
        node = hash2(left, node + sib - left);
    }
    let forged = Inputs::default()
        .set("leaf", tree.leaf(2))
        .array("siblings", &path.siblings)
        .array("index_bits", &bits)
        .set("root", node);
    let err = solver::solve_and_check(p, &forged.ids(p)).expect_err("a bit of 2");
    let solver::SolveError::ConstraintFailed(row) = err else {
        panic!("expected a failed row, got {err:?}");
    };
    let bit = p
        .vars
        .iter()
        .find(|v| v.name == "index_bits[0]")
        .unwrap()
        .id;
    let c = &p.constraints[row];
    assert!(
        c.mul_terms.iter().any(|t| t.left == bit && t.right == bit),
        "the failing row must be index_bits[0]'s booleanity, got {c:?}"
    );
}

#[test]
fn append_writes_an_empty_slot_only() {
    let p = append4();
    let mut tree = tree4();
    let old_root = tree.root();
    let path = tree.path(tree.len());
    let leaf = Field::from(424242u64);
    tree.push(leaf);
    let ok = Inputs::default()
        .set("leaf", leaf)
        .array("siblings", &path.siblings)
        .array("index_bits", &path.index_bits())
        .set("old_root", old_root)
        .set("new_root", tree.root());
    assert!(accepts(p, &ok));

    // Another new root, another old root, another slot.
    assert!(!accepts(p, &ok.clone().set("new_root", old_root)));
    assert!(!accepts(p, &ok.clone().set("old_root", tree.root())));
    let mut bits = path.index_bits();
    bits[0] = Field::one() - bits[0];
    assert!(!accepts(p, &ok.clone().array("index_bits", &bits)));

    // Over a written slot: slot 2's path in the old tree is honest, and the
    // "new root" is the old tree with slot 2 overwritten, but slot 2 wasn't empty.
    let mut old = tree4();
    let before = old.root();
    let path2 = old.path(2);
    old.set(2, leaf);
    let over = Inputs::default()
        .set("leaf", leaf)
        .array("siblings", &path2.siblings)
        .array("index_bits", &path2.index_bits())
        .set("old_root", before)
        .set("new_root", old.root());
    assert!(!accepts(p, &over));
}

/// An indexed tree holding 10, 20, 30, 40 (depth 4).
fn indexed4() -> IndexedTree<4> {
    let mut t = IndexedTree::<4>::new();
    for v in [30u64, 10, 40, 20] {
        t.insert(Field::from(v)).unwrap();
    }
    t
}

fn absent_inputs(tree: &IndexedTree<4>, x: Field, low_slot: usize) -> Inputs {
    let low = tree.leaf(low_slot).unwrap();
    let path = tree.path(low_slot);
    Inputs::default()
        .set("x", x)
        .leaf("low", low)
        .array("siblings", &path.siblings)
        .array("index_bits", &path.index_bits())
        .set("root", tree.root())
}

#[test]
fn non_membership_round_trips_and_rejects_forgeries() {
    let p = absent4();
    let tree = indexed4();
    // Below the first value, between two, and past the last (`next_value = 0`).
    for x in [1u64, 15, 39, 41, 1 << 60] {
        let x = Field::from(x);
        let nm = tree.non_membership(x).unwrap();
        let ok = absent_inputs(&tree, x, nm.path.index);
        assert!(accepts(p, &ok), "{x:?}");
    }
    // The largest value the 252-bit comparison takes, and the first it doesn't.
    let top = Field::from(2u64).pow(252) - Field::one();
    let nm = tree.non_membership(top).unwrap();
    assert!(accepts(p, &absent_inputs(&tree, top, nm.path.index)));
    let over = top + Field::one();
    assert!(!accepts(p, &absent_inputs(&tree, over, nm.path.index)));

    let slot = |v: u64| tree.find(Field::from(v)).unwrap();
    // A present value through the leaf below it: 10 < 20 but 20 is not < 20.
    assert!(!accepts(
        p,
        &absent_inputs(&tree, Field::from(20u64), slot(10))
    ));
    // A present value through its own leaf: 20 is not < 20.
    assert!(!accepts(
        p,
        &absent_inputs(&tree, Field::from(20u64), slot(20))
    ));
    // A low leaf whose range misses x: 25 isn't between 10 and 20, or 30 and 40.
    assert!(!accepts(
        p,
        &absent_inputs(&tree, Field::from(25u64), slot(10))
    ));
    assert!(!accepts(
        p,
        &absent_inputs(&tree, Field::from(25u64), slot(30))
    ));
    // The largest leaf claimed for a value below it: 35 isn't above 40.
    assert!(!accepts(
        p,
        &absent_inputs(&tree, Field::from(35u64), slot(40))
    ));
    // x = 0 is the head's, so never absent.
    assert!(!accepts(p, &absent_inputs(&tree, Field::zero(), 0)));
    // A made-up low leaf that would cover 20 isn't in the tree.
    let fake = IndexedLeaf {
        value: Field::from(10u64),
        next_index: Field::from(slot(30) as u64),
        next_value: Field::from(30u64),
    };
    let forged = absent_inputs(&tree, Field::from(20u64), slot(10)).leaf("low", fake);
    assert!(!accepts(p, &forged));
}

fn insert_inputs(ins: &xark_merkle::tree::Insertion<4>) -> Inputs {
    Inputs::default()
        .set("x", ins.value)
        .leaf("low", ins.low)
        .array("low_siblings", &ins.low_path.siblings)
        .array("low_index_bits", &ins.low_path.index_bits())
        .array("new_siblings", &ins.new_path.siblings)
        .array("new_index_bits", &ins.new_path.index_bits())
        .set("old_root", ins.old_root)
        .set("new_root", ins.new_root)
}

#[test]
fn insert_round_trips_and_rejects_forgeries() {
    let p = insert4();
    let mut tree = indexed4();
    let before = tree.clone();
    let ins = tree.insert(Field::from(25u64)).unwrap();
    let ok = insert_inputs(&ins);
    assert!(accepts(p, &ok));
    // And as the last value, the low leaf being the old largest.
    let last = tree.insert(Field::from(99u64)).unwrap();
    assert!(accepts(p, &insert_inputs(&last)));

    // Another value, another new root, a stale old root.
    assert!(!accepts(p, &ok.clone().set("x", Field::from(26u64))));
    assert!(!accepts(p, &ok.clone().set("new_root", ins.old_root)));
    assert!(!accepts(p, &ok.clone().set("old_root", last.new_root)));
    // A present value: inserting 20 again through 10's leaf.
    let low = before.find(Field::from(10u64)).unwrap();
    let mut dup = ok
        .clone()
        .set("x", Field::from(20u64))
        .leaf("low", before.leaf(low).unwrap());
    let lp = before.path(low);
    dup = dup
        .array("low_siblings", &lp.siblings)
        .array("low_index_bits", &lp.index_bits());
    assert!(!accepts(p, &dup));
    // Over a written slot: slot 1's path for the new leaf.
    let written = tree.path(1);
    let over = ok
        .clone()
        .array("new_siblings", &written.siblings)
        .array("new_index_bits", &written.index_bits());
    assert!(!accepts(p, &over));
}

// ---------------------------------------------------------------------------
// Soundness by exhaustive witness search
// ---------------------------------------------------------------------------

/// Exactly one witness proves `i`, or none does: the adversary's view, not the
/// honest solver's.
fn unique_or_none(p: &PrimitiveProgram, i: &Inputs) -> bool {
    match search_witnesses(p, &i.ids(p), 1 << 14).unwrap() {
        WitnessSearch::Unique(_) => true,
        WitnessSearch::None => false,
        other => panic!("{other:?}"),
    }
}

/// At depth 2 (8-bit values for the indexed tree) the search decides every
/// circuit: one witness for each honest input, none for each forgery. Each
/// honest witness also survives no single tampered value.
#[test]
fn the_witness_search_finds_one_witness_or_none() {
    let (verify, append, absent, insert) = std::thread::scope(|s| {
        let v = s.spawn(|| compile("xark_merkle_p2_verify2", &verify_src(2)));
        let a = s.spawn(|| compile("xark_merkle_p2_append2", &append_src(2)));
        let n = s.spawn(|| compile("xark_merkle_p2_absent2", &absent_src(2, 8)));
        let i = s.spawn(|| compile("xark_merkle_p2_insert2", &insert_src(2, 8)));
        let j = |h: std::thread::ScopedJoinHandle<'_, PrimitiveProgram>| h.join().unwrap();
        (j(v), j(a), j(n), j(i))
    });

    let mut tree = Tree::<2>::poseidon2(Field::from(XARKZERO));
    tree.extend([Field::from(5u64), Field::from(6u64)]);
    let old_root = tree.root();
    let path = tree.path(1);
    let ok = Inputs::default()
        .set("leaf", tree.leaf(1))
        .array("siblings", &path.siblings)
        .array("index_bits", &path.index_bits())
        .set("root", old_root);
    assert!(unique_or_none(&verify, &ok));
    accepts_only_the_honest_witness(&verify, &ok);
    let mut bits = path.index_bits();
    bits[1] = Field::from(2u64);
    assert!(!unique_or_none(
        &verify,
        &ok.clone().array("index_bits", &bits)
    ));
    assert!(!unique_or_none(
        &verify,
        &ok.clone().set("leaf", Field::from(7u64))
    ));

    let slot = tree.path(2);
    let leaf = Field::from(9u64);
    tree.push(leaf);
    let app = Inputs::default()
        .set("leaf", leaf)
        .array("siblings", &slot.siblings)
        .array("index_bits", &slot.index_bits())
        .set("old_root", old_root)
        .set("new_root", tree.root());
    assert!(unique_or_none(&append, &app));
    accepts_only_the_honest_witness(&append, &app);
    assert!(!unique_or_none(
        &append,
        &app.clone().set("old_root", tree.root())
    ));

    let mut it = IndexedTree::<2>::new();
    it.insert(Field::from(100u64)).unwrap();
    it.insert(Field::from(50u64)).unwrap();
    let in_ = |x: u64, low: usize| {
        let l = it.leaf(low).unwrap();
        let p = it.path(low);
        Inputs::default()
            .set("x", Field::from(x))
            .leaf("low", l)
            .array("siblings", &p.siblings)
            .array("index_bits", &p.index_bits())
            .set("root", it.root())
    };
    let s50 = it.find(Field::from(50u64)).unwrap();
    let s100 = it.find(Field::from(100u64)).unwrap();
    assert!(unique_or_none(&absent, &in_(70, s50)));
    accepts_only_the_honest_witness(&absent, &in_(70, s50));
    assert!(unique_or_none(&absent, &in_(255, s100)));
    assert!(!unique_or_none(&absent, &in_(50, s50)));
    assert!(!unique_or_none(&absent, &in_(100, s50)));
    assert!(!unique_or_none(&absent, &in_(256, s100)));
    assert!(!unique_or_none(&absent, &in_(70, 0)));

    let ins = it.insert(Field::from(70u64)).unwrap();
    let honest = Inputs::default()
        .set("x", ins.value)
        .leaf("low", ins.low)
        .array("low_siblings", &ins.low_path.siblings)
        .array("low_index_bits", &ins.low_path.index_bits())
        .array("new_siblings", &ins.new_path.siblings)
        .array("new_index_bits", &ins.new_path.index_bits())
        .set("old_root", ins.old_root)
        .set("new_root", ins.new_root);
    assert!(unique_or_none(&insert, &honest));
    accepts_only_the_honest_witness(&insert, &honest);
    assert!(!unique_or_none(
        &insert,
        &honest.clone().set("x", Field::from(50u64))
    ));
}

// ---------------------------------------------------------------------------
// Cost
// ---------------------------------------------------------------------------

/// The proven (minimized) R1CS at depth 20 with 252-bit values. Per level a
/// Poseidon2 `hash2` and `cond_swap`'s booleanity and product; a second fold over
/// the same path adds a `hash2` and one product.
#[test]
fn depth_20_costs() {
    let srcs = [
        ("xark_merkle_p2_verify20", verify_src(20)),
        ("xark_merkle_p2_append20", append_src(20)),
        ("xark_merkle_p2_absent20", absent_src(20, 252)),
        ("xark_merkle_p2_insert20", insert_src(20, 252)),
    ];
    let counts: Vec<usize> = std::thread::scope(|s| {
        let hs: Vec<_> = srcs
            .iter()
            .map(|(name, src)| {
                s.spawn(move || {
                    let c = xark_test_harness::compile_source(name, src, "bn254");
                    assert!(c.status_success, "compiling {name} failed: {}", c.stderr);
                    c.minimized_r1cs_len()
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    eprintln!("depth 20: verify, append, non-membership, insert = {counts:?}");
    assert_eq!(counts, [4840, 9660, 6585, 22025]);
}
