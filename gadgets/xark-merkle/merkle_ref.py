# Reference values for xark-merkle's Poseidon2 trees, from the Python Poseidon2 in
# ../xark-poseidon2/poseidon2_ref.py (Horizen Labs constants), with no Rust in the
# loop: tests/poseidon2.rs pins what this prints. Run: python3 merkle_ref.py
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "xark-poseidon2"))
from poseidon2_ref import P, poseidon2_perm  # noqa: E402


def hash2(a, b):
    return poseidon2_perm([a, b, 0])[0]


def sponge(xs):
    # Rate 2, capacity 1 seeded with the length (xark_poseidon2::hash).
    s = [0, 0, len(xs)]
    for i in range(0, len(xs), 2):
        s[0] = (s[0] + xs[i]) % P
        if i + 1 < len(xs):
            s[1] = (s[1] + xs[i + 1]) % P
        s = poseidon2_perm(s)
    return s[0]


def root(leaves, depth, empty):
    """The root of a depth-`depth` tree holding `leaves` from the left, every
    other slot `empty`, hashed level by level."""
    level, e = list(leaves), empty
    for _ in range(depth):
        if len(level) % 2:
            level.append(e)
        level = [hash2(level[i], level[i + 1]) for i in range(0, len(level), 2)]
        e = hash2(e, e)
    return level[0] if level else e


def indexed_root(values, depth):
    """The indexed tree after inserting `values` in order: slot 0 the head
    (0, 0, 0), slot i + 1 the i-th value, each pointing at the next larger."""
    slots = [0] + list(values)
    order = sorted(range(len(slots)), key=lambda i: slots[i])
    nxt = {}
    for a, b in zip(order, order[1:]):
        nxt[a] = (b, slots[b])
    nxt[order[-1]] = (0, 0)
    leaves = [sponge([slots[i], nxt[i][0], nxt[i][1]]) for i in range(len(slots))]
    return root(leaves, depth, 0)


XARKZERO = 0x7861726B7A65726F

if __name__ == "__main__":
    print("empty depth 20, leaf 0:       ", root([], 20, 0))
    print("empty depth 20, leaf xarkzero:", root([], 20, XARKZERO))
    print("depth 20, leaves 1..=5, xarkzero:", root(range(1, 6), 20, XARKZERO))
    print("depth 4, leaves 1..=5, leaf 0:   ", root(range(1, 6), 4, 0))
    for vs in ([], [30], [30, 10], [30, 10, 20]):
        print("indexed depth 20 after", vs, ":", indexed_root(vs, 20))
