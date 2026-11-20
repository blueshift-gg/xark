# Independent reference for `schnorr` (tests/schnorr.rs's known answer): plain-integer
# Grumpkin arithmetic and the Python Poseidon2 of `xark-poseidon2`, apart from the
# arkworks host signer. Run from this directory: `python3 schnorr_ref.py`.
import os, sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "xark-poseidon2"))
from poseidon2_ref import poseidon2_perm

r = 21888242871839275222246405745257275088548364400416034343698204186575808495617  # BN254 Fr: Grumpkin's base field
n = 21888242871839275222246405745257275088696311157297823662689037894645226208583  # BN254 Fq: Grumpkin's group order
G = (1, 17631683881184975370165255887551781615748388533673675138860)  # y² = x³ − 17


def add(p, q):
    if p is None:
        return q
    if q is None:
        return p
    if p[0] == q[0] and (p[1] + q[1]) % r == 0:
        return None
    if p == q:
        lam = 3 * p[0] * p[0] * pow(2 * p[1], -1, r) % r
    else:
        lam = (q[1] - p[1]) * pow(q[0] - p[0], -1, r) % r
    x = (lam * lam - p[0] - q[0]) % r
    return (x, (lam * (p[0] - x) - p[1]) % r)


def mul(k, p):
    acc = None
    while k:
        if k & 1:
            acc = add(acc, p)
        p = add(p, p)
        k >>= 1
    return acc


def tag(s):
    return int.from_bytes(s.encode(), "big") << 64


def sponge(t, items):
    state = [0, 0, (t + len(items)) % r]
    for i in range(0, len(items), 2):
        state[0] = (state[0] + items[i]) % r
        if i + 1 < len(items):
            state[1] = (state[1] + items[i + 1]) % r
        state = poseidon2_perm(state)
    return state


def sign(seed, msg):
    x = int.from_bytes(seed, "big") % n
    P = mul(x, G)
    lo, hi = x % 2**127, x >> 127
    h = sponge(tag("grumpkin-schnorr-nonce"), [lo, hi, P[0], P[1]] + msg)
    k = (h[0] * r + h[1]) % n
    R = mul(k, G)
    e = sponge(tag("grumpkin-schnorr"), [R[0], R[1], P[0], P[1]] + msg)[0]
    s = (k + e * x) % n
    assert mul(s, G) == add(R, mul(e, P))
    return P, R, s


if __name__ == "__main__":
    P, R, s = sign(bytes([7] * 32), [1, 2])
    print("KAT_PK", P)
    print("KAT_R ", R)
    print("KAT_S ", s)
