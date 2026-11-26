# xark-rsa

RSASSA-PKCS1-v1_5 signature verification with SHA-256 for xark circuits. This is
the 2048-bit instance, public exponent 65537.

The primary public input follows the zkGolf RSA interface: the big-endian octet
strings **256-byte modulus, 256-byte signature, 32-byte digest**. The circuit
packs each octet with `to_bits::<8>` and builds the 25 x 82-bit internal limbs
in-circuit; the `n` top bit, `sig < n`, and the PKCS#1 v1.5 encoded-message
comparison are all on those limbs. A 17 x 121 whole-number API
(`verify_sha256`) remains for hosts that have already decoded the certificate
integers; both paths share the same 25 x 82 arithmetic.

The crate is for *verification* only. It has no signing code and no private key
material.

## Use

The zkGolf-style byte input, which is what `examples/rsa2048` uses:

```rust
use xark::prelude::*;

#[circuit]
pub fn rsa2048(n: Public<[u8; 256]>, sig: Private<[u8; 256]>, digest: Public<[u8; 32]>) {
    xark_rsa::verify_sha256_bytes(n, sig, digest);
}
```

The 17 x 121 whole-number input, for a host that has decoded `n` and `sig`:

```rust
use xark::prelude::*;
use xark_rsa::prelude::*;

#[circuit]
pub fn rsa2048(n: Public<U2048>, sig: Private<U2048>, digest: Public<[u8; 32]>) {
    xark_rsa::verify_sha256(n, sig, digest);
}
```

On the host, `U2048` is one whole number (`"0x…"` or decimal). The `Bignum`
input reader splits it into 17 limbs and range-checks every limb.

To verify a digest the circuit computed itself, pass the eight 32-bit words
`xark_sha256` returns:

```rust
let digest = xark_sha256::sha256::<144>(body);
xark_rsa::verify_sha256_words(n, sig, digest);
```

## API

| Item | What it does |
|---|---|
| `verify_sha256_bytes(n, sig, digest)` | Verify from 256-byte big-endian `n` and `sig` and a 32-byte digest; packs the octets to the 25 x 82 internal limbs. This is the zkGolf-compatible public input. |
| `verify_sha256(n, sig, digest)` | Verify from typed 17 x 121 `U2048` inputs; the entry point range-checks the limbs (the reader’s bits are reused). |
| `verify_sha256_words(n, sig, words)` | The same, from the eight `[[Field; 32]; 8]` SHA-256 output words; each word is boolean-checked and the limbs are range-checked. |
| `verify_sha256_limbs(n, sig, digest)` | The same from raw `[Field; 17]` arrays; it range-checks them first. |
| `sha256_em(digest)` | The expected EMSA-PKCS1-v1_5 encoded message as 17 limbs. |
| `sha256_em_bits(bits)` | The same from 256 digest bits. |
| `digest_bits(digest)` | The 256 bits of a 32-byte big-endian digest. |
| `mod_exp_65537(base, m, m_minus_1)` | Standalone 17×121 `base^65537 mod m` helper; the verifier uses the 25×82 chain, not this path. |
| `U2048` | `Bignum<17, 121>`, the whole-number input view. |

All paths enforce that `n` is exactly 2048 bits (`2^2047 <= n < 2^2048`), that
`sig < n`, and that the recovered value equals the PKCS#1 v1.5 encoding of the
digest. They do not validate the RSA key structure (oddness/semiprimality); the
caller's key allowlist is the trust boundary. A caller that builds limbs itself
should use `Bignum::new_checked` (or `verify_sha256_limbs`, which range-checks
the raw arrays); `Bignum::new` is the unchecked constructor.

## Host-side decoding

The host decodes the certificate or message, extracts the modulus, signature,
and SHA-256 digest, and passes those three values. The circuit needs only:

* the 2048-bit modulus,
* the 2048-bit signature,
* the SHA-256 digest (or the message, if the circuit hashes it).

With `verify_sha256_bytes` the host passes the raw big-endian
modulus and signature octets (and the digest bytes), so the byte-to-integer
packing is inside the proof. With `verify_sha256` it passes whole numbers and
the typed input reader does the limb split. The signature can be private; the
digest can be private too.

## Cost

* The byte-input example (`examples/rsa2048`, the zkGolf-style public input)
  verifies in **125,856 constraints** in the `xark build`; the harness counts
  **127,089 primitive constraints** and **124,995 multiplication gates**. The
  baseline before the golf was 157,451 / 155,153 (a 20.1% reduction).
* The raw-limb `verify_sha256_limbs` is **137,051 primitive constraints**; the
  typed `verify_sha256` adds its own limb range checks, so a `Bignum::new`
  caller is safe, and its harness is **141,199**.
* The internal chain is 25 x 82-bit limbs with lazy reduction (an intermediate
  is proved `< 2^2048`, not `< n`; the final fused step pins the canonical
  target), paired-column carries, and a terminal multiply whose remainder is
  the encoded message. The octet public input is packed to those limbs with
  `to_bits::<8>`.
* With the generic KAT inputs, `xark prove --verify` solves in 0.04 s and proves
  in 0.70 s (release binary, `PROVE_TIME=1`, one machine), with 288 public
  inputs; the proof verifies.
* The zkGolf public input is bytes, not a limb vector. A 25 x 82 *public* input
  would not match that contract; the byte path is the zkGolf-compatible one.

## Tests

* `tests/known_answer.rs` verifies a generated RSA-2048 key and a PKCS#1 v1.5
  SHA-256 signature over a test message, through both the byte and whole-number
  paths. It also checks on the host that the digest is SHA-256 of the test
  message; the circuit receives only `n`, `sig`, and `digest`.
* `tests/optimized.rs` covers generated keys, edge signatures, 2047-bit `n`,
  the RFC 8017 EM, the host `pow` differential, and the underconstrained check.
* The example test rejects a tampered digest and repeats the test-message hash
  check.
* The 25×82 `require_lt` rows and the 17×121 `range_check_limbs` rows have Lean
  templates (`require_lt__25x82`, `range_check_limbs__17x121`); the byte packing
  uses the base `to_bits` (8-bit) template. `cargo xtask lean-export --check`
  passes all 66 templates, `--coverage` passes, and `cargo xtask digests` passes;
  the optimized digest is pinned in `tests/stable-digests.txt`.

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
