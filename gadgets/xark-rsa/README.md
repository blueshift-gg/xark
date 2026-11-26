# xark-rsa

RSASSA-PKCS1-v1_5 signature verification with SHA-256 for xark circuits. This is
the 2048-bit instance: 17 little-endian 121-bit limbs (2057 bits) at the input
and API boundary, public exponent 65537, and a full EMSA-PKCS1-v1_5
encoded-message comparison. The input limb layout follows the zkGolf RSA
reference; internally the modular chain re-limb to 25 x 82 bits, which is what
lets two convolution columns share one carry (see "Cost").

The crate is for *verification* only. It has no signing code and no private key
material.

## Use

```rust
use xark::prelude::*;
use xark_rsa::prelude::*;

#[circuit]
pub fn rsa2048(n: Public<U2048>, sig: Private<U2048>, digest: Public<[u8; 32]>) {
    xark_rsa::verify_sha256(n, sig, digest);
}
```

On the host, `U2048` is one whole number (`"0x…"` or decimal). The `Bignum`
input reader splits it into limbs and range-checks every limb.

To verify a digest the circuit computed itself, pass the eight 32-bit words
`xark_sha256` returns:

```rust
let digest = xark_sha256::sha256::<144>(body);
xark_rsa::verify_sha256_words(n, sig, digest);
```

## API

| Item | What it does |
|---|---|
| `verify_sha256(n, sig, digest)` | Verify a 32-byte big-endian SHA-256 digest. `n`/`sig` are typed `U2048` inputs, range-checked by their input reader. |
| `verify_sha256_words(n, sig, words)` | The same, from the eight `[[Field; 32]; 8]` SHA-256 output words. |
| `verify_sha256_limbs(n, sig, digest)` | The same from raw `[Field; 17]` arrays; it range-checks them first. |
| `sha256_em(digest)` | The expected EMSA-PKCS1-v1_5 encoded message as 17 limbs. |
| `sha256_em_bits(bits)` | The same from 256 digest bits. |
| `digest_bits(digest)` | The 256 bits of a 32-byte big-endian digest. |
| `mod_exp_65537(base, m, m_minus_1)` | `base^65537 mod m` by left-to-right square-and-multiply. |
| `U2048` | `Bignum<17, 121>`. |

`verify_sha256` enforces that `n` is exactly 2048 bits (`2^2047 <= n < 2^2048`),
that `sig < n`, and that the recovered value equals the PKCS#1 v1.5 encoding of
the digest. It does not check that the modulus belongs to a trusted certificate;
that is the caller's or program's allowlist.

## Host-side decoding

The host does the JSON, Base64, DER, and date work. The circuit needs only:

* the 2048-bit modulus,
* the 2048-bit signature,
* the SHA-256 digest (or the message, if the circuit hashes it).

The modulus and signature can be passed as whole numbers. The signature is
private; the digest can be private too.

## Cost

* The real-certificate KAT (`tests/real_certificate.rs`) verifies in
  **135,695 constraints** in the `examples/rsa2048` build (`xark building
  circuit`); the test harness counts the same artifact as **137,026 primitive
  constraints** and **134,748 multiplication gates**. The baseline before the
  golf was 157,451 / 155,153.
* The internal chain is 25 x 82-bit limbs with lazy reduction (an intermediate
  is proved `< 2^2048`, not `< n`; the final fused step pins the canonical
  target), paired-column carries, and a terminal multiply whose remainder is
  the encoded message. Only the 17 x 121 input view is public API.

## Tests

* `tests/real_certificate.rs` verifies a real signature from the iAM Smart PKI:
  the leaf certificate `CN=IAM SMART` signed by `ID-CERT SIGNING CA CERT 3`
  (RSA-2048, SHA-256).
* The example test rejects a tampered digest.
* The 17×121 `require_lt` and `range_check_limbs` rows have Lean templates under
  `formal/templates/` (`require_lt__17x121`, `range_check_limbs__17x121`). The
  internal 25×82 conversion, range checks and paired-column carry rows are
  hand-written plain functions in `src/lib.rs` (their bound argument is in the
  doc comments). `cargo xtask lean-export --coverage` and `cargo xtask digests`
  pass in the normal checkout; the optimized digest is pinned in
  `tests/stable-digests.txt`.

Part of [xark](https://github.com/blueshift-gg/xark): zero-knowledge circuits in plain Rust, verified on Solana.
