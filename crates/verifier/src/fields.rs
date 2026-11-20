//! Building public inputs: field elements, 32 bytes little-endian, made the way a
//! circuit's `#[input]` makes them.
//!
//! The crate `xark export` writes builds its `PublicInputs` with these, and a program
//! that keeps its own struct packs it the same way. Everything here is a `const fn`,
//! so inputs a program knows at compile time (a policy's limits, an allow-list) are
//! constants, and a value too wide for its bits fails the build instead of the
//! proof:
//!
//! ```
//! use xark_verifier::fields::Packer;
//!
//! // `Policy { today: Days<1900, 2100>, born_by: Days<1900, 2100>, min: u64 }`:
//! // its three fields share one element, the first in the lowest bits.
//! const POLICY: [u8; 32] = Packer::new()
//!     .uint::<17>(46_335)
//!     .uint::<17>(39_761)
//!     .uint::<64>(500_000)
//!     .finish();
//! ```
//!
//! At run time the same checks panic, which aborts the program; values of the
//! generated types always fit.

/// One field element: 32 bytes, little-endian.
pub type Element = [u8; 32];

/// The bits `#[input]` packs into one element: 253, so any packing of them is
/// below the BN254 scalar modulus (just under 2²⁵⁴).
pub const PACK_BITS: u32 = 253;

/// Fields packed into one element in declaration order, the first in the lowest
/// bits, as `#[input]` packs a struct's consecutive narrow fields.
#[derive(Clone, Copy, Debug)]
pub struct Packer {
    out: Element,
    /// The next free bit.
    next: u32,
}

impl Packer {
    pub const fn new() -> Packer {
        Packer {
            out: [0; 32],
            next: 0,
        }
    }

    /// An unsigned value of `BITS` bits (at most 128).
    pub const fn uint<const BITS: u32>(self, v: u128) -> Packer {
        assert!(BITS >= 1 && BITS <= 128, "an integer is 1 to 128 bits");
        assert!(
            BITS == 128 || v >> BITS == 0,
            "the value doesn't fit its bits"
        );
        self.bits::<BITS>(&uint(v))
    }

    /// A signed value of `BITS` bits (at most 128), in two's complement.
    pub const fn int<const BITS: u32>(self, v: i128) -> Packer {
        assert!(BITS >= 1 && BITS <= 128, "an integer is 1 to 128 bits");
        assert!(
            BITS == 128 || (v >= -(1i128 << (BITS - 1)) && v < 1i128 << (BITS - 1)),
            "the value doesn't fit its bits"
        );
        self.bits::<BITS>(&int::<BITS>(v))
    }

    /// `true` or `false`: one bit.
    pub const fn bool(self, b: bool) -> Packer {
        self.uint::<1>(b as u128)
    }

    /// An element no wider than `BITS` bits (a set's bits, a `Text`), as is.
    pub const fn bits<const BITS: u32>(mut self, v: &Element) -> Packer {
        assert!(
            self.next + BITS <= PACK_BITS,
            "packed past the 253 bits of one element"
        );
        let mut i = 0;
        while i < 32 {
            assert!(
                (i as u32) * 8 < BITS || v[i] == 0,
                "the value doesn't fit its bits"
            );
            i += 1;
        }
        if !BITS.is_multiple_of(8) {
            assert!(
                v[(BITS / 8) as usize] >> (BITS % 8) == 0,
                "the value doesn't fit its bits"
            );
        }
        let (bytes, shift) = ((self.next / 8) as usize, self.next % 8);
        let mut i = 0;
        while i + bytes < 32 {
            self.out[i + bytes] |= v[i] << shift;
            if shift > 0 && i + bytes + 1 < 32 {
                self.out[i + bytes + 1] |= v[i] >> (8 - shift);
            }
            i += 1;
        }
        self.next += BITS;
        self
    }

    /// The packed element.
    pub const fn finish(self) -> Element {
        self.out
    }
}

impl Default for Packer {
    fn default() -> Packer {
        Packer::new()
    }
}

/// An unsigned integer as an element.
pub const fn uint(v: u128) -> Element {
    let mut out = [0u8; 32];
    let b = v.to_le_bytes();
    let mut i = 0;
    while i < 16 {
        out[i] = b[i];
        i += 1;
    }
    out
}

/// A signed integer as an element, in `BITS`-bit two's complement.
pub const fn int<const BITS: u32>(v: i128) -> Element {
    let v = v as u128;
    uint(if BITS >= 128 {
        v
    } else {
        v & ((1u128 << BITS) - 1)
    })
}

/// `len` bytes of `b` from `start`, read as a big-endian integer: one part of a
/// byte-encoded value (a `Hash`'s `hi` is `be(&hash, 0, 16)`).
pub const fn be(b: &[u8], start: usize, len: usize) -> Element {
    assert!(len <= 32, "an element holds at most 32 bytes");
    let mut out = [0u8; 32];
    let mut i = 0;
    while i < len {
        out[i] = b[start + len - 1 - i];
        i += 1;
    }
    out
}

/// An unsigned integer of `BITS` bits (1 to 128) that isn't a Rust integer's width,
/// as the circuit's `#[input]` types it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Uint<const BITS: u32>(u128);

impl<const BITS: u32> Uint<BITS> {
    /// The largest value.
    pub const MAX: Uint<BITS> = Uint(if BITS >= 128 {
        u128::MAX
    } else {
        (1 << BITS) - 1
    });

    /// `v`, or `None` past `BITS` bits.
    pub const fn new(v: u128) -> Option<Uint<BITS>> {
        if v <= Self::MAX.0 {
            Some(Uint(v))
        } else {
            None
        }
    }

    pub const fn get(self) -> u128 {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Packing is the integer `a | b << 17 | c << 34`, little-endian.
    #[test]
    fn packs_in_declaration_order() {
        let (a, b, c) = (46_335u128, 39_761u128, u64::MAX as u128);
        let packed = Packer::new()
            .uint::<17>(a)
            .uint::<17>(b)
            .uint::<64>(c)
            .finish();
        let want = a | b << 17 | c << 34;
        assert_eq!(packed, uint(want));
    }

    /// A field past byte 16, at an odd offset: a 249-bit set, then a bool.
    #[test]
    fn packs_wide_values_at_odd_offsets() {
        let mut set = [0u8; 32];
        set[0] = 0b1010_0001;
        set[31] = 0b1; // bit 248, the set's last
        let packed = Packer::new().bits::<249>(&set).bool(true).finish();
        let mut want = set;
        want[31] |= 1 << 1; // bit 249
        assert_eq!(packed, want);
        let shifted = Packer::new().uint::<3>(0b101).bits::<249>(&set).finish();
        assert_eq!(shifted[0], 0b0000_1101); // 0b101, then bit 0 of the set at bit 3
        assert_eq!(shifted[31], 0b1000); // the set's bit 248 at bit 251
    }

    #[test]
    fn signed_values_are_twos_complement() {
        assert_eq!(int::<32>(-1), uint(0xffff_ffff));
        assert_eq!(
            Packer::new().uint::<16>(7).int::<32>(-2).finish(),
            uint(7 | 0xffff_fffe << 16)
        );
    }

    #[test]
    #[should_panic(expected = "doesn't fit its bits")]
    fn a_value_too_wide_panics() {
        let _ = Packer::new().uint::<17>(1 << 17);
    }

    #[test]
    #[should_panic(expected = "past the 253 bits")]
    fn packing_past_one_element_panics() {
        let _ = Packer::new().uint::<128>(0).uint::<126>(0);
    }

    #[test]
    fn big_endian_parts() {
        let mut hash = [0u8; 32];
        for (i, b) in hash.iter_mut().enumerate() {
            *b = i as u8;
        }
        let hi = be(&hash, 0, 16);
        assert_eq!(hi[0], 15);
        assert_eq!(hi[15], 0);
        assert_eq!(hi[16..], [0; 16]);
        assert_eq!(be(&hash, 16, 16)[0], 31);
    }

    #[test]
    fn odd_width_integers() {
        assert_eq!(Uint::<17>::MAX.get(), 131_071);
        assert!(Uint::<17>::new(131_072).is_none());
        assert_eq!(Uint::<128>::MAX.get(), u128::MAX);
    }
}
