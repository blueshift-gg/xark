#![cfg_attr(xark, no_std)]
#[cfg(test)]
mod poseidon2;
use xark::prelude::*;

#[derive(Clone, Debug, CircuitInput)]
pub struct ZKID {
    id: Field,      // an ID encoded as a field element
    dob: Field,     // a DOB as an integer (e.g. YYYYMMDD), < 2^25
    country: Field, // a country code
    nonce: Field,   // a blinding secret from the issuer
}

impl ZKID {
    /// The full Poseidon2 commitment over every field.
    pub fn hash(&self) -> Field {
        xark_poseidon2::hash([self.id, self.dob, self.country, self.nonce])
    }
}

/// Proves a KYCed ID holder is old enough without revealing their identity.
///
/// The prover holds a private identity `(id, dob, country, nonce)` the issuer committed
/// to with a public Poseidon2 `commitment`. The circuit re-derives the commitment and
/// constrains it to match, then constrains `dob < max_dob` (born before the public
/// cutoff). The identity stays hidden; only `max_dob` and `commitment` are revealed.
#[circuit]
pub fn zk_kyc(user: Private<ZKID>, max_dob: Public<Field>, commitment: Public<Field>) {
    require_eq(user.hash(), commitment);
    require(user.dob.lt::<25>(max_dob)); // dob < max_dob, compared as 25-bit unsigned
}

#[cfg(test)]
mod tests {
    use super::{poseidon2, zk_kyc, ZKID};
    use xark::Field;

    // The fixed identity fields as circuit `Field`s, packed at compile time.
    const ID: Field = Field::from_le_bytes("A1938274".as_bytes());
    const COUNTRY: Field = Field::from_u16(u16::from_le_bytes(*b"US"));
    const NONCE: Field = Field::from_le_bytes(&[
        0x13, 0x37, 0xaf, 0x10, 0x15, 0x0b, 0xa5, 0xed, //
        0x13, 0x37, 0xaf, 0x10, 0x15, 0x0b, 0xa5, 0xed, //
        0x13, 0x37, 0xaf, 0x10, 0x15, 0x0b, 0xa5, 0xed, //
        0x13, 0x37, 0xaf, 0x10, 0x15, 0x0b, 0xa5, 0xed,
    ]);
    const DOB: Field = Field::from_u64(19900101);
    const MAX_DOB: Field = Field::from_u64(20200101);

    // The identity with a given `dob`, sharing the fixed id/country/nonce.
    fn user(dob: Field) -> ZKID {
        ZKID {
            id: ID,
            dob,
            country: COUNTRY,
            nonce: NONCE,
        }
    }

    // The issuer's off-circuit Poseidon2 commitment over that identity — `Field`s pass
    // straight in (the reference reduces each mod p, as the solver does).
    fn commitment(dob: Field) -> String {
        poseidon2::hash([ID, dob, COUNTRY, NONCE])
    }

    #[test]
    fn accepts_valid() {
        zk_kyc(user(DOB), MAX_DOB.to_decimal(), commitment(DOB)).unwrap();
    }

    #[test]
    fn rejects_too_young() {
        // dob == MAX_DOB violates the strict `dob < MAX_DOB` (commitment is valid).
        assert!(zk_kyc(user(MAX_DOB), MAX_DOB.to_decimal(), commitment(MAX_DOB)).is_err());
    }

    #[test]
    fn rejects_wrong_hash() {
        assert!(zk_kyc(user(DOB), MAX_DOB.to_decimal(), "1".to_string()).is_err());
    }
}
