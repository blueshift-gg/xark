//! A circuit over another circuit's input: prove the holder of a `zkyc` identity
//! commitment is a national of an allowed country, and nothing else. `zkyc` is an
//! ordinary dependency: its `Identity` and `commitment()` are reused as they are,
//! so a commitment an issuer made for `zkyc` works here unchanged. Only this
//! crate's `#[circuit]` is the entry; `zkyc`'s is an ordinary item here.
use xark::prelude::*;
use zkyc::Identity;

/// `id` is the identity the issuer committed to as `commitment`, and its
/// nationality is one of `allowed`.
#[circuit]
pub fn zkyc_nationality(
    id: Private<Identity>,
    commitment: Public<Field>,
    allowed: Public<Bitfield<Country>>,
) {
    require_eq(id.commitment(), commitment);
    id.nationality.require_in(allowed);
}

#[cfg(test)]
mod tests {
    use super::*;
    use Country::*;

    fn holder(nationality: Country) -> Identity {
        Identity {
            document: "A1938274".into(),
            born: "1990-01-01".into(),
            nationality: nationality.into(),
            net_worth: 1_000_000,
            expires: "2030-01-01".into(),
            salt: Field::from_le_bytes(&[0x13; 31]),
        }
    }

    #[test]
    fn accepts_an_allowed_nationality() {
        let id = holder(FR);
        zkyc_nationality(id, id.commitment(), [US, GB, FR, DE]).unwrap();
    }

    #[test]
    fn rejects_another_nationality() {
        let id = holder(JP);
        assert!(zkyc_nationality(id, id.commitment(), [US, GB, FR, DE]).is_err());
    }

    /// The whole pipeline: a Groth16 proof (on throwaway keys) that verifies.
    #[test]
    fn proves() {
        let id = holder(FR);
        xark::prover::circuit("zkyc_nationality")
            .prove_dev(ZkycNationalityInputs {
                id,
                commitment: id.commitment(),
                allowed: [US, GB, FR, DE].into(),
            })
            .unwrap();
    }

    #[test]
    fn rejects_another_identity() {
        let id = holder(FR);
        let other = Identity { net_worth: 1, ..id };
        assert!(zkyc_nationality(id, other.commitment(), [US, GB, FR, DE]).is_err());
    }
}
