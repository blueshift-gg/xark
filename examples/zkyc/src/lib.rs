//! Zero-knowledge KYC: prove an identity an issuer committed to meets a verifier's
//! policy (old enough, wealthy enough, document still valid, nationality allowed)
//! without revealing it. The identity stays private; the commitment and the policy
//! are public, so a verifier picks the rules at proof time with no new circuit.
use xark::prelude::*;

/// What an issuer attests about a holder, committed to as a whole with Poseidon2.
#[input]
pub struct Identity {
    /// The ID document's number.
    pub document: Text,
    pub born: Date,
    /// An ISO 3166 code.
    pub nationality: Choice<Country>,
    /// Attested net worth, in the attestor's unit (its currency and scale).
    pub net_worth: u64,
    /// The ID document's expiry.
    pub expires: Date,
    /// The issuer's random blinding secret: it hides the commitment.
    pub salt: Field,
}

#[input]
impl Identity {
    /// The issuer's commitment: Poseidon2 over every field, so adding one extends it.
    pub fn commitment(&self) -> Field {
        xark_poseidon2::hash(self.to_fields())
    }
}

/// What a verifier requires, checked on `today`: a public input, so each verifier
/// picks its own rules with no new circuit.
///
/// ```ignore
/// Policy::default().on("2026-10-20").min_age(18).worth_at_least(500_000).nationalities([US, GB, FR, DE])
/// ```
#[input]
pub struct Policy {
    /// The day of the check: the document mustn't have expired by then.
    pub today: Date,
    /// The latest birth date allowed (a minimum age on `today`).
    pub born_by: Date,
    /// The least attested net worth allowed, in the attestor's unit.
    pub min_net_worth: u64,
    /// The nationalities allowed.
    pub allowed: Bitfield<Country>,
}

#[input]
impl Default for Policy {
    /// A policy every holder passes: no expiry, age, net worth or nationality check.
    /// Tighten it from there, starting with `on`.
    fn default() -> Policy {
        Policy {
            today: Date::MIN,
            born_by: Date::MAX,
            min_net_worth: 0,
            allowed: Bitfield::all(),
        }
    }
}

#[input]
impl Policy {
    /// Checked on `today`: the holder's document mustn't have expired by then.
    pub fn on(self, today: impl Into<Date>) -> Policy {
        Policy {
            today: today.into(),
            ..self
        }
    }

    /// At least `years` old on `today` (set it with `on` first).
    #[cfg(not(xark))]
    pub fn min_age(self, years: u16) -> Policy {
        assert!(
            self.today != Date::MIN,
            "a minimum age needs the day of the check: call `on(today)` first"
        );
        Policy {
            born_by: self.today.years_before(years),
            ..self
        }
    }

    /// Worth at least `amount`, in the attestor's unit.
    pub fn worth_at_least(self, amount: u64) -> Policy {
        Policy {
            min_net_worth: amount,
            ..self
        }
    }

    /// A national of one of `allowed` (a country, or a list of them).
    pub fn nationalities(self, allowed: impl Into<Bitfield<Country>>) -> Policy {
        Policy {
            allowed: allowed.into(),
            ..self
        }
    }
}

/// `id` is the identity the issuer committed to as `commitment`, and it meets
/// `policy`.
#[circuit]
pub fn zkyc(id: Private<Identity>, commitment: Public<Field>, policy: Public<Policy>) {
    require_eq(id.commitment(), commitment);
    require(id.born <= policy.born_by);
    require(id.net_worth >= policy.min_net_worth);
    require(id.expires >= policy.today);
    id.nationality.require_in(policy.allowed);
}

#[cfg(test)]
mod tests {
    use super::*;
    use Country::*;

    fn holder(nationality: Country, born: &str, net_worth: u64, expires: &str) -> Identity {
        Identity {
            document: "A1938274".into(),
            born: born.into(),
            nationality: nationality.into(),
            net_worth,
            expires: expires.into(),
            salt: Field::from_le_bytes(&[0x13; 31]),
        }
    }

    /// 18 or older, worth ≥ 500k, valid on 2026-10-20, from US/GB/FR/DE.
    fn policy() -> Policy {
        Policy::default()
            .on("2026-10-20")
            .min_age(18)
            .worth_at_least(500_000)
            .nationalities([US, GB, FR, DE])
    }

    fn check(id: Identity) -> Result<(), xark::prover::ProveError> {
        zkyc(id, id.commitment(), policy())
    }

    #[test]
    fn accepts_a_compliant_holder() {
        check(holder(US, "1990-01-01", 1_000_000, "2030-01-01")).unwrap();
        // Every limit inclusive: 18 today, exactly 500k, the document's last day.
        check(holder(GB, "2008-10-20", 500_000, "2026-10-20")).unwrap();
    }

    #[test]
    fn rejects_each_failed_check() {
        assert!(check(holder(KP, "1990-01-01", 1_000_000, "2030-01-01")).is_err());
        assert!(check(holder(US, "2008-10-21", 1_000_000, "2030-01-01")).is_err()); // 18 tomorrow
        assert!(check(holder(US, "1990-01-01", 100, "2030-01-01")).is_err());
        assert!(check(holder(US, "1990-01-01", 1_000_000, "2026-10-19")).is_err());
    }

    #[test]
    fn rejects_a_wrong_commitment() {
        let id = holder(US, "1990-01-01", 1_000_000, "2030-01-01");
        assert!(zkyc(id, 1, policy()).is_err());
    }

    #[test]
    fn checks_switch_off_without_a_new_circuit() {
        let id = holder(JP, "2025-01-01", 0, "2026-10-21");
        zkyc(id, id.commitment(), Policy::default().on("2026-10-20")).unwrap();
        // With no day either, not even an expired document is refused.
        let expired = holder(JP, "2025-01-01", 0, "2001-01-01");
        zkyc(expired, expired.commitment(), Policy::default()).unwrap();
    }

    #[test]
    #[should_panic(expected = "call `on(today)` first")]
    fn a_minimum_age_needs_the_day() {
        let _ = Policy::default().min_age(18);
    }
}
