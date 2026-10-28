//! Times as circuit inputs: a [`Timestamp`] (Unix seconds, an `i64`) for any moment,
//! and a [`Time`] (whole steps over a range of years: [`Days`], minutes, …) for one
//! known to lie in a range, as an unsigned integer just wide enough for it.
//!
//! Both count from instants, not calendar fields, so leap years matter only when a
//! date is read or written (`"2024-02-29"`): two consecutive days are always one
//! `Days` step apart. Every day is 86,400 seconds, as Unix time, a JS `Date` and
//! Solana's `Clock` count them, and everything is UTC.
//!
//! ```ignore
//! #[input]
//! pub struct Identity { pub born: Days<1900, 2100>, /* … */ } // 17 bits
//! require(id.born <= policy.born_by);
//! ```

use core::cmp::Ordering;

use crate::input::{Encoding, Input, Layout, Named, Reader, Type, Writer};
use crate::lang::Field;

/// Seconds in a [`Time`] step: one second.
pub const SECOND: u32 = 1;
/// Seconds in a [`Time`] step: one minute.
pub const MINUTE: u32 = 60;
/// Seconds in a [`Time`] step: one hour.
pub const HOUR: u32 = 3_600;
/// Seconds in a [`Time`] step: one day ([`Days`]).
pub const DAY: u32 = 86_400;
/// Seconds in a [`Time`] step: one week (from the start of `FROM`, not a Monday).
pub const WEEK: u32 = 604_800;

/// Days from 1970-01-01 to `year-month-day` (proleptic Gregorian).
const fn days_from_civil(year: i64, month: u8, day: u8) -> i64 {
    let y = if month <= 2 { year - 1 } else { year };
    let era = y.div_euclid(400);
    let yoe = y - era * 400;
    let m = month as i64;
    let doy = (153 * (if m > 2 { m - 3 } else { m + 9 }) + 2) / 5 + day as i64 - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146_097 + doe - 719_468
}

/// Days in `month` of `year`.
const fn days_in_month(year: i64, month: u8) -> u8 {
    match month {
        2 if (year % 4 == 0 && year % 100 != 0) || year % 400 == 0 => 29,
        2 => 28,
        4 | 6 | 9 | 11 => 30,
        _ => 31,
    }
}

/// Midnight (UTC) of a real calendar day as Unix seconds, or `None`.
const fn midnight(year: u16, month: u8, day: u8) -> Option<i64> {
    if month < 1 || month > 12 || day < 1 || day > days_in_month(year as i64, month) {
        return None;
    }
    Some(days_from_civil(year as i64, month, day) * DAY as i64)
}

// ---- Timestamp -------------------------------------------------------------------

/// A moment: whole seconds since 1970-01-01T00:00:00Z (Unix time), an `i64`, as
/// Solana's `Clock::unix_timestamp` holds it and a JS `Date` gives it (its
/// milliseconds dropped). Compared with `<`, `<=`, `>`, `>=` and `==` as a signed
/// 64-bit integer.
///
/// A moment known to lie in a range of years is cheaper as a [`Time`] (a birth date
/// as [`Days<1900, 2100>`](Days): 17 bits instead of 64).
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct Timestamp(i64);

impl Timestamp {
    /// The earliest timestamp.
    pub const MIN: Timestamp = Timestamp(i64::MIN);
    /// The latest timestamp.
    pub const MAX: Timestamp = Timestamp(i64::MAX);

    /// The moment `seconds` after 1970-01-01T00:00:00Z (before it, when negative).
    pub const fn from_unix(seconds: i64) -> Timestamp {
        Timestamp(seconds)
    }

    /// Seconds since 1970-01-01T00:00:00Z.
    pub const fn unix(self) -> i64 {
        self.0
    }

    /// Midnight (UTC) of a real calendar day, checked: a bad literal in a `const` is a
    /// compile error, at run time a panic.
    pub const fn new(year: u16, month: u8, day: u8) -> Timestamp {
        match midnight(year, month, day) {
            Some(s) => Timestamp(s),
            None => panic!("no such day"),
        }
    }

    /// Midnight (UTC) of a real calendar day, or `None` (30 February, month 13).
    pub const fn checked(year: u16, month: u8, day: u8) -> Option<Timestamp> {
        match midnight(year, month, day) {
            Some(s) => Some(Timestamp(s)),
            None => None,
        }
    }

    /// This moment `seconds` later (earlier, when negative).
    pub const fn plus(self, seconds: i64) -> Timestamp {
        Timestamp(self.0 + seconds)
    }
}

/// `<`, `<=`, `>`, `>=`: a signed comparison, a `{0, 1}` circuit wire.
impl PartialOrd for Timestamp {
    fn partial_cmp(&self, other: &Timestamp) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
    fn lt(&self, other: &Timestamp) -> bool {
        self.0 < other.0
    }
    fn le(&self, other: &Timestamp) -> bool {
        self.0 <= other.0
    }
    fn gt(&self, other: &Timestamp) -> bool {
        self.0 > other.0
    }
    fn ge(&self, other: &Timestamp) -> bool {
        self.0 >= other.0
    }
}

impl Input for Timestamp {
    const TYPE: Type = Type::Named(
        &Type::named("Timestamp", Layout::Newtype(Type::Int(64))).encoded(Encoding::Timestamp),
    );
    fn read(r: &mut Reader<'_>) -> Self {
        Timestamp(r.read())
    }
    fn write(&self, w: &mut Writer<'_>) {
        w.write(&self.0)
    }
}

impl crate::RequireEqCircuit<Timestamp> for Timestamp {
    #[inline]
    #[cfg_attr(not(xark), track_caller)]
    fn require_eq_circuit(self, rhs: Timestamp) {
        crate::lang::__xark_require_eq_scalar(Field::from(self.0 as u64), Field::from(rhs.0 as u64))
    }
}

// ---- Time -----------------------------------------------------------------------

/// A moment from the start of year `FROM` to the end of year `TO` (UTC), in whole
/// `UNIT`-second steps ([`SECOND`], [`MINUTE`], [`HOUR`], [`DAY`], [`WEEK`]): in the
/// circuit an unsigned integer of [`Time::BITS`] bits, just enough for the range,
/// range-checked on entry and compared at that width. [`Days`] is the usual one:
/// `Days<1900, 2100>` is 73,414 days, 17 bits.
///
/// A moment inside a step is that step (`from_unix` rounds down, as Unix time
/// does), so a day is any time on it: a JS `new Date()` is today. A moment outside
/// the range isn't a `Time` of it: [`Time::from_unix`] gives `None`, and a client
/// refuses it.
///
/// Values of one `Time` type compare with `<`, `<=`, `>`, `>=` and `==`; a
/// [`Timestamp`] converts with [`Time::from_timestamp`] (off the circuit: in a
/// client, or a program building public inputs from `Clock`).
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct Time<const UNIT: u32, const FROM: u16, const TO: u16>(u64);

/// A day from the start of year `FROM` to the end of year `TO` (UTC): a
/// [`Time`] in steps of a [`DAY`].
pub type Days<const FROM: u16, const TO: u16> = Time<DAY, FROM, TO>;

impl<const UNIT: u32, const FROM: u16, const TO: u16> Time<UNIT, FROM, TO> {
    /// The first moment, as Unix seconds: the start of `FROM`.
    pub const START: i64 = {
        assert!(UNIT > 0, "a Time's UNIT must be at least a second");
        assert!(
            FROM <= TO,
            "a Time's FROM year must not be after its TO year"
        );
        days_from_civil(FROM as i64, 1, 1) * DAY as i64
    };
    /// The end of `TO`, as Unix seconds (the start of the year after it).
    const END: i64 = days_from_civil(TO as i64 + 1, 1, 1) * DAY as i64;
    /// How many steps the range holds (the last may run past `TO`).
    pub const STEPS: u64 = ((Self::END - Self::START - 1) / UNIT as i64 + 1) as u64;
    /// The width of a value in the circuit: enough bits for every step.
    pub const BITS: u32 = {
        let last = Self::STEPS - 1;
        let bits = if last == 0 {
            1
        } else {
            64 - last.leading_zeros()
        };
        assert!(bits <= 64);
        bits
    };
    /// The first step: the start of `FROM`.
    pub const MIN: Self = Time(0);
    /// The last step: the one holding the end of `TO`.
    pub const MAX: Self = Time(Self::STEPS - 1);

    /// The step holding the moment `seconds` after 1970-01-01T00:00:00Z, or `None`
    /// outside the range.
    pub const fn from_unix(seconds: i64) -> Option<Self> {
        if seconds < Self::START || seconds >= Self::END {
            return None;
        }
        Some(Time(((seconds - Self::START) / UNIT as i64) as u64))
    }

    /// The step holding `t`, or `None` outside the range.
    pub const fn from_timestamp(t: Timestamp) -> Option<Self> {
        Self::from_unix(t.0)
    }

    /// The step holding midnight (UTC) of a real calendar day in the range, checked:
    /// a bad literal in a `const` is a compile error, at run time a panic.
    pub const fn new(year: u16, month: u8, day: u8) -> Self {
        match Self::checked(year, month, day) {
            Some(t) => t,
            None => panic!("no such day in this Time's range"),
        }
    }

    /// The step holding midnight (UTC) of a calendar day, or `None` (not a day, or
    /// outside the range).
    pub const fn checked(year: u16, month: u8, day: u8) -> Option<Self> {
        match midnight(year, month, day) {
            Some(s) => Self::from_unix(s),
            None => None,
        }
    }

    /// The `n`-th step from the start of `FROM`, or `None` past the last.
    pub const fn from_steps(n: u64) -> Option<Self> {
        if n < Self::STEPS { Some(Time(n)) } else { None }
    }

    /// Steps since the start of `FROM`: the value the circuit holds.
    pub const fn steps(self) -> u64 {
        self.0
    }

    /// The step's first moment, as Unix seconds.
    pub const fn unix(self) -> i64 {
        Self::START + self.0 as i64 * UNIT as i64
    }

    /// The step's first moment.
    pub const fn timestamp(self) -> Timestamp {
        Timestamp(self.unix())
    }
}

/// `<`, `<=`, `>`, `>=`: an unsigned comparison at [`Time::BITS`] bits, a `{0, 1}`
/// circuit wire.
impl<const UNIT: u32, const FROM: u16, const TO: u16> PartialOrd for Time<UNIT, FROM, TO> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
    fn lt(&self, other: &Self) -> bool {
        self.0 < other.0
    }
    fn le(&self, other: &Self) -> bool {
        self.0 <= other.0
    }
    fn gt(&self, other: &Self) -> bool {
        self.0 > other.0
    }
    fn ge(&self, other: &Self) -> bool {
        self.0 >= other.0
    }
}

impl<const UNIT: u32, const FROM: u16, const TO: u16> From<Time<UNIT, FROM, TO>> for Timestamp {
    fn from(t: Time<UNIT, FROM, TO>) -> Timestamp {
        t.timestamp()
    }
}

impl<const UNIT: u32, const FROM: u16, const TO: u16> Input for Time<UNIT, FROM, TO> {
    const TYPE: Type = Type::Named(&Named {
        name: "Time",
        arg: None,
        layout: Layout::Newtype(Type::Uint(Self::BITS)),
        encoding: Encoding::Time {
            unit: UNIT,
            from: FROM,
            to: TO,
        },
    });
    fn read(r: &mut Reader<'_>) -> Self {
        Time(r.uint(Self::BITS))
    }
    fn write(&self, w: &mut Writer<'_>) {
        w.field(Field::from(self.0))
    }
}

impl<const UNIT: u32, const FROM: u16, const TO: u16> crate::RequireEqCircuit<Self>
    for Time<UNIT, FROM, TO>
{
    #[inline]
    #[cfg_attr(not(xark), track_caller)]
    fn require_eq_circuit(self, rhs: Self) {
        crate::lang::__xark_require_eq_scalar(Field::from(self.0), Field::from(rhs.0))
    }
}

// In the circuit build `Debug` only has to exist (a derived `Debug` on a struct of
// these compiles there too); the host's renders the moment.
#[cfg(xark)]
mod circuit_debug {
    use core::fmt;

    use super::*;

    impl fmt::Debug for Timestamp {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "Timestamp({})", self.0)
        }
    }
    impl<const UNIT: u32, const FROM: u16, const TO: u16> fmt::Debug for Time<UNIT, FROM, TO> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "Time({})", self.0)
        }
    }
}

#[cfg(not(xark))]
mod host {
    use alloc::format;
    use core::fmt;

    use xark_schema::time;

    use super::*;
    use crate::types::InvalidValue;

    impl Timestamp {
        /// `"YYYY-MM-DD"` (midnight UTC), or an ISO 8601 date-time with a zone
        /// (`"2026-10-20T09:30:00Z"`, `…+01:00`); a fraction of a second rounds down.
        pub fn parse(s: &str) -> Result<Timestamp, InvalidValue> {
            time::parse(s).map(Timestamp).map_err(InvalidValue)
        }

        /// The calendar day it falls on (UTC): `(year, month, day)`.
        pub fn date(self) -> (i64, u8, u8) {
            let (y, m, d) = time::civil_from_days(self.0.div_euclid(time::DAY));
            (y, m as u8, d as u8)
        }

        /// The same moment `years` earlier: the same day and time of day, 29 February
        /// becoming the 28th in a common year (the latest birth of someone `years` old
        /// at this moment). Panics before year 0.
        pub fn years_before(self, years: u16) -> Timestamp {
            let (y, m, d) = self.date();
            let y = y - years as i64;
            assert!(y >= 0, "{years} years before {self:?} is before year 0");
            let d = d.min(time::days_in_month(y, m as u32) as u8);
            let day = time::days_from_civil(y, m as u32, d as u32);
            Timestamp(day * time::DAY + self.0.rem_euclid(time::DAY))
        }
    }

    /// As [`Timestamp::parse`].
    impl core::str::FromStr for Timestamp {
        type Err = InvalidValue;
        fn from_str(s: &str) -> Result<Timestamp, InvalidValue> {
            Timestamp::parse(s)
        }
    }

    /// As [`Timestamp::parse`]. Panics on anything else: for literals in tests
    /// (`"1990-01-01".into()`); parse input you didn't write.
    impl From<&str> for Timestamp {
        fn from(s: &str) -> Timestamp {
            Timestamp::parse(s).unwrap_or_else(|e| panic!("{e}"))
        }
    }

    impl From<(u16, u8, u8)> for Timestamp {
        fn from((y, m, d): (u16, u8, u8)) -> Timestamp {
            Timestamp::new(y, m, d)
        }
    }

    impl fmt::Debug for Timestamp {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "Timestamp({})", time::format(self.0, false))
        }
    }

    impl<const UNIT: u32, const FROM: u16, const TO: u16> Time<UNIT, FROM, TO> {
        /// A date or date-time, as [`Timestamp::parse`], in the range: the step
        /// holding it.
        pub fn parse(s: &str) -> Result<Self, InvalidValue> {
            Self::try_from(Timestamp::parse(s)?)
        }

        /// The calendar day the step starts on (UTC): `(year, month, day)`.
        pub fn date(self) -> (i64, u8, u8) {
            self.timestamp().date()
        }

        /// The step holding the same moment `years` earlier (as
        /// [`Timestamp::years_before`]). Panics before the range starts.
        pub fn years_before(self, years: u16) -> Self {
            let t = self.timestamp().years_before(years);
            Self::from_timestamp(t).unwrap_or_else(|| {
                panic!("{years} years before {self:?} is before the start of {FROM}")
            })
        }
    }

    /// The step holding a timestamp, or why it's outside the range.
    impl<const UNIT: u32, const FROM: u16, const TO: u16> TryFrom<Timestamp> for Time<UNIT, FROM, TO> {
        type Error = InvalidValue;
        fn try_from(t: Timestamp) -> Result<Self, InvalidValue> {
            Self::from_timestamp(t).ok_or_else(|| {
                InvalidValue(format!(
                    "{} is outside {FROM}-01-01 to {TO}-12-31",
                    time::format(t.0, UNIT.is_multiple_of(DAY))
                ))
            })
        }
    }

    /// As [`Time::parse`].
    impl<const UNIT: u32, const FROM: u16, const TO: u16> core::str::FromStr for Time<UNIT, FROM, TO> {
        type Err = InvalidValue;
        fn from_str(s: &str) -> Result<Self, InvalidValue> {
            Self::parse(s)
        }
    }

    /// As [`Time::parse`]. Panics on anything else: for literals in tests
    /// (`"1990-01-01".into()`); parse input you didn't write.
    impl<const UNIT: u32, const FROM: u16, const TO: u16> From<&str> for Time<UNIT, FROM, TO> {
        fn from(s: &str) -> Self {
            Self::parse(s).unwrap_or_else(|e| panic!("{e}"))
        }
    }

    impl<const UNIT: u32, const FROM: u16, const TO: u16> From<(u16, u8, u8)> for Time<UNIT, FROM, TO> {
        fn from((y, m, d): (u16, u8, u8)) -> Self {
            Self::new(y, m, d)
        }
    }

    impl<const UNIT: u32, const FROM: u16, const TO: u16> fmt::Debug for Time<UNIT, FROM, TO> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let at = time::format(self.unix(), UNIT.is_multiple_of(DAY));
            if UNIT == DAY {
                write!(f, "Days<{FROM}, {TO}>({at})")
            } else {
                write!(f, "Time<{UNIT}, {FROM}, {TO}>({at})")
            }
        }
    }
}

#[cfg(all(test, not(xark)))]
mod tests {
    use super::*;

    type Born = Days<1900, 2100>;

    #[test]
    fn widths_follow_the_range() {
        assert_eq!((Born::STEPS, Born::BITS), (73_414, 17));
        assert_eq!(<Days<1950, 2100>>::BITS, 16);
        assert_eq!(<Days<1900, 9999>>::STEPS, 2_958_464);
        assert_eq!(<Days<1900, 9999>>::BITS, 22);
        assert_eq!(<Days<2024, 2024>>::STEPS, 366);
        assert_eq!(<Time<SECOND, 1970, 1970>>::STEPS, 365 * 86_400);
        assert_eq!(<Time<WEEK, 2024, 2024>>::STEPS, 53); // the last week runs into 2025
        assert_eq!(
            Born::TYPE,
            Type::Named(&Named {
                name: "Time",
                arg: None,
                layout: Layout::Newtype(Type::Uint(17)),
                encoding: Encoding::Time {
                    unit: DAY,
                    from: 1900,
                    to: 2100
                },
            })
        );
    }

    #[test]
    fn steps_round_down_and_stay_in_range() {
        let d = Born::new(1990, 1, 1);
        assert_eq!(d.unix(), Timestamp::new(1990, 1, 1).unix());
        assert_eq!(d.steps() as i64, (d.unix() - Born::START) / 86_400);
        // Any moment of the day is that day.
        let noon = Timestamp::parse("1990-01-01T12:00:00Z").unwrap();
        assert!(Born::from_timestamp(noon) == Some(d));
        assert!(Born::from_unix(d.unix() - 1) == Some(Born::new(1989, 12, 31)));
        // Leap days are days: 29 February 2024 sits between the 28th and 1 March.
        let leap = Born::new(2024, 2, 29).steps();
        assert_eq!(
            (
                Born::new(2024, 2, 28).steps(),
                Born::new(2024, 3, 1).steps()
            ),
            (leap - 1, leap + 1)
        );
        assert!(Born::checked(2023, 2, 29).is_none());
        // The ends.
        assert_eq!(Born::MIN.date(), (1900, 1, 1));
        assert_eq!(Born::MAX.date(), (2100, 12, 31));
        assert!(Born::checked(1899, 12, 31).is_none() && Born::checked(2101, 1, 1).is_none());
        assert_eq!(
            alloc::format!("{}", Born::parse("2101-01-01").unwrap_err()),
            "2101-01-01 is outside 1900-01-01 to 2100-12-31"
        );
        assert_eq!(alloc::format!("{d:?}"), "Days<1900, 2100>(1990-01-01)");
    }

    #[test]
    fn timestamps() {
        assert_eq!(Timestamp::new(1970, 1, 1).unix(), 0);
        assert_eq!(Timestamp::new(1969, 12, 31).unix(), -86_400);
        assert!(Timestamp::from("1969-12-31") < Timestamp::from_unix(0));
        let t = Timestamp::parse("2024-02-29T08:00:00Z").unwrap();
        assert_eq!(alloc::format!("{t:?}"), "Timestamp(2024-02-29T08:00:00Z)");
        assert_eq!(
            alloc::format!("{:?}", t.years_before(1)),
            "Timestamp(2023-02-28T08:00:00Z)"
        );
        assert_eq!(t.years_before(4).date(), (2020, 2, 29));
        // The first of every month, and of the range.
        for m in 1..=12 {
            assert_eq!(
                Timestamp::new(2024, m, 1).years_before(18).date(),
                (2006, m, 1)
            );
            assert_eq!(
                Days::<1900, 2100>::new(2024, m, 1).years_before(18).date(),
                (2006, m, 1)
            );
        }
        assert_eq!(
            Days::<1900, 2100>::new(2000, 1, 1).years_before(100),
            Days::MIN
        );
        // The calendar here agrees with the one clients parse with.
        for (y, m, d) in [
            (0u16, 1u8, 1u8),
            (1900, 3, 1),
            (2000, 2, 29),
            (9999, 12, 31),
        ] {
            assert_eq!(
                Timestamp::new(y, m, d).unix(),
                xark_schema::time::days_from_civil(y as i64, m as u32, d as u32) * 86_400
            );
        }
    }

    #[test]
    #[should_panic(expected = "no such day")]
    fn february_30_is_refused() {
        let _ = Timestamp::new(2023, 2, 30);
    }
}
