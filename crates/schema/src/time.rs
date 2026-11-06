//! Calendar times as Unix seconds (UTC), for the time encodings: reading
//! `"YYYY-MM-DD"` and ISO 8601 date-times, and writing them back. Proleptic Gregorian
//! (a leap year every 4, except centuries not divisible by 400), and every day 86,400
//! seconds, as Unix time, a JS `Date` and Solana's `Clock` count them.

/// Seconds in a day.
pub const DAY: i64 = 86_400;

/// Days from 1970-01-01 to `year-month-day` (negative before it).
pub fn days_from_civil(year: i64, month: u32, day: u32) -> i64 {
    let y = if month <= 2 { year - 1 } else { year };
    let era = y.div_euclid(400);
    let yoe = y - era * 400;
    let m = month as i64;
    let doy = (153 * (if m > 2 { m - 3 } else { m + 9 }) + 2) / 5 + day as i64 - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146_097 + doe - 719_468
}

/// The `(year, month, day)` of day `days` since 1970-01-01.
pub fn civil_from_days(days: i64) -> (i64, u32, u32) {
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let month = if mp < 10 { mp + 3 } else { mp - 9 } as u32;
    let year = yoe + era * 400 + i64::from(month <= 2);
    (year, month, day)
}

/// Days in `month` of `year`.
pub fn days_in_month(year: i64, month: u32) -> u32 {
    match month {
        2 if (year % 4 == 0 && year % 100 != 0) || year % 400 == 0 => 29,
        2 => 28,
        4 | 6 | 9 | 11 => 30,
        _ => 31,
    }
}

/// `"YYYY-MM-DD"` (midnight UTC), or an ISO 8601 date-time with a zone:
/// `"YYYY-MM-DDTHH:MM[:SS[.fff]]Z"` or `…+HH:MM` / `…-HH:MM`, as Unix seconds. A
/// fraction of a second rounds down, as Unix time does.
pub fn parse(s: &str) -> Result<i64, String> {
    let bad = || format!("`{s}` is not a YYYY-MM-DD date or an ISO 8601 date-time");
    let num = |t: &str| -> Option<i64> {
        (!t.is_empty() && t.bytes().all(|b| b.is_ascii_digit()))
            .then(|| t.parse().ok())
            .flatten()
    };
    let t = s.trim();
    let (date, time) = match t.split_once(['T', 't']) {
        Some((d, rest)) => (d, Some(rest)),
        None => (t, None),
    };
    let mut parts = date.split('-');
    let (y, m, d) = match (parts.next(), parts.next(), parts.next(), parts.next()) {
        (Some(y), Some(m), Some(d), None) if y.len() == 4 && m.len() == 2 && d.len() == 2 => (
            num(y).ok_or_else(bad)?,
            num(m).ok_or_else(bad)?,
            num(d).ok_or_else(bad)?,
        ),
        _ => return Err(bad()),
    };
    if !(1..=12).contains(&m) || d < 1 || d > days_in_month(y, m as u32) as i64 {
        return Err(format!("`{s}` is not a calendar day"));
    }
    let midnight = days_from_civil(y, m as u32, d as u32) * DAY;
    let Some(time) = time else {
        return Ok(midnight);
    };
    // The zone: `Z`, or `±HH:MM`.
    let (clock, offset) = if let Some(c) = time.strip_suffix(['Z', 'z']) {
        (c, 0)
    } else if let Some(i) = time.rfind(['+', '-']) {
        let (c, z) = time.split_at(i);
        let sign = if z.starts_with('-') { -1 } else { 1 };
        let (h, mi) = z[1..].split_once(':').ok_or_else(bad)?;
        let (h, mi) = (num(h).ok_or_else(bad)?, num(mi).ok_or_else(bad)?);
        if h.to_string().len() > 2 || h > 23 || mi > 59 {
            return Err(bad());
        }
        (c, sign * (h * 3600 + mi * 60))
    } else {
        return Err(format!(
            "`{s}` has no time zone: end it with `Z` for UTC (or an offset like `+01:00`)"
        ));
    };
    let (clock, _fraction) = match clock.split_once('.') {
        Some((c, f)) if num(f).is_some() => (c, f),
        Some(_) => return Err(bad()),
        None => (clock, ""),
    };
    let hms: Vec<&str> = clock.split(':').collect();
    if !(2..=3).contains(&hms.len()) || hms.iter().any(|p| p.len() != 2) {
        return Err(bad());
    }
    let h = num(hms[0]).ok_or_else(bad)?;
    let mi = num(hms[1]).ok_or_else(bad)?;
    let sec = hms.get(2).map_or(Some(0), |x| num(x)).ok_or_else(bad)?;
    if h > 23 || mi > 59 || sec > 59 {
        return Err(format!("`{s}` is not a time of day"));
    }
    Ok(midnight + h * 3600 + mi * 60 + sec - offset)
}

/// Unix seconds as `"YYYY-MM-DDTHH:MM:SSZ"`, or `"YYYY-MM-DD"` when `date_only`
/// (the day it falls on). Outside years 0 to 9999, which ISO 8601 can't write
/// without an agreement, the seconds as a decimal string.
pub fn format(seconds: i64, date_only: bool) -> String {
    let (days, secs) = (seconds.div_euclid(DAY), seconds.rem_euclid(DAY));
    let (y, m, d) = civil_from_days(days);
    if !(0..=9999).contains(&y) {
        return seconds.to_string();
    }
    if date_only {
        return format!("{y:04}-{m:02}-{d:02}");
    }
    let (h, mi, s) = (secs / 3600, secs / 60 % 60, secs % 60);
    format!("{y:04}-{m:02}-{d:02}T{h:02}:{mi:02}:{s:02}Z")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn calendar_round_trips() {
        assert_eq!(days_from_civil(1970, 1, 1), 0);
        assert_eq!(days_from_civil(2000, 3, 1), 11_017);
        assert_eq!(days_from_civil(1900, 1, 1), -25_567);
        assert_eq!(days_from_civil(0, 1, 1), -719_528);
        // Every day from year 0 to 10000 and back, each the day after the one before.
        let mut prev = days_from_civil(0, 1, 1) - 1;
        for y in 0..=10_000 {
            for m in 1..=12 {
                for d in 1..=days_in_month(y, m) {
                    let n = days_from_civil(y, m, d);
                    assert_eq!(n, prev + 1, "{y}-{m}-{d}");
                    assert_eq!(civil_from_days(n), (y, m, d));
                    prev = n;
                }
            }
        }
        // Leap years: 2000 is one, 1900 and 2100 aren't.
        assert_eq!((days_in_month(2000, 2), days_in_month(1900, 2)), (29, 28));
        assert_eq!((days_in_month(2100, 2), days_in_month(2024, 2)), (28, 29));
    }

    #[test]
    fn parses_dates_and_date_times() {
        assert_eq!(parse("1970-01-01"), Ok(0));
        assert_eq!(parse("1969-12-31"), Ok(-DAY));
        assert_eq!(parse("2024-02-29"), Ok(days_from_civil(2024, 2, 29) * DAY));
        assert_eq!(parse("1970-01-01T00:00:01Z"), Ok(1));
        assert_eq!(parse("1970-01-01T01:00Z"), Ok(3600));
        assert_eq!(parse("1970-01-01T00:00:00.999Z"), Ok(0));
        assert_eq!(parse("1970-01-01T01:00:00+01:00"), Ok(0));
        assert_eq!(parse("1969-12-31T23:00:00-01:00"), Ok(0));
        for (s, why) in [
            ("2023-02-29", "not a calendar day"),
            ("2024-13-01", "not a calendar day"),
            ("1990-1-1", "is not a YYYY-MM-DD date"),
            ("1970-01-01T00:00:00", "no time zone"),
            ("1970-01-01T24:00:00Z", "not a time of day"),
            ("1970-01-01T00:00:60Z", "not a time of day"),
            ("soon", "is not a YYYY-MM-DD date"),
        ] {
            assert!(parse(s).unwrap_err().contains(why), "{s}: {:?}", parse(s));
        }
    }

    #[test]
    fn formats_back() {
        assert_eq!(format(0, false), "1970-01-01T00:00:00Z");
        assert_eq!(format(-1, false), "1969-12-31T23:59:59Z");
        assert_eq!(format(-1, true), "1969-12-31");
        assert_eq!(format(i64::MAX, false), i64::MAX.to_string());
        for s in [
            "2024-02-29T12:34:56Z",
            "0000-01-01T00:00:00Z",
            "9999-12-31T23:59:59Z",
        ] {
            assert_eq!(format(parse(s).unwrap(), false), s);
        }
    }
}
