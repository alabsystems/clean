// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Record age in whole days. Age is displayed and never decides freshness.

use std::time::{SystemTime, UNIX_EPOCH};

/// Days since 1970-01-01 of a proleptic Gregorian date (Howard Hinnant's
/// `days_from_civil`).
fn days_from_civil(year: i64, month: i64, day: i64) -> i64 {
    let year = if month <= 2 { year - 1 } else { year };
    let era = year.div_euclid(400);
    let year_of_era = year - era * 400;
    let month_index = (month + 9) % 12;
    let day_of_year = (153 * month_index + 2) / 5 + day - 1;
    let day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
    era * 146_097 + day_of_era - 719_468
}

/// Days since the epoch of a text that starts with `YYYY-MM-DD`.
pub(super) fn epoch_day(text: &str) -> Option<i64> {
    let date = text.get(..10)?;
    let mut parts = date.split('-');
    let (year, month, day) = (parts.next()?, parts.next()?, parts.next()?);
    if year.len() != 4 || month.len() != 2 || day.len() != 2 {
        return None;
    }
    let (year, month, day): (i64, i64, i64) =
        (year.parse().ok()?, month.parse().ok()?, day.parse().ok()?);
    if !(1..=12).contains(&month) || !(1..=31).contains(&day) {
        return None;
    }
    Some(days_from_civil(year, month, day))
}

/// Whole days from the recorded date to today (UTC).
pub(super) fn age_days(recorded: &str) -> Option<i64> {
    let today = SystemTime::now().duration_since(UNIX_EPOCH).ok()?.as_secs() / 86_400;
    Some(i64::try_from(today).ok()? - epoch_day(recorded)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_epoch_day_known_dates_match() {
        assert_eq!(epoch_day("1970-01-01"), Some(0));
        assert_eq!(epoch_day("2000-03-01"), Some(11_017));
        assert_eq!(epoch_day("2026-11-15T22:23:17Z"), Some(20_772));
    }

    #[test]
    fn test_epoch_day_malformed_text_is_none() {
        for text in ["", "2026-1-15", "2026-13-01", "not a date", "20261115"] {
            assert_eq!(epoch_day(text), None, "{text}");
        }
    }
}
