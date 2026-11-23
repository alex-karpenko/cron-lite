//! Helpers shared by unit tests of several modules.

use jiff::{civil, fmt::strtime, tz::TimeZone, ZonedDateTime};

/// Parses an RFC 3339 timestamp (`Z` or a numeric offset) into a fixed-offset [`ZonedDateTime`].
pub(crate) fn parse_rfc3339(input: &str) -> Result<ZonedDateTime, jiff::Error> {
    let normalized = if let Some(prefix) = input.strip_suffix('Z') {
        format!("{prefix}+00:00")
    } else {
        input.to_string()
    };
    strtime::parse("%Y-%m-%dT%H:%M:%S%.f%:z", &normalized)?.to_zoned_datetime()
}

/// Formats a [`ZonedDateTime`] as an RFC 3339 timestamp with a numeric offset, without fractional seconds.
pub(crate) fn format_rfc3339(value: &ZonedDateTime) -> String {
    strtime::format("%Y-%m-%dT%H:%M:%S%:z", value).unwrap()
}

/// Builds a [`ZonedDateTime`] in UTC.
pub(crate) fn utc(
    year: i16,
    month: i8,
    day: i8,
    hour: i8,
    minute: i8,
    second: i8,
) -> Result<ZonedDateTime, jiff::Error> {
    civil::date(year, month, day)
        .at(hour, minute, second, 0)
        .to_zoned_datetime(TimeZone::UTC)
}

/// Builds a [`ZonedDateTime`] in the named timezone; ambiguous local times resolve to the earlier occurrence.
pub(crate) fn zoned(
    year: i16,
    month: i8,
    day: i8,
    hour: i8,
    minute: i8,
    second: i8,
    tz: &str,
) -> Result<ZonedDateTime, jiff::Error> {
    civil::date(year, month, day).at(hour, minute, second, 0).in_tz(tz)
}
