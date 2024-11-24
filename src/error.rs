use thiserror::Error;

/// Crate specific Errors implementation.
#[derive(Debug, Error, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Error {
    /// Error parsing cron schedule pattern.
    #[error("invalid schedule pattern: {0}")]
    InvalidCronPattern(String),
    /// Invalid year value specified.
    #[error("invalid year value: {0}")]
    InvalidYearValue(String),
    /// Invalid hour value specified.
    #[error("invalid hour value: {0}")]
    InvalidHourValue(String),
    /// Invalid minute value specified.
    #[error("invalid minute value: {0}")]
    InvalidMinuteValue(String),
    /// Invalid second value specified.
    #[error("invalid second value: {0}")]
    InvalidSecondValue(String),
    /// Invalid day of month value specified.
    #[error("invalid day of month value: {0}")]
    InvalidDayOfMonthValue(String),
    /// Invalid month value specified.
    #[error("invalid month value: {0}")]
    InvalidMonthValue(String),
    /// Invalid day of week value specified.
    #[error("invalid day of week value: {0}")]
    InvalidDayOfWeekValue(String),
    /// Invalid range value specified.
    #[error("invalid range value: {0}")]
    InvalidRangeValue(String),
    /// Invalid repeating pattern specified.
    #[error("invalid repeating pattern: {0}")]
    InvalidRepeatingPattern(String),
}
