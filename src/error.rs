use std::fmt::Display;

/// Crate specific Error implementation.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Error {
    /// Invalid cron schedule.
    InvalidCronSchedule(String),
    /// Invalid day of month/week values.
    InvalidDaysPattern(String),
    /// Error parsing cron pattern.
    InvalidCronPattern(String),
    /// Invalid digital value.
    InvalidDigitalValue(String),
    /// Invalid mnemonic value.
    InvalidMnemonicValue(String),
    /// Invalid day of the week.
    InvalidDayOfWeekValue(String),
    /// Invalid range pattern.
    InvalidRangeValue(String),
    /// Invalid repeating pattern.
    InvalidRepeatingPattern(String),
}

impl std::error::Error for Error {}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::InvalidCronSchedule(s) => write!(f, "invalid cron schedule: {}", s),
            Error::InvalidDaysPattern(s) => write!(f, "invalid patterns for days of month or/and week: {}", s),
            Error::InvalidCronPattern(s) => write!(f, "invalid cron pattern: {}", s),
            Error::InvalidDigitalValue(s) => write!(f, "invalid digital value: {}", s),
            Error::InvalidMnemonicValue(s) => write!(f, "invalid mnemonic value: {}", s),
            Error::InvalidDayOfWeekValue(s) => write!(f, "invalid day of week value: {}", s),
            Error::InvalidRangeValue(s) => write!(f, "invalid range pattern: {}", s),
            Error::InvalidRepeatingPattern(s) => write!(f, "invalid repeating pattern: {}", s),
        }
    }
}
