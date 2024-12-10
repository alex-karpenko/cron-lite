use std::{error::Error, fmt::Display};

/// Crate specific Error implementation.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CronError {
    /// Invalid cron schedule.
    InvalidCronSchedule(String),
    /// Invalid day of month/week values.
    InvalidDaysPattern(String),
    /// Error parsing cron pattern.
    InvalidCronPattern(String, String),
    /// Invalid digital value.
    InvalidDigitalValue(String, String),
    /// Invalid mnemonic value.
    InvalidMnemonicValue(String, String),
    /// Invalid day of the week.
    InvalidDayOfWeekValue(String, String),
    /// Invalid range pattern.
    InvalidRangeValue(String, String),
    /// Invalid repeating pattern.
    InvalidRepeatingPattern(String, String),
}

impl Error for CronError {}

impl Display for CronError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CronError::InvalidCronSchedule(schedule) => write!(f, "invalid cron schedule: {}", schedule),
            CronError::InvalidDaysPattern(pattern) => {
                write!(f, "invalid patterns of days of month or/and week: {pattern}")
            }
            CronError::InvalidCronPattern(pattern, type_) => write!(f, "{type_}: invalid cron pattern: {}", pattern),
            CronError::InvalidDigitalValue(value, type_) => write!(f, "{type_}: invalid digital value: {}", value),
            CronError::InvalidMnemonicValue(value, type_) => write!(f, "{type_}: invalid mnemonic value: {}", value),
            CronError::InvalidDayOfWeekValue(value, type_) => {
                write!(f, "{type_}: invalid day of week value: {}", value)
            }
            CronError::InvalidRangeValue(value, type_) => write!(f, "{type_}: invalid range pattern: {}", value),
            CronError::InvalidRepeatingPattern(pattern, type_) => {
                write!(f, "{type_}: invalid repeating pattern: {}", pattern)
            }
        }
    }
}
