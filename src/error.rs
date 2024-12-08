use thiserror::Error;

/// Crate specific Errors implementation.
#[derive(Debug, Error, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Error {
    /// Error parsing cron schedule pattern.
    #[error("invalid schedule pattern: {0}")]
    InvalidCronPattern(String),
    /// Invalid digital value.
    #[error("invalid digital value: {0}")]
    InvalidDigitalValue(String),
    /// Invalid mnemonic value.
    #[error("invalid mnemonic value: {0}")]
    InvalidMnemonicValue(String),
    /// Invalid day of week.
    #[error("invalid day of week value: {0}")]
    InvalidDayOfWeekValue(String),
    /// Invalid range.
    #[error("invalid range value: {0}")]
    InvalidRangeValue(String),
    /// Invalid repeating pattern.
    #[error("invalid repeating pattern: {0}")]
    InvalidRepeatingPattern(String),
}
