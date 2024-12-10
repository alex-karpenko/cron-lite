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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_invalid_cron_schedule() {
        let error = CronError::InvalidCronSchedule("* * *".to_string());
        assert_eq!(error.to_string(), "invalid cron schedule: * * *");
    }

    #[test]
    fn test_invalid_days_pattern() {
        let error = CronError::InvalidDaysPattern("31W".to_string());
        assert_eq!(error.to_string(), "invalid patterns of days of month or/and week: 31W");
    }

    #[test]
    fn test_invalid_cron_pattern() {
        let error = CronError::InvalidCronPattern("abc".to_string(), "minutes".to_string());
        assert_eq!(error.to_string(), "minutes: invalid cron pattern: abc");
    }

    #[test]
    fn test_invalid_digital_value() {
        let error = CronError::InvalidDigitalValue("99".to_string(), "minutes".to_string());
        assert_eq!(error.to_string(), "minutes: invalid digital value: 99");
    }

    #[test]
    fn test_invalid_mnemonic_value() {
        let error = CronError::InvalidMnemonicValue("FOO".to_string(), "months".to_string());
        assert_eq!(error.to_string(), "months: invalid mnemonic value: FOO");
    }

    #[test]
    fn test_invalid_day_of_week() {
        let error = CronError::InvalidDayOfWeekValue("8".to_string(), "days of week".to_string());
        assert_eq!(error.to_string(), "days of week: invalid day of week value: 8");
    }

    #[test]
    fn test_invalid_range() {
        let error = CronError::InvalidRangeValue("5-2".to_string(), "hours".to_string());
        assert_eq!(error.to_string(), "hours: invalid range pattern: 5-2");
    }

    #[test]
    fn test_invalid_repeating() {
        let error = CronError::InvalidRepeatingPattern("*/0".to_string(), "minutes".to_string());
        assert_eq!(error.to_string(), "minutes: invalid repeating pattern: */0");
    }
}
