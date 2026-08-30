use std::{error::Error, fmt::Display};

/// Crate-specific `Error` trait implementation.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum CronError {
    /// Invalid cron schedule.
    InvalidCronSchedule(String),
    /// Invalid day of month/week values.
    InvalidDaysPattern(String),
    /// Error parsing cron pattern.
    InvalidCronPattern {
        /// The unparsable pattern.
        pattern: String,
        /// Name of the schedule field the pattern belongs to.
        field: String,
    },
    /// Invalid digital value.
    InvalidDigitalValue {
        /// The invalid value.
        value: String,
        /// Name of the schedule field the value belongs to.
        field: String,
    },
    /// Invalid mnemonic value.
    InvalidMnemonicValue {
        /// The invalid value.
        value: String,
        /// Name of the schedule field the value belongs to.
        field: String,
    },
    /// Invalid day of the week.
    InvalidDayOfWeekValue {
        /// The invalid value.
        value: String,
        /// Name of the schedule field the value belongs to.
        field: String,
    },
    /// Invalid range pattern.
    InvalidRangeValue {
        /// The invalid range.
        value: String,
        /// Name of the schedule field the range belongs to.
        field: String,
    },
    /// Invalid repeating pattern.
    InvalidRepeatingPattern {
        /// The invalid pattern.
        pattern: String,
        /// Name of the schedule field the pattern belongs to.
        field: String,
    },
    /// Invalid `TimeZone`
    InvalidTimeZone(String),
    /// A single schedule field contains more comma-separated values than the field allows.
    TooManyPatternValues {
        /// Name of the schedule field with too many values.
        field: String,
        /// Maximum number of values allowed for this field.
        max: usize,
    },
}

impl Error for CronError {}

impl Display for CronError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CronError::InvalidCronSchedule(schedule) => write!(f, "invalid cron schedule: {schedule}"),
            CronError::InvalidDaysPattern(pattern) => {
                write!(f, "invalid patterns of days of month or/and week: {pattern}")
            }
            CronError::InvalidCronPattern { pattern, field } => {
                write!(f, "{field}: invalid cron pattern: {pattern}")
            }
            CronError::InvalidDigitalValue { value, field } => {
                write!(f, "{field}: invalid digital value: {value}")
            }
            CronError::InvalidMnemonicValue { value, field } => {
                write!(f, "{field}: invalid mnemonic value: {value}")
            }
            CronError::InvalidDayOfWeekValue { value, field } => {
                write!(f, "{field}: invalid day of week value: {value}")
            }
            CronError::InvalidRangeValue { value, field } => {
                write!(f, "{field}: invalid range pattern: {value}")
            }
            CronError::InvalidRepeatingPattern { pattern, field } => {
                write!(f, "{field}: invalid repeating pattern: {pattern}")
            }
            CronError::InvalidTimeZone(tz) => write!(f, "invalid time zone: {tz}"),
            CronError::TooManyPatternValues { field, max } => {
                write!(f, "{field}: pattern list exceeds maximum of {max} values")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;
    use std::time::Duration;

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn test_invalid_cron_schedule() {
        let error = CronError::InvalidCronSchedule("* * *".to_string());
        assert_eq!(error.to_string(), "invalid cron schedule: * * *");
    }

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn test_invalid_days_pattern() {
        let error = CronError::InvalidDaysPattern("31W".to_string());
        assert_eq!(error.to_string(), "invalid patterns of days of month or/and week: 31W");
    }

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn test_invalid_cron_pattern() {
        let error = CronError::InvalidCronPattern {
            pattern: "abc".to_string(),
            field: "minutes".to_string(),
        };
        assert_eq!(error.to_string(), "minutes: invalid cron pattern: abc");
    }

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn test_invalid_digital_value() {
        let error = CronError::InvalidDigitalValue {
            value: "99".to_string(),
            field: "minutes".to_string(),
        };
        assert_eq!(error.to_string(), "minutes: invalid digital value: 99");
    }

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn test_invalid_mnemonic_value() {
        let error = CronError::InvalidMnemonicValue {
            value: "FOO".to_string(),
            field: "months".to_string(),
        };
        assert_eq!(error.to_string(), "months: invalid mnemonic value: FOO");
    }

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn test_invalid_day_of_week() {
        let error = CronError::InvalidDayOfWeekValue {
            value: "8".to_string(),
            field: "days of week".to_string(),
        };
        assert_eq!(error.to_string(), "days of week: invalid day of week value: 8");
    }

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn test_invalid_range() {
        let error = CronError::InvalidRangeValue {
            value: "5-2".to_string(),
            field: "hours".to_string(),
        };
        assert_eq!(error.to_string(), "hours: invalid range pattern: 5-2");
    }

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn test_invalid_repeating() {
        let error = CronError::InvalidRepeatingPattern {
            pattern: "*/0".to_string(),
            field: "minutes".to_string(),
        };
        assert_eq!(error.to_string(), "minutes: invalid repeating pattern: */0");
    }

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn test_invalid_tz() {
        let error = CronError::InvalidTimeZone("qqq".to_string());
        assert_eq!(error.to_string(), "invalid time zone: qqq");
    }

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn test_too_many_pattern_values() {
        let error = CronError::TooManyPatternValues {
            field: "seconds".to_string(),
            max: 60,
        };
        assert_eq!(error.to_string(), "seconds: pattern list exceeds maximum of 60 values");
    }
}
