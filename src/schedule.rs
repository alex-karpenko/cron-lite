use crate::{pattern::Pattern, Result};
use std::fmt::Display;

/// Represents a cron schedule pattern with its methods.
///
/// | Field        | Required | Allowed values  | Allowed special characters |
/// | ------------ | -------- | --------------- | -------------------------- |
/// | Seconds      | No       | 0-59            | * , - /                    |
/// | Minutes      | Yes      | 0-59            | * , - /                    |
/// | Hours        | Yes      | 0-23            | * , - /                    |
/// | Day of Month | Yes      | 1-31            | * , - / ? L W              |
/// | Month        | Yes      | 1-12 or JAN-DEC | * , - /                    |
/// | Day of Week  | Yes      | 0-6 or SUN-SAT  | * , - ? L #                |
/// | Year         | No       | 1970-2099       | * , - /                    |

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Schedule {
    pattern: Pattern,
}

impl Schedule {
    /// Schedule constructor.
    pub fn new(pattern: impl Into<String>) -> Result<Self> {
        Ok(Self {
            pattern: Pattern::new(pattern.into())?,
        })
    }
}

impl Display for Schedule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.pattern)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display() {
        let schedule = Schedule::new("*/5 * * * *").unwrap();
        assert_eq!(schedule.to_string(), "*/5 * * * *");
    }
}
