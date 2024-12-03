use crate::{
    pattern::{Pattern, PatternType},
    Error, Result,
};
use chrono::{DateTime, Datelike, TimeZone, Timelike};
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
    year: Pattern,
    month: Pattern,
    dom: Pattern,
    dow: Pattern,
    hour: Pattern,
    minute: Pattern,
    second: Pattern,
}

impl Schedule {
    /// Schedule constructor.
    pub fn new(pattern: impl Into<String>) -> Result<Self> {
        let pattern = pattern.into();
        let mut parts: Vec<&str> = pattern.split_whitespace().collect();

        if parts.len() == 5 {
            parts.insert(0, "0");
            parts.insert(6, "*");
        } else if parts.len() == 6 {
            parts.insert(6, "*");
        } else if parts.len() != 7 {
            return Err(Error::InvalidCronPattern(pattern));
        }

        Ok(Self {
            second: Pattern::parse(PatternType::Seconds, parts[0])?,
            minute: Pattern::parse(PatternType::Minutes, parts[1])?,
            hour: Pattern::parse(PatternType::Hours, parts[2])?,
            dom: Pattern::parse(PatternType::Doms, parts[3])?,
            month: Pattern::parse(PatternType::Months, parts[4])?,
            dow: Pattern::parse(PatternType::Dows, parts[5])?,
            year: Pattern::parse(PatternType::Years, parts[6])?,
        })
    }

    /// Return time of the upcoming cron event next to provided current.
    pub fn upcoming<Tz: TimeZone>(&self, current: DateTime<Tz>) -> Option<DateTime<Tz>> {
        self.iter(current).next()
    }

    pub fn iter<Tz: TimeZone>(&self, current: DateTime<Tz>) -> impl Iterator<Item = DateTime<Tz>> {
        ScheduleIterator {
            schedule: self.clone(),
            last: current,
        }
    }
}

struct ScheduleIterator<Tz: TimeZone> {
    schedule: Schedule,
    last: DateTime<Tz>,
}

impl<Tz: TimeZone> Iterator for ScheduleIterator<Tz> {
    type Item = DateTime<Tz>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut year = self.last.year();
        let mut month = self.last.month();
        let mut dom = self.last.day();
        let mut hour = self.last.hour();
        let mut minute = self.last.minute();
        let mut second = self.last.second();

        todo!()
    }
}

impl From<String> for Schedule {
    fn from(value: String) -> Self {
        Self::new(value).unwrap()
    }
}

impl From<&String> for Schedule {
    fn from(value: &String) -> Self {
        Self::new(value).unwrap()
    }
}

impl From<&str> for Schedule {
    fn from(value: &str) -> Self {
        Self::new(value).unwrap()
    }
}

impl Display for Schedule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {} {} {} {} {} {}",
            self.second, self.minute, self.hour, self.dom, self.month, self.dow, self.year
        )
    }
}

#[cfg(test)]
mod tests {}
