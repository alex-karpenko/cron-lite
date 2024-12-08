use crate::{
    pattern::{Pattern, PatternItem, PatternType, PatternValueType},
    utils, Error, Result,
};
use chrono::{DateTime, Datelike, TimeDelta, TimeZone, Timelike};
use std::fmt::Display;

pub const MIN_YEAR: u16 = 1970;
pub const MAX_YEAR: u16 = 2099;

pub(crate) const MIN_YEAR_STR: &str = "1970";

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

        let schedule = Self {
            second: Pattern::parse(PatternType::Seconds, parts[0])?,
            minute: Pattern::parse(PatternType::Minutes, parts[1])?,
            hour: Pattern::parse(PatternType::Hours, parts[2])?,
            dom: Pattern::parse(PatternType::Doms, parts[3])?,
            month: Pattern::parse(PatternType::Months, parts[4])?,
            dow: Pattern::parse(PatternType::Dows, parts[5])?,
            year: Pattern::parse(PatternType::Years, parts[6])?,
        };

        // Validate DOM and DOW relationship
        let pattern_dom = schedule.dom.pattern();
        let pattern_dow = schedule.dow.pattern();
        match (pattern_dom, pattern_dow) {
            (PatternItem::Any, PatternItem::Any) => return Err(Error::InvalidCronPattern(pattern)),
            (PatternItem::All, _) | (_, PatternItem::All) | (PatternItem::Any, _) | (_, PatternItem::Any) => {}
            (_, _) => {
                return Err(Error::InvalidCronPattern(pattern));
            }
        }

        Ok(schedule)
    }

    /// Return time of the upcoming cron event next to provided current.
    pub fn upcoming<Tz: TimeZone>(&self, current: &DateTime<Tz>) -> Option<DateTime<Tz>> {
        let mut current = if current.nanosecond() > 0 {
            current
                .with_nanosecond(0)
                .unwrap()
                .checked_add_signed(TimeDelta::seconds(1))
                .unwrap()
        } else {
            current.clone()
        };

        let mut year = Some(current.year() as PatternValueType);
        let mut month = Some(current.month() as PatternValueType);
        let mut dom = Some(current.day() as PatternValueType);
        let mut hour = Some(current.hour() as PatternValueType);
        let mut minute = Some(current.minute() as PatternValueType);
        let mut second = Some(current.second() as PatternValueType);
        let mut first_iteration = true;

        while year.is_none()
            || month.is_none()
            || dom.is_none()
            || hour.is_none()
            || minute.is_none()
            || second.is_none()
            || first_iteration
        {
            first_iteration = false;

            if year.is_none() {
                return None;
            } else if month.is_none() {
                inc_year(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second)?;
            } else if dom.is_none() {
                inc_month(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second)?;
            } else if hour.is_none() {
                inc_dom(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second)?;
            } else if minute.is_none() {
                inc_hour(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second)?;
            } else if second.is_none() {
                inc_minute(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second)?;
            }

            current = current
                .timezone()
                .with_ymd_and_hms(
                    year? as i32,
                    month? as u32,
                    dom? as u32,
                    hour? as u32,
                    minute? as u32,
                    second? as u32,
                )
                .unwrap();

            year = self.year.next(&mut current);
            if year.is_some() {
                month = self.month.next(&mut current);
                year = Some(current.year() as PatternValueType);
                if month.is_some() {
                    dom = match (self.dom.pattern(), self.dow.pattern()) {
                        (PatternItem::All, PatternItem::All) => self.dom.next(&mut current),
                        (PatternItem::All, PatternItem::Any) => self.dom.next(&mut current),
                        (PatternItem::All, _) => self.dow.next(&mut current),
                        (PatternItem::Any, PatternItem::All) => self.dow.next(&mut current),
                        (PatternItem::Any, PatternItem::Any) => unreachable!(),
                        (PatternItem::Any, _) => self.dow.next(&mut current),
                        (_, PatternItem::All) => self.dom.next(&mut current),
                        (_, PatternItem::Any) => self.dom.next(&mut current),
                        (_, _) => unreachable!(),
                    };
                    year = Some(current.year() as PatternValueType);
                    month = Some(current.month() as PatternValueType);
                    if dom.is_some() {
                        hour = self.hour.next(&mut current);
                        year = Some(current.year() as PatternValueType);
                        month = Some(current.month() as PatternValueType);
                        dom = Some(current.day() as PatternValueType);
                        if hour.is_some() {
                            minute = self.minute.next(&mut current);
                            year = Some(current.year() as PatternValueType);
                            month = Some(current.month() as PatternValueType);
                            dom = Some(current.day() as PatternValueType);
                            hour = Some(current.hour() as PatternValueType);
                            if minute.is_some() {
                                second = self.second.next(&mut current);
                                year = Some(current.year() as PatternValueType);
                                month = Some(current.month() as PatternValueType);
                                dom = Some(current.day() as PatternValueType);
                                hour = Some(current.hour() as PatternValueType);
                                minute = Some(current.minute() as PatternValueType);
                            }
                        }
                    }
                }
            }
        }

        Some(
            current
                .timezone()
                .with_ymd_and_hms(
                    year? as i32,
                    month? as u32,
                    dom? as u32,
                    hour? as u32,
                    minute? as u32,
                    second? as u32,
                )
                .unwrap(),
        )
    }

    pub fn iter<Tz: TimeZone>(&self, current: &DateTime<Tz>) -> impl Iterator<Item = DateTime<Tz>> {
        ScheduleIterator {
            schedule: self.clone(),
            next: self.upcoming(current),
        }
    }

    pub fn into_iter<Tz: TimeZone>(self, current: &DateTime<Tz>) -> impl Iterator<Item = DateTime<Tz>> {
        let next = self.upcoming(current);
        ScheduleIterator { schedule: self, next }
    }
}

struct ScheduleIterator<Tz: TimeZone> {
    schedule: Schedule,
    next: Option<DateTime<Tz>>,
}

impl<Tz: TimeZone> Iterator for ScheduleIterator<Tz> {
    type Item = DateTime<Tz>;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.next.take()?;
        self.next = self
            .schedule
            .upcoming(&current.clone().checked_add_signed(TimeDelta::seconds(1))?);
        Some(current)
    }
}

impl TryFrom<String> for Schedule {
    type Error = Error;

    fn try_from(value: String) -> Result<Self> {
        Self::new(value)
    }
}

impl TryFrom<&String> for Schedule {
    type Error = Error;

    fn try_from(value: &String) -> Result<Self> {
        Self::new(value)
    }
}

impl TryFrom<&str> for Schedule {
    type Error = Error;

    fn try_from(value: &str) -> Result<Self> {
        Self::new(value)
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

fn inc_year(
    year: &mut Option<PatternValueType>,
    month: &mut Option<PatternValueType>,
    dom: &mut Option<PatternValueType>,
    hour: &mut Option<PatternValueType>,
    minute: &mut Option<PatternValueType>,
    second: &mut Option<PatternValueType>,
) -> Option<PatternValueType> {
    if (*year)? < MAX_YEAR {
        *year = Some((*year)? + 1);
        *month = Some(1);
        *dom = Some(1);
        *hour = Some(0);
        *minute = Some(0);
        *second = Some(0);

        *year
    } else {
        *year = None;
        None
    }
}

fn inc_month(
    year: &mut Option<PatternValueType>,
    month: &mut Option<PatternValueType>,
    dom: &mut Option<PatternValueType>,
    hour: &mut Option<PatternValueType>,
    minute: &mut Option<PatternValueType>,
    second: &mut Option<PatternValueType>,
) -> Option<PatternValueType> {
    if (*month)? < 12 {
        *month = Some((*month)? + 1);
        *dom = Some(1);
        *hour = Some(0);
        *minute = Some(0);
        *second = Some(0);

        *month
    } else {
        inc_year(year, month, dom, hour, minute, second)?;
        *month
    }
}

fn inc_dom(
    year: &mut Option<PatternValueType>,
    month: &mut Option<PatternValueType>,
    dom: &mut Option<PatternValueType>,
    hour: &mut Option<PatternValueType>,
    minute: &mut Option<PatternValueType>,
    second: &mut Option<PatternValueType>,
) -> Option<PatternValueType> {
    if (*dom)? < utils::days_in_month((*year)?, (*month)?) {
        *dom = Some((*dom)? + 1);
        *hour = Some(0);
        *minute = Some(0);
        *second = Some(0);

        *dom
    } else {
        inc_month(year, month, dom, hour, minute, second)?;
        *dom
    }
}

fn inc_hour(
    year: &mut Option<PatternValueType>,
    month: &mut Option<PatternValueType>,
    dom: &mut Option<PatternValueType>,
    hour: &mut Option<PatternValueType>,
    minute: &mut Option<PatternValueType>,
    second: &mut Option<PatternValueType>,
) -> Option<PatternValueType> {
    if (*hour)? < 23 {
        *hour = Some((*hour)? + 1);
        *minute = Some(0);
        *second = Some(0);

        *hour
    } else {
        inc_dom(year, month, dom, hour, minute, second)?;
        *hour
    }
}

fn inc_minute(
    year: &mut Option<PatternValueType>,
    month: &mut Option<PatternValueType>,
    dom: &mut Option<PatternValueType>,
    hour: &mut Option<PatternValueType>,
    minute: &mut Option<PatternValueType>,
    second: &mut Option<PatternValueType>,
) -> Option<PatternValueType> {
    if (*minute)? < 59 {
        *minute = Some((*minute)? + 1);
        *second = Some(0);

        *minute
    } else {
        inc_hour(year, month, dom, hour, minute, second)?;
        *minute
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use chrono::DateTime;
    use rstest::rstest;
    use rstest_reuse::{apply, template};
    use std::time::Duration;

    #[rstest]
    #[case("* 0 0 1 1 *", "2024-01-01T00:00:21Z", "2024-01-01T00:00:21+00:00")]
    #[case("* 0 0 1 1 *", "2024-01-01T01:00:25Z", "2025-01-01T00:00:00+00:00")]
    #[case("*/5 * * * * *", "2024-01-01T00:00:00Z", "2024-01-01T00:00:00+00:00")]
    #[case("*/5 * * * * *", "2024-01-01T00:00:01Z", "2024-01-01T00:00:05+00:00")]
    #[case("0 */15 * * * *", "2024-01-01T00:00:00Z", "2024-01-01T00:00:00+00:00")]
    #[case("0 */15 * * * *", "2024-01-01T00:01:00Z", "2024-01-01T00:15:00+00:00")]
    #[case("0 */30 9-17 * * 1-5", "2024-01-01T09:00:00Z", "2024-01-01T09:00:00+00:00")]
    #[case("0 */30 9-17 * * 1-5", "2024-01-01T09:15:00Z", "2024-01-01T09:30:00+00:00")]
    #[case("0 */5 * * * *", "2024-01-01T00:01:00Z", "2024-01-01T00:05:00+00:00")]
    #[case("0 0 */2 * * *", "2024-01-01T01:00:00Z", "2024-01-01T02:00:00+00:00")]
    #[case("0 0 0 ? * 1-5", "2024-01-01T00:00:00Z", "2024-01-01T00:00:00+00:00")]
    #[case("0 0 0 ? * 1-5", "2024-01-01T00:00:01Z", "2024-01-02T00:00:00+00:00")]
    #[case("0 0 0 ? * 1-5", "2024-01-05T00:00:01Z", "2024-01-08T00:00:00+00:00")]
    #[case("0 0 0 * * 1#1", "2024-01-01T00:00:00Z", "2024-01-01T00:00:00+00:00")]
    #[case("0 0 0 * * 1#1", "2024-01-02T00:00:00Z", "2024-02-05T00:00:00+00:00")]
    #[case("0 0 0 * * 5L", "2024-01-01T00:00:00Z", "2024-01-26T00:00:00+00:00")]
    #[case("0 0 0 * * 5L", "2024-01-26T00:00:01Z", "2024-02-23T00:00:00+00:00")]
    #[case("0 0 0 * * 5L", "2024-02-23T00:00:00Z", "2024-02-23T00:00:00+00:00")]
    #[case("0 0 0 * * 6,0", "2024-01-01T00:00:00Z", "2024-01-06T00:00:00+00:00")]
    #[case("0 0 0 * * 6,0", "2024-01-06T00:00:01Z", "2024-01-07T00:00:00+00:00")]
    #[case("0 0 0 * * 6,0", "2024-01-07T00:00:00Z", "2024-01-07T00:00:00+00:00")]
    #[case("0 0 0 * * 6,0", "2024-01-07T00:00:01Z", "2024-01-13T00:00:00+00:00")]
    #[case("0 0 0 * * MON", "2024-01-01T00:00:00Z", "2024-01-01T00:00:00+00:00")]
    #[case("0 0 0 * * SUN", "2024-01-01T00:00:00Z", "2024-01-07T00:00:00+00:00")]
    #[case("0 0 0 1 */2 *", "2024-01-01T00:00:00Z", "2024-01-01T00:00:00+00:00")]
    #[case("0 0 0 1 */2 *", "2024-02-01T00:00:00Z", "2024-03-01T00:00:00+00:00")]
    #[case("0 0 0 1 */3 * 1999", "1999-01-01T00:00:00Z", "1999-01-01T00:00:00+00:00")]
    #[case("0 0 0 1 */3 * 1999", "1999-02-01T00:00:00Z", "1999-04-01T00:00:00+00:00")]
    #[case("0 0 0 1 */3 *", "2024-01-01T00:00:00Z", "2024-01-01T00:00:00+00:00")]
    #[case("0 0 0 1 */3 *", "2024-02-01T00:00:00Z", "2024-04-01T00:00:00+00:00")]
    #[case("0 0 0 1 1 * *", "2024-01-01T00:00:00Z", "2024-01-01T00:00:00+00:00")]
    #[case("0 0 0 1 1 * *", "2024-01-01T00:00:01Z", "2025-01-01T00:00:00+00:00")]
    #[case("0 0 0 1 1 * 1970", "2024-01-01T00:00:00Z", "None")]
    #[case("0 0 0 1 1 * 1999", "1999-01-01T00:00:00Z", "1999-01-01T00:00:00+00:00")]
    #[case("0 0 0 1 1 * 1999", "1999-01-01T00:00:01Z", "None")]
    #[case("0 0 0 1 1 * 2024-2025", "2024-01-01T00:00:00Z", "2024-01-01T00:00:00+00:00")]
    #[case("0 0 0 1 1 * 2024-2025", "2025-01-01T00:00:00Z", "2025-01-01T00:00:00+00:00")]
    #[case("0 0 0 1 1 * 2024-2025", "2026-01-01T00:00:00Z", "None")]
    #[case("0 0 0 1 1,6,12 *", "2024-01-01T00:00:00Z", "2024-01-01T00:00:00+00:00")]
    #[case("0 0 0 1 1,6,12 *", "2024-02-01T00:00:00Z", "2024-06-01T00:00:00+00:00")]
    #[case("0 0 0 1,15 * ?", "2024-01-01T00:00:00Z", "2024-01-01T00:00:00+00:00")]
    #[case("0 0 0 1,15 * ?", "2024-01-01T00:00:01Z", "2024-01-15T00:00:00+00:00")]
    #[case("0 0 0 1,15 * ?", "2024-01-15T00:00:01Z", "2024-02-01T00:00:00+00:00")]
    #[case("0 0 0 1,15,L * ?", "2024-01-01T00:00:00Z", "2024-01-01T00:00:00+00:00")]
    #[case("0 0 0 1,15,L * ?", "2024-01-15T00:00:01Z", "2024-01-31T00:00:00+00:00")]
    #[case("0 0 0 1,15,L * ?", "2024-01-31T00:00:01Z", "2024-02-01T00:00:00+00:00")]
    #[case("0 0 0 1W * *", "2024-01-01T00:00:00Z", "2024-01-01T00:00:00+00:00")]
    #[case("0 0 0 1W * *", "2024-04-01T00:00:00Z", "2024-04-01T00:00:00+00:00")]
    #[case("0 0 0 28-31 2 *", "2024-02-28T00:00:00Z", "2024-02-28T00:00:00+00:00")]
    #[case("0 0 0 28-31 2 *", "2024-02-28T00:00:01Z", "2024-02-29T00:00:00+00:00")]
    #[case("0 0 0 28-31 2 *", "2025-02-28T00:00:00Z", "2025-02-28T00:00:00+00:00")]
    #[case("0 0 0 28-31 2 *", "2025-02-28T00:00:01Z", "2026-02-28T00:00:00+00:00")]
    #[case("0 0 0 28,29,30,31 2 *", "2024-02-28T00:00:00Z", "2024-02-28T00:00:00+00:00")]
    #[case("0 0 0 28,29,30,31 2 *", "2024-02-28T00:00:01Z", "2024-02-29T00:00:00+00:00")]
    #[case("0 0 0 28,29,30,31 2 *", "2025-02-28T00:00:00Z", "2025-02-28T00:00:00+00:00")]
    #[case("0 0 0 28,29,30,31 2 *", "2025-02-28T00:00:01Z", "2026-02-28T00:00:00+00:00")]
    #[case("0 0 0 29 2 * 1999", "1999-01-01T00:00:00Z", "None")]
    #[case("0 0 0 29 2 * 1999/3", "1999-01-01T00:00:00Z", "2008-02-29T00:00:00+00:00")]
    #[case("0 0 0 29 2 *", "2024-01-01T00:00:00Z", "2024-02-29T00:00:00+00:00")]
    #[case("0 0 0 29 2 *", "2024-03-01T00:00:00Z", "2028-02-29T00:00:00+00:00")]
    #[case("0 0 0 29-31 2 *", "2024-02-29T00:00:00Z", "2024-02-29T00:00:00+00:00")]
    #[case("0 0 0 29-31 2 *", "2024-02-29T00:00:01Z", "2028-02-29T00:00:00+00:00")]
    #[case("0 0 0 29-31 2 *", "2025-02-01T00:00:00Z", "2028-02-29T00:00:00+00:00")]
    #[case("0 0 0 29,30,31 2 *", "2024-02-29T00:00:00Z", "2024-02-29T00:00:00+00:00")]
    #[case("0 0 0 29,30,31 2 *", "2024-02-29T00:00:01Z", "2028-02-29T00:00:00+00:00")]
    #[case("0 0 0 29,30,31 2 *", "2025-02-01T00:00:00Z", "2028-02-29T00:00:00+00:00")]
    #[case("0 0 0 31 */2 * 1999", "1999-01-01T00:00:00Z", "1999-01-31T00:00:00+00:00")]
    #[case("0 0 0 31 */2 *", "2024-01-01T00:00:00Z", "2024-01-31T00:00:00+00:00")]
    #[case("0 0 0 31 */2 *", "2024-02-01T00:00:00Z", "2024-03-31T00:00:00+00:00")]
    #[case("0 0 0 L * * 1999", "1999-01-15T00:00:00Z", "1999-01-31T00:00:00+00:00")]
    #[case("0 0 0 L * * 1999", "1999-02-15T00:00:00Z", "1999-02-28T00:00:00+00:00")]
    #[case("0 0 0 L * *", "2024-01-15T00:00:00Z", "2024-01-31T00:00:00+00:00")]
    #[case("0 0 0 L * *", "2024-02-15T00:00:00Z", "2024-02-29T00:00:00+00:00")]
    #[case("0 0 0 L * *", "2024-04-15T00:00:00Z", "2024-04-30T00:00:00+00:00")]
    #[case("0 0 1 1 *", "2024-01-01T00:00:00Z", "2024-01-01T00:00:00+00:00")]
    #[case("0 0 1 1 *", "2024-01-01T00:00:01Z", "2025-01-01T00:00:00+00:00")]
    #[case("0 0 12 ? * 2-6", "2024-01-01T00:00:00Z", "2024-01-02T12:00:00+00:00")]
    #[case("0 0 12 ? * 2-6", "2024-01-06T12:00:00Z", "2024-01-06T12:00:00+00:00")]
    #[case("0 0 12 ? * 2-6", "2024-01-06T12:00:01Z", "2024-01-09T12:00:00+00:00")]
    #[case("0 0 12 * * MON-FRI 1999", "1999-01-01T00:00:00Z", "1999-01-01T12:00:00+00:00")]
    #[case("0 0 12 * * MON-FRI 1999", "1999-01-01T12:00:01Z", "1999-01-04T12:00:00+00:00")]
    #[case("0 0 12 * * MON-FRI", "2024-01-01T00:00:00Z", "2024-01-01T12:00:00+00:00")]
    #[case("0 0 12 * * MON-FRI", "2024-01-06T00:00:00Z", "2024-01-08T12:00:00+00:00")]
    #[case("0 0 12 1-7 * *", "2024-01-01T00:00:00Z", "2024-01-01T12:00:00+00:00")]
    #[case("0 0 12 1-7 * *", "2024-01-07T12:00:00Z", "2024-01-07T12:00:00+00:00")]
    #[case("0 0 12 1-7 * *", "2024-01-07T12:00:01Z", "2024-02-01T12:00:00+00:00")]
    #[case("0 0 12 1,15 * ?", "2024-01-01T00:00:00Z", "2024-01-01T12:00:00+00:00")]
    #[case("0 0 12 1,15 * ?", "2024-01-01T12:00:01Z", "2024-01-15T12:00:00+00:00")]
    #[case("0 0 6 * * 1-5", "2024-01-01T00:00:00Z", "2024-01-01T06:00:00+00:00")]
    #[case("0 0 6 * * 1-5", "2024-01-06T00:00:00Z", "2024-01-08T06:00:00+00:00")]
    #[case("0 0 9 * * 1", "2024-01-01T00:00:00Z", "2024-01-01T09:00:00+00:00")]
    #[case("0 0 9 * * 1", "2024-01-01T09:00:01Z", "2024-01-08T09:00:00+00:00")]
    #[case("0 0 9-17 * * 1-5", "2024-01-01T08:00:00Z", "2024-01-01T09:00:00+00:00")]
    #[case("0 0 9-17 * * 1-5", "2024-01-01T17:00:01Z", "2024-01-02T09:00:00+00:00")]
    #[case("0 15,45 9-17 * * 1-5", "2024-01-01T09:00:00Z", "2024-01-01T09:15:00+00:00")]
    #[case("0 15,45 9-17 * * 1-5", "2024-01-01T09:15:01Z", "2024-01-01T09:45:00+00:00")]
    #[case("0 30 0 1 * *", "2024-01-01T00:00:00Z", "2024-01-01T00:30:00+00:00")]
    #[case("30 0 0 1 * *", "2024-01-01T00:00:00Z", "2024-01-01T00:00:30+00:00")]
    #[case("30 0 0 1 * *", "2024-01-01T00:00:30Z", "2024-01-01T00:00:30+00:00")]
    #[case("30 0 0 1 * *", "2024-01-01T00:00:30.001Z", "2024-02-01T00:00:30+00:00")]
    #[case("25 * * * *", "2024-01-01T00:21:21Z", "2024-01-01T00:25:00+00:00")] // case with increasing current minute
    #[case("1 2 29-31 * *", "2024-01-01T00:00:21Z", "2024-01-29T02:01:00+00:00")]
    #[case("1 2 29-31 * *", "2024-01-31T00:00:21Z", "2024-01-31T02:01:00+00:00")]
    #[case("1 2 29-31 * *", "2024-02-01T00:00:21Z", "2024-02-29T02:01:00+00:00")]
    #[case("1 2 29-31 * *", "2024-03-31T00:00:21Z", "2024-03-31T02:01:00+00:00")]
    #[case("1 2 29-31 * *", "2025-01-01T00:00:21Z", "2025-01-29T02:01:00+00:00")]
    #[case("1 2 29-31 * *", "2025-02-01T00:00:21Z", "2025-03-29T02:01:00+00:00")]
    #[case("1 2 29-31 * *", "2025-03-31T00:00:21Z", "2025-03-31T02:01:00+00:00")]
    #[timeout(Duration::from_secs(1))]
    fn test_schedule_upcoming(#[case] pattern: &str, #[case] current: &str, #[case] expected: &str) {
        let schedule = Schedule::new(pattern).unwrap();
        let current = DateTime::parse_from_rfc3339(current).unwrap();
        let next = schedule.upcoming(&current);

        if expected == "None" {
            assert!(
                next.is_none(),
                "pattern = {pattern}, schedule = {schedule:?}, current = {current}, next = {next:?}"
            );
        } else {
            assert!(
                next.is_some(),
                "pattern = {pattern}, schedule = {schedule:?}, current = {current}, next = {next:?}"
            );

            assert_eq!(
                next.unwrap().to_rfc3339(),
                expected,
                "pattern = {pattern}, schedule = {schedule:?}, current = {current}, next = {next:?}"
            );
        }
    }

    #[test]
    fn test_inc_year() {
        let mut year = Some(2024);
        let mut month = Some(1);
        let mut dom = Some(1);
        let mut hour = Some(0);
        let mut minute = Some(0);
        let mut second = Some(0);

        assert_eq!(
            inc_year(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second),
            Some(2025)
        );
        assert_eq!(year, Some(2025));
        assert_eq!(month, Some(1));
        assert_eq!(dom, Some(1));
        assert_eq!(hour, Some(0));
        assert_eq!(minute, Some(0));
        assert_eq!(second, Some(0));

        year = Some(MAX_YEAR);
        assert_eq!(
            inc_year(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second),
            None
        );
        assert_eq!(year, None);
    }

    #[test]
    fn test_inc_month() {
        let mut year = Some(2024);
        let mut month = Some(1);
        let mut dom = Some(1);
        let mut hour = Some(0);
        let mut minute = Some(0);
        let mut second = Some(0);

        assert_eq!(
            inc_month(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second),
            Some(2)
        );
        assert_eq!(year, Some(2024));
        assert_eq!(month, Some(2));
        assert_eq!(dom, Some(1));
        assert_eq!(hour, Some(0));
        assert_eq!(minute, Some(0));
        assert_eq!(second, Some(0));

        year = Some(2024);
        month = Some(12);
        assert_eq!(
            inc_month(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second),
            Some(1)
        );
        assert_eq!(year, Some(2025));
        assert_eq!(month, Some(1));
        assert_eq!(dom, Some(1));
        assert_eq!(hour, Some(0));
        assert_eq!(minute, Some(0));
        assert_eq!(second, Some(0));

        year = Some(MAX_YEAR);
        month = Some(12);
        assert_eq!(
            inc_month(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second),
            None
        );
        assert_eq!(year, None);
    }

    #[test]
    fn test_inc_dom() {
        let mut year = Some(2024);
        let mut month = Some(1);
        let mut dom = Some(1);
        let mut hour = Some(0);
        let mut minute = Some(0);
        let mut second = Some(0);

        assert_eq!(
            inc_dom(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second),
            Some(2)
        );
        assert_eq!(year, Some(2024));
        assert_eq!(month, Some(1));
        assert_eq!(dom, Some(2));
        assert_eq!(hour, Some(0));
        assert_eq!(minute, Some(0));
        assert_eq!(second, Some(0));

        year = Some(2024);
        month = Some(1);
        dom = Some(31);
        assert_eq!(
            inc_dom(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second),
            Some(1)
        );
        assert_eq!(year, Some(2024));
        assert_eq!(month, Some(2));
        assert_eq!(dom, Some(1));
        assert_eq!(hour, Some(0));
        assert_eq!(minute, Some(0));
        assert_eq!(second, Some(0));

        year = Some(2024);
        month = Some(12);
        dom = Some(31);
        assert_eq!(
            inc_dom(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second),
            Some(1)
        );
        assert_eq!(year, Some(2025));
        assert_eq!(month, Some(1));
        assert_eq!(dom, Some(1));
        assert_eq!(hour, Some(0));
        assert_eq!(minute, Some(0));
        assert_eq!(second, Some(0));

        year = Some(2024);
        month = Some(2);
        dom = Some(28);
        assert_eq!(
            inc_dom(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second),
            Some(29)
        );
        assert_eq!(year, Some(2024));
        assert_eq!(month, Some(2));
        assert_eq!(dom, Some(29));
        assert_eq!(hour, Some(0));
        assert_eq!(minute, Some(0));
        assert_eq!(second, Some(0));

        year = Some(2025);
        month = Some(2);
        dom = Some(28);
        assert_eq!(
            inc_dom(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second),
            Some(1)
        );
        assert_eq!(year, Some(2025));
        assert_eq!(month, Some(3));
        assert_eq!(dom, Some(1));
        assert_eq!(hour, Some(0));
        assert_eq!(minute, Some(0));
        assert_eq!(second, Some(0));

        year = Some(MAX_YEAR);
        month = Some(12);
        dom = Some(31);
        assert_eq!(
            inc_dom(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second),
            None
        );
        assert_eq!(year, None);
    }

    #[test]
    fn test_inc_hour() {
        let mut year = Some(2024);
        let mut month = Some(1);
        let mut dom = Some(1);
        let mut hour = Some(0);
        let mut minute = Some(0);
        let mut second = Some(0);

        assert_eq!(
            inc_hour(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second),
            Some(1)
        );
        assert_eq!(year, Some(2024));
        assert_eq!(month, Some(1));
        assert_eq!(dom, Some(1));
        assert_eq!(hour, Some(1));
        assert_eq!(minute, Some(0));
        assert_eq!(second, Some(0));

        year = Some(2024);
        month = Some(1);
        dom = Some(1);
        hour = Some(23);
        assert_eq!(
            inc_hour(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second),
            Some(0)
        );
        assert_eq!(year, Some(2024));
        assert_eq!(month, Some(1));
        assert_eq!(dom, Some(2));
        assert_eq!(hour, Some(0));
        assert_eq!(minute, Some(0));
        assert_eq!(second, Some(0));

        year = Some(2024);
        month = Some(12);
        dom = Some(31);
        hour = Some(23);
        assert_eq!(
            inc_hour(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second),
            Some(0)
        );
        assert_eq!(year, Some(2025));
        assert_eq!(month, Some(1));
        assert_eq!(dom, Some(1));
        assert_eq!(hour, Some(0));
        assert_eq!(minute, Some(0));
        assert_eq!(second, Some(0));

        year = Some(MAX_YEAR);
        month = Some(12);
        dom = Some(31);
        hour = Some(23);
        assert_eq!(
            inc_hour(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second),
            None
        );
        assert_eq!(year, None);
    }

    #[test]
    fn test_inc_minute() {
        let mut year = Some(2024);
        let mut month = Some(1);
        let mut dom = Some(1);
        let mut hour = Some(0);
        let mut minute = Some(0);
        let mut second = Some(0);

        assert_eq!(
            inc_minute(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second),
            Some(1)
        );
        assert_eq!(year, Some(2024));
        assert_eq!(month, Some(1));
        assert_eq!(dom, Some(1));
        assert_eq!(hour, Some(0));
        assert_eq!(minute, Some(1));
        assert_eq!(second, Some(0));

        year = Some(2024);
        month = Some(1);
        dom = Some(1);
        hour = Some(23);
        minute = Some(59);
        assert_eq!(
            inc_minute(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second),
            Some(0)
        );
        assert_eq!(year, Some(2024));
        assert_eq!(month, Some(1));
        assert_eq!(dom, Some(2));
        assert_eq!(hour, Some(0));
        assert_eq!(minute, Some(0));
        assert_eq!(second, Some(0));

        year = Some(2024);
        month = Some(12);
        dom = Some(31);
        hour = Some(23);
        minute = Some(59);
        assert_eq!(
            inc_minute(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second),
            Some(0)
        );
        assert_eq!(year, Some(2025));
        assert_eq!(month, Some(1));
        assert_eq!(dom, Some(1));
        assert_eq!(hour, Some(0));
        assert_eq!(minute, Some(0));
        assert_eq!(second, Some(0));

        year = Some(MAX_YEAR);
        month = Some(12);
        dom = Some(31);
        hour = Some(23);
        minute = Some(59);
        assert_eq!(
            inc_minute(&mut year, &mut month, &mut dom, &mut hour, &mut minute, &mut second),
            None
        );
        assert_eq!(year, None);
    }

    #[template]
    #[rstest]
    #[case("* * * * * * *", "* * * * * * *")]
    #[case("* * * * * *", "* * * * * * *")]
    #[case("* * * * *", "0 * * * * * *")]
    #[case("*/5 * * * *", "0 0/5 * * * * *")]
    #[case("0 */15 */6 * * *", "0 0/15 0/6 * * * *")]
    #[case("0 0 ? 1 0", "0 0 0 ? 1 0 *")]
    #[case("0 0 * * SUN", "0 0 0 * * 0 *")]
    #[case("0 0 * 1 0", "0 0 0 * 1 0 *")]
    #[case("0 0 1 1 ?", "0 0 0 1 1 ? *")]
    #[case("0 0 1 1 *", "0 0 0 1 1 * *")]
    #[case("0 0 12 * * MON", "0 0 12 * * 1 *")]
    #[case("0 0 22 * * 1-5", "0 0 22 * * 1-5 *")]
    #[case("0 0/5 14,18 * * *", "0 0/5 14,18 * * * *")]
    #[case("0 15 10 ? * MON-FRI", "0 15 10 ? * 1-5 *")]
    #[case("1,22,45 5/2 0-15 1-6/2 */6 * 2000", "1,22,45 5/2 0-15 1-6/2 1/6 * 2000")]
    #[case("23 0-20/2 * * *", "0 23 0-20/2 * * * *")]
    #[case("30 0 1 1 * *", "30 0 1 1 * * *")]
    #[case("5,10,15,20 * * * *", "0 5,10,15,20 * * * * *")]
    fn valid_schedules_to_test(#[case] input: &str) {}

    #[apply(valid_schedules_to_test)]
    fn test_schedule_display_and_new(#[case] input: &str, #[case] expected: &str) {
        assert_eq!(Schedule::new(input).unwrap().to_string(), expected);
    }

    #[apply(valid_schedules_to_test)]
    fn test_try_from_string(#[case] input: &str, #[case] _expected: &str) {
        // &str
        let schedule1 = Schedule::new(input).unwrap();
        let schedule2 = Schedule::try_from(input).unwrap();
        assert_eq!(schedule1, schedule2);

        // &String
        let tst_string = String::from(input);
        let schedule2 = Schedule::try_from(&tst_string).unwrap();
        assert_eq!(schedule1, schedule2);

        // String
        let schedule2 = Schedule::try_from(tst_string).unwrap();
        assert_eq!(schedule1, schedule2);
    }

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn test_schedule_iter() {
        let schedule = Schedule::new("0 0 12 * 1 MON 2024").unwrap();
        let mut iter = schedule.iter(&DateTime::parse_from_rfc3339("2024-01-01T00:00:00+00:00").unwrap());

        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-01T12:00:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-08T12:00:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-15T12:00:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-22T12:00:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-29T12:00:00+00:00");
        assert_eq!(iter.next(), None);
    }

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn test_schedule_iter_every_second() {
        let schedule = Schedule::new("* * * * * *").unwrap();
        let mut iter = schedule.iter(&DateTime::parse_from_rfc3339("2024-01-01T00:00:01+00:00").unwrap());

        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-01T00:00:01+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-01T00:00:02+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-01T00:00:03+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-01T00:00:04+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-01T00:00:05+00:00");
    }

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn test_schedule_iter_every_minute() {
        let schedule = Schedule::new("* * * * *").unwrap();
        let mut iter = schedule.iter(&DateTime::parse_from_rfc3339("2024-01-01T00:00:01+00:00").unwrap());

        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-01T00:01:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-01T00:02:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-01T00:03:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-01T00:04:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-01T00:05:00+00:00");
    }

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn test_schedule_iter_every_hour() {
        let schedule = Schedule::new("13 * * * *").unwrap();
        let mut iter = schedule.iter(&DateTime::parse_from_rfc3339("2024-01-01T07:01:01+00:00").unwrap());

        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-01T07:13:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-01T08:13:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-01T09:13:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-01T10:13:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-01T11:13:00+00:00");
    }

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn test_schedule_iter_every_day() {
        let schedule = Schedule::new("22 5 * * *").unwrap();
        let mut iter = schedule.iter(&DateTime::parse_from_rfc3339("2024-01-01T04:01:01+00:00").unwrap());

        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-01T05:22:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-02T05:22:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-03T05:22:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-04T05:22:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-05T05:22:00+00:00");
    }

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn test_schedule_iter_every_month() {
        let schedule = Schedule::new("13 13 12 * *").unwrap();
        let mut iter = schedule.iter(&DateTime::parse_from_rfc3339("2024-01-12T13:13:01+00:00").unwrap());

        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-02-12T13:13:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-03-12T13:13:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-04-12T13:13:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-05-12T13:13:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-06-12T13:13:00+00:00");
    }

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn test_schedule_iter_every_weekday() {
        let schedule = Schedule::new("13 13 ? * *").unwrap();
        let mut iter = schedule.iter(&DateTime::parse_from_rfc3339("2024-01-12T13:13:01+00:00").unwrap());

        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-13T13:13:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-14T13:13:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-15T13:13:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-16T13:13:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-17T13:13:00+00:00");
    }

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn test_schedule_into_iter() {
        let schedule = Schedule::new("0 0 12 * 1 MON 2024").unwrap();
        let mut iter = schedule.into_iter(&DateTime::parse_from_rfc3339("2024-01-01T00:00:00+00:00").unwrap());

        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-01T12:00:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-08T12:00:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-15T12:00:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-22T12:00:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-01-29T12:00:00+00:00");
        assert_eq!(iter.next(), None);
    }

    #[template]
    #[rstest]
    #[case("* * * *")]
    #[case("* * ? * ?")]
    #[case("* * 10 * 1")]
    #[case("* * * * 2/2")]
    #[case("0 1 2 3 * * 1969")]
    #[case("0 0 0 ? * 6-1")]
    fn invalid_schedules_to_test(#[case] input: &str) {}

    #[apply(invalid_schedules_to_test)]
    fn test_invalid_schedule_constructor(#[case] input: &str) {
        assert!(Schedule::new(input).is_err(), "input = {input}");
    }

    #[apply(invalid_schedules_to_test)]
    fn test_try_from_invalid_string(#[case] input: &str) {
        assert!(Schedule::try_from(input).is_err(), "input = {input}");
    }
}
