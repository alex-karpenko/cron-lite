use crate::{
    pattern::{Pattern, PatternItem, PatternType, PatternValueType},
    utils, CronError, Result,
};
use chrono::{DateTime, Datelike, TimeDelta, TimeZone, Timelike};
#[cfg(feature = "tz")]
use chrono_tz::Tz;
use std::{fmt::Display, str::FromStr};

/// Minimum valid year.
pub const MIN_YEAR: u16 = 1970;
/// Maximum valid year.
pub const MAX_YEAR: u16 = 2099;

pub(crate) const MIN_YEAR_STR: &str = "1970";

/// Represents a cron schedule pattern with its methods.
///
/// For cron schedule clarification and usage examples, please refer to the [crate documentation](crate).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(try_from = "String"))]
#[cfg_attr(feature = "serde", serde(into = "String"))]
#[cfg_attr(not(feature = "tz"), derive(PartialOrd, Ord))]
pub struct Schedule {
    year: Pattern,
    month: Pattern,
    dom: Pattern,
    dow: Pattern,
    hour: Pattern,
    minute: Pattern,
    second: Pattern,
    #[cfg(feature = "tz")]
    tz: Option<chrono_tz::Tz>,
}

impl Schedule {
    /// Parses and validates provided `pattern` and constructs [`Schedule`] instance.
    ///
    /// Alternative way to construct [`Schedule`] is to use one of `try_from` or `from_str` methods .
    ///
    /// Returns [`CronError`] in a case provided pattern is unparsable or has format errors.
    pub fn new(pattern: impl Into<String>) -> Result<Self> {
        let pattern = pattern.into();
        let mut elements: Vec<&str> = pattern.split_whitespace().collect();
        #[cfg(feature = "tz")]
        let mut tz = None;

        // Parse and define TZ, if present
        #[cfg(feature = "tz")]
        if elements.len() >= 2 {
            let tz_elements: Vec<&str> = elements[0].split('=').collect();
            if tz_elements.len() == 2 && tz_elements[0].to_uppercase() == "TZ" {
                let tz_str = tz_elements[1];
                if let Ok(tz_value) = Tz::from_str(tz_str) {
                    tz = Some(tz_value);
                    elements.remove(0);
                } else {
                    return Err(CronError::InvalidTimeZone(tz_str.to_string()));
                }
            }
        }

        // Check the number of elements in the provided expression and augment it with defaults.
        if elements.len() == 1 {
            // Check fo aliases
            match elements[0] {
                "@yearly" | "@annually" => elements = vec!["0", "0", "0", "1", "1", "?", "*"],
                "@monthly" => elements = vec!["0", "0", "0", "1", "*", "?", "*"],
                "@weekly" => elements = vec!["0", "0", "0", "?", "*", "0", "*"],
                "@daily" | "@midnight" => elements = vec!["0", "0", "0", "*", "*", "*", "*"],
                "@hourly" => elements = vec!["0", "0", "*", "*", "*", "*", "*"],
                _ => return Err(CronError::InvalidCronSchedule(pattern)),
            }
        } else if elements.len() == 5 {
            elements.insert(0, "0");
            elements.insert(6, "*");
        } else if elements.len() == 6 {
            elements.insert(6, "*");
        } else if elements.len() != 7 {
            return Err(CronError::InvalidCronSchedule(pattern));
        }

        // Parse each element.
        let schedule = Self {
            second: Pattern::parse(PatternType::Seconds, elements[0])?,
            minute: Pattern::parse(PatternType::Minutes, elements[1])?,
            hour: Pattern::parse(PatternType::Hours, elements[2])?,
            dom: Pattern::parse(PatternType::Doms, elements[3])?,
            month: Pattern::parse(PatternType::Months, elements[4])?,
            dow: Pattern::parse(PatternType::Dows, elements[5])?,
            year: Pattern::parse(PatternType::Years, elements[6])?,
            #[cfg(feature = "tz")]
            tz,
        };

        // Validate DOM and DOW relationship.
        match (schedule.dom.pattern(), schedule.dow.pattern()) {
            (PatternItem::Any, PatternItem::Any) => return Err(CronError::InvalidDaysPattern(pattern)),
            (PatternItem::All, _) | (_, PatternItem::All) | (PatternItem::Any, _) | (_, PatternItem::Any) => {}
            (_, _) => {
                return Err(CronError::InvalidDaysPattern(pattern));
            }
        }

        Ok(schedule)
    }

    /// Return time of the upcoming cron event, starting from the provided `current` value (inclusively).
    ///
    /// If `tz` feature isn't enabled,
    /// this method assumes that schedule timezone is the same as timezone of the provided `current` instance.
    ///
    /// If `tz` feature is enabled and [schedule uses timezone](crate#schedule-with-timezone),
    /// then method calculates time of the upcoming event with respect to the schedule's timezone:
    /// - converts `current` into schedule timezone;
    /// - calculates upcoming event time;
    /// - converts obtained upcoming value back to the timezone of the `current` instance.
    ///
    /// Returns `None` if there is no time of the upcoming event.
    #[cfg(not(feature = "tz"))]
    #[inline]
    pub fn upcoming<T: TimeZone>(&self, current: &DateTime<T>) -> Option<DateTime<T>> {
        self.upcoming_impl(current)
    }

    /// Doc is above.
    #[cfg(feature = "tz")]
    pub fn upcoming<Tz: TimeZone>(&self, current: &DateTime<Tz>) -> Option<DateTime<Tz>> {
        if let Some(schedule_tz) = &self.tz {
            let current_tz = current.timezone();
            let current = current.with_timezone(schedule_tz);
            let result = self.upcoming_impl(&current);
            result.map(|dt| dt.with_timezone(&current_tz))
        } else {
            self.upcoming_impl(current)
        }
    }

    /// Return time of the upcoming cron event starting from (including) provided `current` value.
    ///
    /// Returns `None` if there is no upcoming event's time.
    fn upcoming_impl<Tz: TimeZone>(&self, current: &DateTime<Tz>) -> Option<DateTime<Tz>> {
        // Normalize current time to the start of the whole second.
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
        let mut first_iteration = true; // since we don't have `util` loop

        while year.is_none()
            || month.is_none()
            || dom.is_none()
            || hour.is_none()
            || minute.is_none()
            || second.is_none()
            || first_iteration
        {
            first_iteration = false;

            // Jump over to the next possible value is needed.
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

            // Calculate the next possible valid date/time from the current,
            // with leaping to the first day/hour/... when the current element was changed.
            year = self.year.next(&mut current);
            if year.is_some() {
                month = self.month.next(&mut current);
                year = Some(current.year() as PatternValueType);
                if month.is_some() {
                    // Prepare day od month depending on DOM/DOW pattern types.
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

    /// Returns iterator of events starting from `current` (inclusively).
    #[inline]
    pub fn iter<Tz: TimeZone>(&self, current: &DateTime<Tz>) -> impl Iterator<Item = DateTime<Tz>> {
        ScheduleIterator {
            schedule: self.clone(),
            next: self.upcoming(current),
        }
    }

    /// Consumes [`Schedule`] and returns iterator of events starting from `current` (inclusively).
    #[inline]
    pub fn into_iter<Tz: TimeZone>(self, current: &DateTime<Tz>) -> impl Iterator<Item = DateTime<Tz>> {
        let next = self.upcoming(current);
        ScheduleIterator { schedule: self, next }
    }
}

/// Contains iterator state.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(not(feature = "tz"), derive(PartialOrd, Ord))]
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

impl From<Schedule> for String {
    fn from(value: Schedule) -> Self {
        value.to_string()
    }
}

impl From<&Schedule> for String {
    fn from(value: &Schedule) -> Self {
        value.to_string()
    }
}

impl TryFrom<String> for Schedule {
    type Error = CronError;

    fn try_from(value: String) -> Result<Self> {
        Self::new(value)
    }
}

impl TryFrom<&String> for Schedule {
    type Error = CronError;

    fn try_from(value: &String) -> Result<Self> {
        Self::new(value)
    }
}

impl TryFrom<&str> for Schedule {
    type Error = CronError;

    fn try_from(value: &str) -> Result<Self> {
        Self::new(value)
    }
}

impl FromStr for Schedule {
    type Err = CronError;

    fn from_str(s: &str) -> Result<Self> {
        Self::new(s)
    }
}

impl Display for Schedule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        #[cfg(not(feature = "tz"))]
        {
            write!(
                f,
                "{} {} {} {} {} {} {}",
                self.second, self.minute, self.hour, self.dom, self.month, self.dow, self.year
            )
        }

        #[cfg(feature = "tz")]
        if let Some(tz) = self.tz {
            write!(
                f,
                "TZ={} {} {} {} {} {} {} {}",
                tz, self.second, self.minute, self.hour, self.dom, self.month, self.dow, self.year
            )
        } else {
            write!(
                f,
                "{} {} {} {} {} {} {}",
                self.second, self.minute, self.hour, self.dom, self.month, self.dow, self.year
            )
        }
    }
}

/// Increments current year and set all other elements to the first valid value.
#[inline]
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

/// Increments current month and set all other elements to the first valid value.
#[inline]
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

/// Increments current day of month and set all other elements to the first valid value.
#[inline]
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

/// Increments current hour and set all other elements to the first valid value.
#[inline]
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

/// Increments current minute and set all other elements to the first valid value.
#[inline]
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
    #[case("0 0 9 * * 1#1", "2024-04-12T00:00:00Z", "2024-05-06T09:00:00+00:00")]
    #[case("0 0 9 * * 6#4", "2024-11-30T09:00:00Z", "2024-12-28T09:00:00+00:00")]
    #[case("0 0 9-17 * * 1-5", "2024-01-01T08:00:00Z", "2024-01-01T09:00:00+00:00")]
    #[case("0 0 9-17 * * 1-5", "2024-01-01T17:00:01Z", "2024-01-02T09:00:00+00:00")]
    #[case("0 15,45 9-17 * * 1-5", "2024-01-01T09:00:00Z", "2024-01-01T09:15:00+00:00")]
    #[case("0 15,45 9-17 * * 1-5", "2024-01-01T09:15:01Z", "2024-01-01T09:45:00+00:00")]
    #[case("0 30 0 1 * *", "2024-01-01T00:00:00Z", "2024-01-01T00:30:00+00:00")]
    #[case("30 0 0 1 * *", "2024-01-01T00:00:00Z", "2024-01-01T00:00:30+00:00")]
    #[case("30 0 0 1 * *", "2024-01-01T00:00:30Z", "2024-01-01T00:00:30+00:00")]
    #[case("30 0 0 1 * *", "2024-01-01T00:00:30.001Z", "2024-02-01T00:00:30+00:00")]
    #[case("25 * * * *", "2024-01-01T00:21:21Z", "2024-01-01T00:25:00+00:00")]
    #[case("1 2 29-31 * *", "2024-01-01T00:00:21Z", "2024-01-29T02:01:00+00:00")]
    #[case("1 2 29-31 * *", "2024-01-31T00:00:21Z", "2024-01-31T02:01:00+00:00")]
    #[case("1 2 29-31 * *", "2024-02-01T00:00:21Z", "2024-02-29T02:01:00+00:00")]
    #[case("1 2 29-31 * *", "2024-03-31T00:00:21Z", "2024-03-31T02:01:00+00:00")]
    #[case("1 2 29-31 * *", "2025-01-01T00:00:21Z", "2025-01-29T02:01:00+00:00")]
    #[case("1 2 29-31 * *", "2025-02-01T00:00:21Z", "2025-03-29T02:01:00+00:00")]
    #[case("1 2 29-31 * *", "2025-03-31T00:00:21Z", "2025-03-31T02:01:00+00:00")]
    #[case("@yearly", "2025-03-31T00:00:21Z", "2026-01-01T00:00:00+00:00")]
    #[case("@annually", "2025-03-31T00:00:21Z", "2026-01-01T00:00:00+00:00")]
    #[case("@monthly", "2025-03-31T00:00:21Z", "2025-04-01T00:00:00+00:00")]
    #[case("@weekly", "2025-03-31T00:00:21Z", "2025-04-06T00:00:00+00:00")]
    #[case("@daily", "2025-03-31T00:00:21Z", "2025-04-01T00:00:00+00:00")]
    #[case("@midnight", "2025-03-31T00:00:21Z", "2025-04-01T00:00:00+00:00")]
    #[case("@hourly", "2025-03-31T00:00:21Z", "2025-03-31T01:00:00+00:00")]
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
    #[case("@yearly", "0 0 0 1 1 ? *")]
    #[case("@annually", "0 0 0 1 1 ? *")]
    #[case("@monthly", "0 0 0 1 * ? *")]
    #[case("@weekly", "0 0 0 ? * 0 *")]
    #[case("@daily", "0 0 0 * * * *")]
    #[case("@midnight", "0 0 0 * * * *")]
    #[case("@hourly", "0 0 * * * * *")]
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

        // from_str
        let schedule2 = Schedule::from_str(input).unwrap();
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
    fn test_schedule_iter_every_year() {
        let schedule = Schedule::new("30 12 22 6 ?").unwrap();
        let mut iter = schedule.iter(&DateTime::parse_from_rfc3339("2021-01-12T13:13:01+00:00").unwrap());

        assert_eq!(iter.next().unwrap().to_rfc3339(), "2021-06-22T12:30:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2022-06-22T12:30:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2023-06-22T12:30:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2024-06-22T12:30:00+00:00");
        assert_eq!(iter.next().unwrap().to_rfc3339(), "2025-06-22T12:30:00+00:00");
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
    #[case("@minutely")]
    fn invalid_schedules_to_test(#[case] input: &str) {}

    #[apply(invalid_schedules_to_test)]
    fn test_invalid_schedule_constructor(#[case] input: &str) {
        assert!(Schedule::new(input).is_err(), "input = {input}");
    }

    #[apply(invalid_schedules_to_test)]
    fn test_try_from_invalid_string(#[case] input: &str) {
        assert!(Schedule::try_from(input).is_err(), "input = {input}");
        assert!(Schedule::from_str(input).is_err(), "input = {input}");
    }

    #[rstest]
    // leap year
    #[case("0 0 0 29 2 ? 2024", "2024-02-28T23:59:59Z", "2024-02-29T00:00:00+00:00")]
    #[case("0 0 0 29 2 ? 2024-2099", "2024-03-01T23:59:59Z", "2028-02-29T00:00:00+00:00")]
    #[case("0 0 0 29 2 ? 2025-2099", "2024-02-01T23:59:59Z", "2028-02-29T00:00:00+00:00")]
    #[case("0 0 0 29 2 ? 1971/7", "1970-02-01T23:59:59Z", "1992-02-29T00:00:00+00:00")]
    #[case("0 0 0 29 2 ? 2024-2027", "2024-02-29T00:00:01Z", "None")]
    // end of month rollover
    #[case("0 0 0 1 * ? 2024", "2024-01-31T23:59:59Z", "2024-02-01T00:00:00+00:00")]
    #[case("0 0 0 1 * ? 2024", "2024-02-28T23:59:59Z", "2024-03-01T00:00:00+00:00")]
    #[case("0 0 0 1 * ? 2024", "2024-02-29T23:59:59Z", "2024-03-01T00:00:00+00:00")]
    #[case("0 0 0 1 * ? 2024", "2024-03-31T23:59:59Z", "2024-04-01T00:00:00+00:00")]
    #[case("0 0 0 1 * ? 2024", "2024-04-30T23:59:59Z", "2024-05-01T00:00:00+00:00")]
    #[case("0 0 0 1 * ? 2024", "2024-11-30T23:59:59Z", "2024-12-01T00:00:00+00:00")]
    // end-of-year rollover
    #[case("0 0 0 1 1 ? 2025", "2024-12-31T23:59:59Z", "2025-01-01T00:00:00+00:00")]
    // last day of month
    #[case("0 0 0 L 2 ? 2024", "2024-02-28T23:59:59Z", "2024-02-29T00:00:00+00:00")]
    #[case("0 0 0 L 2 ? 2025", "2024-02-28T23:59:59Z", "2025-02-28T00:00:00+00:00")]
    // last weekday of month
    #[case("0 0 0 ? 2 4L 2024", "2024-02-28T23:59:59Z", "2024-02-29T00:00:00+00:00")]
    // weekday nearest to specific day
    #[case("0 0 0 15W * ? 2024", "2024-01-14T23:59:59Z", "2024-01-15T00:00:00+00:00")]
    // nth day of the week
    #[case("0 0 0 ? * 1#3 2024", "2024-01-20T23:59:59Z", "2024-02-19T00:00:00+00:00")]
    #[timeout(Duration::from_secs(1))]
    fn test_edge_cases(#[case] pattern: &str, #[case] current: &str, #[case] expected: &str) {
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

    #[apply(valid_schedules_to_test)]
    fn test_schedule_to_string(#[case] input: &str, #[case] expected: &str) {
        let schedule = Schedule::new(input).unwrap();

        let string: String = (&schedule).into();
        assert_eq!(string, expected);

        let string: String = schedule.into();
        assert_eq!(string, expected);
    }

    #[cfg(feature = "tz")]
    mod tz {
        use super::super::*;
        use rstest::rstest;
        use rstest_reuse::{apply, template};
        use std::time::Duration;

        #[template]
        #[rstest]
        #[case("TZ=Europe/Kyiv * * * * * * *", "TZ=Europe/Kyiv * * * * * * *")]
        #[case("TZ=Europe/London * * * * * *", "TZ=Europe/London * * * * * * *")]
        #[case("TZ=UTC * * * * *", "TZ=UTC 0 * * * * * *")]
        #[case("TZ=US/Pacific */5 * * * *", "TZ=US/Pacific 0 0/5 * * * * *")]
        #[case("TZ=EET 0 */15 */6 * * *", "TZ=EET 0 0/15 0/6 * * * *")]
        #[case("TZ=Asia/Tokyo @yearly", "TZ=Asia/Tokyo 0 0 0 1 1 ? *")]
        #[case("Tz=Asia/Tokyo @yearly", "TZ=Asia/Tokyo 0 0 0 1 1 ? *")]
        #[case("tz=Asia/Tokyo @yearly", "TZ=Asia/Tokyo 0 0 0 1 1 ? *")]
        #[case("tz=Europe/Paris @yearly", "TZ=Europe/Paris 0 0 0 1 1 ? *")]
        fn valid_schedules_to_test(#[case] input: &str, #[case] expected: &str) {}

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

            // from_str
            let schedule2 = Schedule::from_str(input).unwrap();
            assert_eq!(schedule1, schedule2);
        }

        #[template]
        #[rstest]
        #[case("TZ * * * *")]
        #[case("TZ= * * ? * ?")]
        #[case("tz=UTC * * 10 * 1")]
        #[case("TZ=Aaa/Bbb * * * * 2/2")]
        #[case("TZ=Aaa/Bbb * * * * *")]
        #[case("TZ =UTC * * * * *")]
        #[case("TZ= UTC * * * * *")]
        #[case("TZ = UTC * * * * *")]
        #[case("TZ= 0 0 0 ? * 1-6")]
        #[case("tz= @hourly")]
        fn invalid_schedules_to_test(#[case] input: &str) {}

        #[apply(invalid_schedules_to_test)]
        fn test_invalid_schedule_constructor(#[case] input: &str) {
            assert!(Schedule::new(input).is_err(), "input = {input}");
        }

        #[apply(invalid_schedules_to_test)]
        fn test_try_from_invalid_string(#[case] input: &str) {
            assert!(Schedule::try_from(input).is_err(), "input = {input}");
            assert!(Schedule::from_str(input).is_err(), "input = {input}");
        }

        #[rstest]
        #[case("TZ=Europe/Kyiv @monthly", "2025-03-31T00:00:21Z", "2025-03-31T21:00:00+00:00")]
        #[case("TZ=Europe/Kyiv @monthly", "2025-03-31T00:00:21+02:00", "2025-03-31T23:00:00+02:00")]
        #[case("TZ=Europe/Kyiv @monthly", "2025-11-30T00:00:21Z", "2025-11-30T22:00:00+00:00")]
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
    }
}
