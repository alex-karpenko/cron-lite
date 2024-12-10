use crate::{
    schedule::{MAX_YEAR, MIN_YEAR, MIN_YEAR_STR},
    series::SeriesWithStep,
    utils::{self, days_in_month},
    CronError, Result,
};
use chrono::{DateTime, Datelike, TimeZone, Timelike};
use std::{collections::BTreeSet, fmt::Display};

pub(crate) type PatternValueType = u16;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Pattern {
    type_: PatternType,
    pattern: PatternItem,
}

impl Pattern {
    #[inline]
    pub(crate) fn pattern(&self) -> &PatternItem {
        &self.pattern
    }

    pub(crate) fn parse(type_: PatternType, input: &str) -> Result<Self> {
        if input.is_empty() {
            return Err(CronError::InvalidCronPattern(input.to_owned(), type_.to_string()));
        }

        let mut error_indicator = Ok(());
        let mut splitted = input
            .split(',')
            .map(|value| {
                if value == "*" {
                    Ok(PatternItem::All)
                } else if value == "?" && [PatternType::Dows, PatternType::Doms].contains(&type_) {
                    Ok(PatternItem::Any)
                } else if value.ends_with('L') && type_ == PatternType::Dows {
                    let value = value.trim_end_matches('L');
                    Ok(PatternItem::LastDow(type_.parse(value)?))
                } else if value == "L" && type_ == PatternType::Doms {
                    Ok(PatternItem::LastDom)
                } else if value.ends_with('W') && type_ == PatternType::Doms {
                    let value = value.trim_end_matches('W');
                    Ok(PatternItem::Weekday(type_.parse(value)?))
                } else if value.contains('/') && type_ != PatternType::Dows {
                    let (base, repeater) = value.split_once('/').unwrap();
                    let base = if base == "*" {
                        match type_ {
                            PatternType::Doms | PatternType::Months => "1",
                            PatternType::Years => MIN_YEAR_STR,
                            _ => "0",
                        }
                    } else {
                        base
                    };

                    let repeater = if let Ok(repeater) = repeater.parse() {
                        let (_min, max) = type_.min_max();
                        if repeater < 2 || repeater > max {
                            return Err(CronError::InvalidRepeatingPattern(value.to_owned(), type_.to_string()));
                        }
                        repeater
                    } else {
                        return Err(CronError::InvalidRepeatingPattern(value.to_owned(), type_.to_string()));
                    };

                    if base.contains('-') {
                        let (start, end) = base.split_once('-').unwrap();
                        let start = type_.parse(start)?;
                        let end = type_.parse(end)?;
                        if start >= end {
                            return Err(CronError::InvalidRangeValue(value.to_owned(), type_.to_string()));
                        }
                        Ok(PatternItem::RepeatingRange(start, end, repeater))
                    } else {
                        Ok(PatternItem::RepeatingValue(type_.parse(base)?, repeater))
                    }
                } else if value.contains('-') {
                    let (start, end) = value.split_once('-').unwrap();
                    let start = type_.parse(start)?;
                    let end = type_.parse(end)?;
                    if start >= end {
                        return Err(CronError::InvalidRangeValue(value.to_owned(), type_.to_string()));
                    }
                    Ok(PatternItem::Range(start, end))
                } else if value.contains('#') && type_ == PatternType::Dows {
                    let mut parts = value.split('#');
                    let dow = parts.next().unwrap();
                    let number = parts.next().unwrap();
                    let number = utils::parse_digital_value(number, 1, 4);
                    if number.is_none() {
                        return Err(CronError::InvalidDayOfWeekValue(value.to_owned(), type_.to_string()));
                    }
                    Ok(PatternItem::Hash(type_.parse(dow)?, number.unwrap()))
                } else {
                    Ok(PatternItem::Particular(type_.parse(value)?))
                }
            })
            .scan(&mut error_indicator, |err, res| match res {
                Ok(o) => Some(o),
                Err(e) => {
                    **err = Err(e);
                    None
                }
            })
            .collect::<Vec<_>>();

        error_indicator?;

        if splitted.is_empty()
            || (splitted.len() > 1 && (splitted.contains(&PatternItem::All) || splitted.contains(&PatternItem::Any)))
        {
            return Err(CronError::InvalidCronPattern(input.to_owned(), type_.to_string()));
        }

        let pattern = if splitted.len() > 1 {
            PatternItem::List(splitted)
        } else {
            splitted.remove(0)
        };

        Ok(Self { type_, pattern })
    }

    pub(crate) fn next<Tz: TimeZone>(&self, current: &mut DateTime<Tz>) -> Option<PatternValueType> {
        let max = if self.type_ == PatternType::Doms || self.type_ == PatternType::Dows {
            days_in_month(current.year() as PatternValueType, current.month() as PatternValueType)
        } else {
            let (_min, max) = self.type_.min_max();
            max
        };

        let start = match self.type_ {
            PatternType::Seconds => current.second() as PatternValueType,
            PatternType::Minutes => current.minute() as PatternValueType,
            PatternType::Hours => current.hour() as PatternValueType,
            PatternType::Doms | PatternType::Dows => current.day() as PatternValueType,
            PatternType::Months => current.month() as PatternValueType,
            PatternType::Years => current.year() as PatternValueType,
        };

        let value: Option<PatternValueType> = match &self.pattern {
            PatternItem::List(values) => {
                let mut min: Option<PatternValueType> = None;

                for pattern in values {
                    let item = Self {
                        type_: self.type_,
                        pattern: pattern.clone(),
                    };
                    let mut current = current.clone();
                    if let Some(next) = item.next(&mut current) {
                        if let Some(prev) = min {
                            if next < prev {
                                min = Some(next);
                            }
                        } else {
                            min = Some(next)
                        }
                    }
                }
                min
            }
            PatternItem::All => Some(start),
            PatternItem::Particular(value) if self.type_ != PatternType::Dows => {
                if *value >= start && *value <= max {
                    Some(*value)
                } else {
                    None
                }
            }
            PatternItem::Particular(value) if self.type_ == PatternType::Dows => (start..=max).find(|&day| {
                utils::day_of_week(
                    current.year() as PatternValueType,
                    current.month() as PatternValueType,
                    day,
                ) == *value
            }),
            PatternItem::Range(begin, end) if self.type_ != PatternType::Dows => {
                SeriesWithStep::new(*begin, *end, 1, *begin)
                    .filter(|v| *v >= start && *v <= max)
                    .collect::<BTreeSet<_>>()
                    .first()
                    .copied()
            }
            PatternItem::Range(first_dow, last_dow) if self.type_ == PatternType::Dows => (start..=max).find(|&day| {
                let dow = utils::day_of_week(
                    current.year() as PatternValueType,
                    current.month() as PatternValueType,
                    day,
                );
                dow >= *first_dow && dow <= *last_dow
            }),
            PatternItem::RepeatingValue(range_start, step) => {
                SeriesWithStep::new(*range_start, max, *step, *range_start)
                    .filter(|v| *v >= start)
                    .collect::<BTreeSet<_>>()
                    .first()
                    .copied()
            }

            PatternItem::RepeatingRange(min, max, step) => SeriesWithStep::new(*min, *max, *step, *min)
                .filter(|v| *v >= start)
                .collect::<BTreeSet<_>>()
                .first()
                .copied(),
            PatternItem::LastDow(dow) => {
                let last_dow = utils::last_dow(
                    current.year() as PatternValueType,
                    current.month() as PatternValueType,
                    *dow,
                );
                if last_dow >= current.day() as PatternValueType {
                    Some(last_dow)
                } else {
                    None
                }
            }
            PatternItem::LastDom => Some(days_in_month(
                current.year() as PatternValueType,
                current.month() as PatternValueType,
            )),
            PatternItem::Weekday(dom) => {
                let weekday = utils::nearest_weekday(
                    current.year() as PatternValueType,
                    current.month() as PatternValueType,
                    *dom,
                );
                if weekday >= start {
                    Some(weekday)
                } else {
                    None
                }
            }
            PatternItem::Hash(dow, number) => {
                let day = utils::nth_dow(
                    current.year() as PatternValueType,
                    current.month() as PatternValueType,
                    *dow,
                    *number,
                );
                if day >= current.day() as PatternValueType {
                    Some(day)
                } else {
                    None
                }
            }
            PatternItem::Any => None,
            _ => unreachable!(),
        };

        if let Some(value) = value {
            if value > start {
                match self.type_ {
                    PatternType::Years => {
                        *current = current
                            .with_day(1)?
                            .with_month(1)?
                            .with_year(value as i32)?
                            .with_hour(0)?
                            .with_minute(0)?
                            .with_second(0)?;
                    }
                    PatternType::Months => {
                        *current = current
                            .with_day(1)?
                            .with_month(value as u32)?
                            .with_hour(0)?
                            .with_minute(0)?
                            .with_second(0)?;
                    }
                    PatternType::Doms | PatternType::Dows => {
                        *current = current
                            .with_day(value as u32)?
                            .with_hour(0)?
                            .with_minute(0)?
                            .with_second(0)?;
                    }
                    PatternType::Hours => {
                        *current = current.with_hour(value as u32)?.with_minute(0)?.with_second(0)?;
                    }
                    PatternType::Minutes => {
                        *current = current.with_minute(value as u32)?.with_second(0)?;
                    }
                    PatternType::Seconds => {
                        *current = current.with_second(value as u32)?;
                    }
                }
            }
        }

        value
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.pattern)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum PatternType {
    Seconds,
    Minutes,
    Hours,
    Doms,
    Months,
    Dows,
    Years,
}

impl Display for PatternType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Seconds => "seconds",
                Self::Minutes => "minutes",
                Self::Hours => "hours",
                Self::Doms => "days of month",
                Self::Months => "months",
                Self::Dows => "days of week",
                Self::Years => "years",
            }
        )
    }
}

impl PatternType {
    const DAYS_OF_WEEK: [&str; 7] = ["SUN", "MON", "TUE", "WED", "THU", "FRI", "SAT"];
    const MONTHS: [&str; 12] = [
        "JAN", "FEB", "MAR", "APR", "MAY", "JUN", "JUL", "AUG", "SEP", "OCT", "NOV", "DEC",
    ];

    fn min_max(&self) -> (PatternValueType, PatternValueType) {
        match self {
            Self::Seconds => (0, 59),
            Self::Minutes => (0, 59),
            Self::Hours => (0, 23),
            Self::Doms => (1, 31),
            Self::Months => (1, 12),
            Self::Dows => (0, 6),
            Self::Years => (MIN_YEAR, MAX_YEAR),
        }
    }

    fn parse(&self, input: &str) -> Result<PatternValueType> {
        let (min, max) = self.min_max();
        let (variants, starter_shift) = match self {
            PatternType::Seconds
            | PatternType::Minutes
            | PatternType::Hours
            | PatternType::Doms
            | PatternType::Years => (vec![], 0),
            PatternType::Months => (Self::MONTHS.to_vec(), 1),
            PatternType::Dows => (Self::DAYS_OF_WEEK.to_vec(), 0),
        };

        match self {
            PatternType::Seconds
            | PatternType::Minutes
            | PatternType::Hours
            | PatternType::Doms
            | PatternType::Years => {
                if let Some(value) = utils::parse_digital_value(input, min, max) {
                    Ok(value)
                } else {
                    Err(CronError::InvalidDigitalValue(input.to_owned(), self.to_string()))
                }
            }
            PatternType::Months | PatternType::Dows => {
                if let Some(value) = utils::parse_digital_value(input, min, max) {
                    Ok(value)
                } else if let Some(value) = utils::parse_string_value(input, &variants) {
                    Ok(value + starter_shift)
                } else {
                    Err(CronError::InvalidMnemonicValue(input.to_owned(), self.to_string()))
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum PatternItem {
    All,
    Any,
    Particular(PatternValueType),
    List(Vec<PatternItem>),
    // start-finish
    Range(PatternValueType, PatternValueType),
    // start/step
    RepeatingValue(PatternValueType, PatternValueType),
    // start-finish/step
    RepeatingRange(PatternValueType, PatternValueType, PatternValueType),
    // weekday
    LastDow(PatternValueType),
    LastDom,
    // month
    Weekday(PatternValueType),
    // weekday#nth
    Hash(PatternValueType, PatternValueType),
}

impl Display for PatternItem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PatternItem::All => write!(f, "*"),
            PatternItem::Any => write!(f, "?"),
            PatternItem::LastDow(dow) => write!(f, "{}L", dow),
            PatternItem::LastDom => write!(f, "L"),
            PatternItem::Weekday(dom) => write!(f, "{}W", dom),
            PatternItem::RepeatingValue(value, repeater) => write!(f, "{}/{}", value, repeater),
            PatternItem::RepeatingRange(start, end, repeater) => {
                write!(f, "{}-{}/{}", start, end, repeater)
            }
            PatternItem::Range(start, end) => write!(f, "{}-{}", start, end),
            PatternItem::Particular(value) => write!(f, "{}", value),
            PatternItem::List(vec) => {
                let values = vec.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(",");
                write!(f, "{}", values)
            }
            PatternItem::Hash(dow, number) => write!(f, "{}#{}", dow, number),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;
    use std::time::Duration;

    const MAX_YEAR_STR: &str = "2099";

    #[rstest]
    #[case(PatternType::Seconds)]
    #[case(PatternType::Minutes)]
    #[case(PatternType::Hours)]
    #[case(PatternType::Doms)]
    #[case(PatternType::Months)]
    #[case(PatternType::Dows)]
    #[case(PatternType::Years)]
    fn test_pattern_item_display(#[case] type_: PatternType) {
        let test_cases = vec![
            (PatternItem::All, "*"),
            (PatternItem::Any, "?"),
            (PatternItem::Particular(5), "5"),
            (
                PatternItem::List(vec![PatternItem::Particular(3), PatternItem::Particular(1)]),
                "3,1",
            ),
            (PatternItem::Range(2, 5), "2-5"),
            (PatternItem::RepeatingValue(15, 30), "15/30"),
            (PatternItem::RepeatingRange(0, 30, 5), "0-30/5"),
            (PatternItem::LastDow(1), "1L"),
            (PatternItem::LastDom, "L"),
            (PatternItem::Weekday(15), "15W"),
            (PatternItem::Hash(3, 2), "3#2"),
            (
                PatternItem::List(vec![
                    PatternItem::Particular(3),
                    PatternItem::Particular(1),
                    PatternItem::Range(2, 5),
                    PatternItem::RepeatingValue(12, 3),
                    PatternItem::RepeatingRange(10, 22, 4),
                ]),
                "3,1,2-5,12/3,10-22/4",
            ),
        ];

        for (item, expected) in test_cases {
            assert_eq!(item.to_string(), expected);
            let pattern = Pattern { type_, pattern: item };
            assert_eq!(pattern.to_string(), expected);
        }
    }

    #[rstest]
    #[case(PatternType::Seconds)]
    #[case(PatternType::Minutes)]
    fn test_pattern_item_parse_valid_1(#[case] type_: PatternType) {
        let test_cases = vec![
            ("*", PatternItem::All),
            ("5", PatternItem::Particular(5)),
            (
                "3,1",
                PatternItem::List(vec![PatternItem::Particular(3), PatternItem::Particular(1)]),
            ),
            ("2-5", PatternItem::Range(2, 5)),
            ("15/30", PatternItem::RepeatingValue(15, 30)),
            ("*/10", PatternItem::RepeatingValue(0, 10)),
            ("0/5", PatternItem::RepeatingValue(0, 5)),
            ("0-30/5", PatternItem::RepeatingRange(0, 30, 5)),
            (
                "3,1,2-5,12/3,10-22/4",
                PatternItem::List(vec![
                    PatternItem::Particular(3),
                    PatternItem::Particular(1),
                    PatternItem::Range(2, 5),
                    PatternItem::RepeatingValue(12, 3),
                    PatternItem::RepeatingRange(10, 22, 4),
                ]),
            ),
        ];

        for (item, expected) in test_cases {
            let pattern = Pattern::parse(type_, item);
            assert!(
                pattern.is_ok(),
                "type = {type_:?}, item = {item}, error = {}",
                pattern.err().unwrap()
            );
            let pattern = pattern.unwrap();
            assert_eq!(pattern.pattern, expected, "item = {item}");
        }
    }

    #[test]
    fn test_pattern_item_parse_valid_dows() {
        let test_cases = vec![
            ("*", PatternItem::All),
            ("?", PatternItem::Any),
            ("5", PatternItem::Particular(5)),
            ("Mon", PatternItem::Particular(1)),
            ("WED", PatternItem::Particular(3)),
            ("fri", PatternItem::Particular(5)),
            ("sun#1", PatternItem::Hash(0, 1)),
            ("3#2", PatternItem::Hash(3, 2)),
            ("4L", PatternItem::LastDow(4)),
            (
                "3,1",
                PatternItem::List(vec![PatternItem::Particular(3), PatternItem::Particular(1)]),
            ),
            (
                "MON,FRI",
                PatternItem::List(vec![PatternItem::Particular(1), PatternItem::Particular(5)]),
            ),
            ("2-5", PatternItem::Range(2, 5)),
            ("Wed-sat", PatternItem::Range(3, 6)),
            (
                "3,1,2-5",
                PatternItem::List(vec![
                    PatternItem::Particular(3),
                    PatternItem::Particular(1),
                    PatternItem::Range(2, 5),
                ]),
            ),
            (
                "WEd,mon,tue-fri",
                PatternItem::List(vec![
                    PatternItem::Particular(3),
                    PatternItem::Particular(1),
                    PatternItem::Range(2, 5),
                ]),
            ),
        ];

        for (item, expected) in test_cases {
            let pattern = Pattern::parse(PatternType::Dows, item);
            assert!(pattern.is_ok(), "item = {item}, error = {}", pattern.err().unwrap());
            let pattern = pattern.unwrap();
            assert_eq!(pattern.pattern, expected, "item = {item}");
        }
    }

    #[test]
    fn test_pattern_item_parse_valid_months() {
        let test_cases = vec![
            ("*", PatternItem::All),
            ("5", PatternItem::Particular(5)),
            ("Jan", PatternItem::Particular(1)),
            ("JUN", PatternItem::Particular(6)),
            ("dec", PatternItem::Particular(12)),
            (
                "3,1",
                PatternItem::List(vec![PatternItem::Particular(3), PatternItem::Particular(1)]),
            ),
            (
                "mar,may",
                PatternItem::List(vec![PatternItem::Particular(3), PatternItem::Particular(5)]),
            ),
            ("2-5", PatternItem::Range(2, 5)),
            ("auG-DEC", PatternItem::Range(8, 12)),
            (
                "3,1,2-5",
                PatternItem::List(vec![
                    PatternItem::Particular(3),
                    PatternItem::Particular(1),
                    PatternItem::Range(2, 5),
                ]),
            ),
            (
                "feb,mar,oct-nov",
                PatternItem::List(vec![
                    PatternItem::Particular(2),
                    PatternItem::Particular(3),
                    PatternItem::Range(10, 11),
                ]),
            ),
            ("2/2", PatternItem::RepeatingValue(2, 2)),
            ("mar/2", PatternItem::RepeatingValue(3, 2)),
            ("*/5", PatternItem::RepeatingValue(1, 5)),
            ("1/6", PatternItem::RepeatingValue(1, 6)),
            ("apr/6", PatternItem::RepeatingValue(4, 6)),
            ("1-12/4", PatternItem::RepeatingRange(1, 12, 4)),
            ("jun-sep/2", PatternItem::RepeatingRange(6, 9, 2)),
            (
                "3,1,2-5,2/6,10-12/4,*/4,apR/2",
                PatternItem::List(vec![
                    PatternItem::Particular(3),
                    PatternItem::Particular(1),
                    PatternItem::Range(2, 5),
                    PatternItem::RepeatingValue(2, 6),
                    PatternItem::RepeatingRange(10, 12, 4),
                    PatternItem::RepeatingValue(1, 4),
                    PatternItem::RepeatingValue(4, 2),
                ]),
            ),
        ];

        for (item, expected) in test_cases {
            let pattern = Pattern::parse(PatternType::Months, item);
            assert!(pattern.is_ok(), "item = {item}, error = {}", pattern.err().unwrap());
            let pattern = pattern.unwrap();
            assert_eq!(pattern.pattern, expected, "item = {item}");
        }
    }

    #[test]
    fn test_pattern_item_parse_valid_doms() {
        let test_cases = vec![
            ("*", PatternItem::All),
            ("?", PatternItem::Any),
            ("5", PatternItem::Particular(5)),
            ("L", PatternItem::LastDom),
            ("15W", PatternItem::Weekday(15)),
            (
                "3,1",
                PatternItem::List(vec![PatternItem::Particular(3), PatternItem::Particular(1)]),
            ),
            ("2-5", PatternItem::Range(2, 5)),
            ("15/30", PatternItem::RepeatingValue(15, 30)),
            ("*/10", PatternItem::RepeatingValue(1, 10)),
            ("1/11", PatternItem::RepeatingValue(1, 11)),
            ("1-30/5", PatternItem::RepeatingRange(1, 30, 5)),
            (
                "3,1,2-5,12/3,10-22/4",
                PatternItem::List(vec![
                    PatternItem::Particular(3),
                    PatternItem::Particular(1),
                    PatternItem::Range(2, 5),
                    PatternItem::RepeatingValue(12, 3),
                    PatternItem::RepeatingRange(10, 22, 4),
                ]),
            ),
        ];

        for (item, expected) in test_cases {
            let pattern = Pattern::parse(PatternType::Doms, item);
            assert!(pattern.is_ok(), "item = {item}, error = {}", pattern.err().unwrap());
            let pattern = pattern.unwrap();
            assert_eq!(pattern.pattern, expected, "item = {item}");
        }
    }

    #[test]
    fn test_pattern_item_parse_valid_year() {
        let test_cases = vec![
            ("*", PatternItem::All),
            ("1975", PatternItem::Particular(1975)),
            (
                "2000,2001",
                PatternItem::List(vec![PatternItem::Particular(2000), PatternItem::Particular(2001)]),
            ),
            ("1982-1999", PatternItem::Range(1982, 1999)),
            ("2015/30", PatternItem::RepeatingValue(2015, 30)),
            ("*/10", PatternItem::RepeatingValue(1970, 10)),
            ("2011/11", PatternItem::RepeatingValue(2011, 11)),
            ("1971-2030/5", PatternItem::RepeatingRange(1971, 2030, 5)),
            (
                "2003,2001,2002-2005,2012/3,2010-2022/4",
                PatternItem::List(vec![
                    PatternItem::Particular(2003),
                    PatternItem::Particular(2001),
                    PatternItem::Range(2002, 2005),
                    PatternItem::RepeatingValue(2012, 3),
                    PatternItem::RepeatingRange(2010, 2022, 4),
                ]),
            ),
        ];

        for (item, expected) in test_cases {
            let pattern = Pattern::parse(PatternType::Years, item);
            assert!(pattern.is_ok(), "item = {item}, error = {}", pattern.err().unwrap());
            let pattern = pattern.unwrap();
            assert_eq!(pattern.pattern, expected, "item = {item}");
        }
    }

    #[rstest]
    #[case(PatternType::Seconds, vec!["2-2/2", "5-1/2", "*,1", "1-1", "5-1", "W", "?", "L", "", " ", ",", "/", "*/", "5/", "-", "1-", "a,b,c", "a-b,c", "1-2-3", ",1", "1,", "1, 2", "1#1", "0/-5", "0/0", "0/60", "60", "0/1"])]
    #[case(PatternType::Minutes, vec!["2-2/2", "5-1/2", "*,1", "1-1", "5-1", "W", "?", "L", "", " ", ",", "/", "*/", "5/", "-", "1-", "a,b,c", "a-b,c", "1-2-3", ",1", "1,", "1, 2", "1#1", "0/-5", "0/0", "0/60", "60", "0/1"])]
    #[case(PatternType::Hours,   vec!["2-2/2", "5-1/2", "*,1", "1-1", "5-1", "W", "?", "L", "", " ", ",", "/", "*/", "5/", "-", "1-", "a,b,c", "a-b,c", "1-2-3", ",1", "1,", "1, 2", "1#1", "0/-5", "0/0", "0/24", "24", "0/1"])]
    #[case(PatternType::Doms,    vec!["2-2/2", "5-1/2", "?,4", "*,1", "1-1", "5-1", "", " ", ",", "/", "*/", "5/", "-", "1-", "a,b,c", "a-b,c", "1-2-3", ",1", "1,", "1, 2", "1#5", "0/-5", "0/0", "0/31", "32", "0/1", "0"])]
    #[case(PatternType::Months,  vec!["2-2/2", "5-1/2", "*,1", "1-1", "5-1", "W", "?", "L", "", " ", ",", "/", "*/", "5/", "-", "1-", "a,b,c", "a-b,c", "1-2-3", ",1", "1,", "1, 2", "1#1", "0/-5", "0/0", "0/12", "32", "0/1", "0"])]
    #[case(PatternType::Dows,    vec!["?, 3", "*,1", "1-1", "5-1", "W", "L", "", " ", ",", "/", "*/", "5/", "-", "1-", "a,b,c", "a-b,c", "1-2-3", ",1", "1,", "1, 2", "1#5", "0/-5", "0/0", "0/2", "7"])]
    #[case(PatternType::Years,   vec!["1972-1972/2", "2005-2001/2", "*,1", "2001-2001", "2005-2001", "W", "?", "L", "", " ", ",", "/", "*/", "5/", "-", "1-", "a,b,c", "a-b,c", "1-2-3", ",1", "1,", "1, 2", "1#5", "0/-5", "0/0", "0/2", "1969", "2100", "2000/2100"])]
    fn test_pattern_item_parse_invalid(#[case] type_: PatternType, #[case] input: Vec<&str>) {
        for item in input {
            let r = Pattern::parse(type_, item);
            assert!(r.is_err(), "type = {type_:?}, pattern = '{item}'");
        }
    }

    #[rstest]
    #[case(PatternType::Seconds, "0", 0)]
    #[case(PatternType::Seconds, "33", 33)]
    #[case(PatternType::Seconds, "59", 59)]
    #[case(PatternType::Minutes, "0", 0)]
    #[case(PatternType::Minutes, "33", 33)]
    #[case(PatternType::Minutes, "59", 59)]
    #[case(PatternType::Hours, "0", 0)]
    #[case(PatternType::Hours, "13", 13)]
    #[case(PatternType::Hours, "23", 23)]
    #[case(PatternType::Doms, "1", 1)]
    #[case(PatternType::Doms, "15", 15)]
    #[case(PatternType::Doms, "31", 31)]
    #[case(PatternType::Years, MIN_YEAR_STR, MIN_YEAR)]
    #[case(PatternType::Years, MAX_YEAR_STR, MAX_YEAR)]
    #[case(PatternType::Years, "1999", 1999)]
    #[case(PatternType::Years, "2001", 2001)]
    #[case(PatternType::Months, "1", 1)]
    #[case(PatternType::Months, "6", 6)]
    #[case(PatternType::Months, "12", 12)]
    #[case(PatternType::Months, "Jan", 1)]
    #[case(PatternType::Months, "JUN", 6)]
    #[case(PatternType::Months, "dec", 12)]
    #[case(PatternType::Dows, "0", 0)]
    #[case(PatternType::Dows, "3", 3)]
    #[case(PatternType::Dows, "6", 6)]
    #[case(PatternType::Dows, "Sun", 0)]
    #[case(PatternType::Dows, "WED", 3)]
    #[case(PatternType::Dows, "fri", 5)]
    fn test_parse_valid_pattern_type(
        #[case] type_: PatternType,
        #[case] input: &str,
        #[case] expected: PatternValueType,
    ) {
        assert_eq!(type_.parse(input).unwrap(), expected);
    }

    #[rstest]
    #[case(PatternType::Seconds, "60")]
    #[case(PatternType::Seconds, "-1")]
    #[case(PatternType::Seconds, "256")]
    #[case(PatternType::Seconds, "abc")]
    #[case(PatternType::Minutes, "60")]
    #[case(PatternType::Minutes, "-1")]
    #[case(PatternType::Minutes, "256")]
    #[case(PatternType::Minutes, "abc")]
    #[case(PatternType::Hours, "24")]
    #[case(PatternType::Hours, "-1")]
    #[case(PatternType::Hours, "256")]
    #[case(PatternType::Hours, "abc")]
    #[case(PatternType::Doms, "0")]
    #[case(PatternType::Doms, "-12")]
    #[case(PatternType::Doms, "32")]
    #[case(PatternType::Doms, "abc")]
    #[case(PatternType::Years, "1969")]
    #[case(PatternType::Years, "1900")]
    #[case(PatternType::Years, "2100")]
    #[case(PatternType::Years, "-12")]
    #[case(PatternType::Years, "abc")]
    #[case(PatternType::Months, "-2")]
    #[case(PatternType::Months, "0")]
    #[case(PatternType::Months, "13")]
    #[case(PatternType::Months, "256")]
    #[case(PatternType::Months, "abc")]
    #[case(PatternType::Dows, "-3")]
    #[case(PatternType::Dows, "7")]
    #[case(PatternType::Dows, "abc")]
    #[case(PatternType::Months, "")]
    #[case(PatternType::Months, "invalid")]
    #[case(PatternType::Months, "j@n")]
    #[case(PatternType::Months, "ja")]
    #[case(PatternType::Dows, "")]
    #[case(PatternType::Dows, "invalid")]
    #[case(PatternType::Dows, "we")]
    #[case(PatternType::Dows, "M@n")]
    fn test_parse_invalid_pattern_type(#[case] type_: PatternType, #[case] input: &str) {
        assert!(
            matches!(type_.parse(input), Err(CronError::InvalidDigitalValue(e, t)) | Err(CronError::InvalidMnemonicValue(e, t)) if e == input && t == type_.to_string())
        );
    }

    #[rstest]
    // Seconds
    #[case("00:00:00", "0", PatternType::Seconds, Some(0))]
    #[case("00:00:00", "00", PatternType::Seconds, Some(0))]
    #[case("00:00:00", "05", PatternType::Seconds, Some(5))]
    #[case("00:00:00", "59", PatternType::Seconds, Some(59))]
    #[case("00:00:00", "*", PatternType::Seconds, Some(0))]
    #[case("00:00:00", "*/6", PatternType::Seconds, Some(0))]
    #[case("00:00:00", "0/2", PatternType::Seconds, Some(0))]
    #[case("00:00:00", "20/5", PatternType::Seconds, Some(20))]
    #[case("00:00:00", "30/5", PatternType::Seconds, Some(30))]
    #[case("00:00:00", "10-30/5", PatternType::Seconds, Some(10))]
    #[case("00:00:00", "50-59/10", PatternType::Seconds, Some(50))]
    #[case("00:00:00", "0-5", PatternType::Seconds, Some(0))]
    #[case("00:00:00", "25-30", PatternType::Seconds, Some(25))]
    #[case("00:00:00", "12,22,30", PatternType::Seconds, Some(12))]
    #[case("00:00:00", "10,12,20/5,25-30,40-45/2,*/30", PatternType::Seconds, Some(0))]
    #[case("00:00:22", "0", PatternType::Seconds, None)]
    #[case("00:00:22", "59", PatternType::Seconds, Some(59))]
    #[case("00:00:22", "*", PatternType::Seconds, Some(22))]
    #[case("00:00:22", "*/6", PatternType::Seconds, Some(24))]
    #[case("00:00:22", "0/2", PatternType::Seconds, Some(22))]
    #[case("00:00:22", "20/5", PatternType::Seconds, Some(25))]
    #[case("00:00:22", "10-30/5", PatternType::Seconds, Some(25))]
    #[case("00:00:22", "50-59/10", PatternType::Seconds, Some(50))]
    #[case("00:00:22", "0-5", PatternType::Seconds, None)]
    #[case("00:00:22", "25-30", PatternType::Seconds, Some(25))]
    #[case("00:00:22", "12,22,30", PatternType::Seconds, Some(22))]
    #[case("00:00:22", "10,12,20/5,25-30,40-45/2,*/30", PatternType::Seconds, Some(25))]
    // Minutes
    #[case("00:00:00", "0", PatternType::Minutes, Some(0))]
    #[case("00:00:00", "59", PatternType::Minutes, Some(59))]
    #[case("00:00:00", "*", PatternType::Minutes, Some(0))]
    #[case("00:00:00", "*/6", PatternType::Minutes, Some(0))]
    #[case("00:00:00", "0/2", PatternType::Minutes, Some(0))]
    #[case("00:00:00", "20/5", PatternType::Minutes, Some(20))]
    #[case("00:00:00", "10-30/5", PatternType::Minutes, Some(10))]
    #[case("00:00:00", "50-59/10", PatternType::Minutes, Some(50))]
    #[case("00:00:00", "0-5", PatternType::Minutes, Some(0))]
    #[case("00:00:00", "25-30", PatternType::Minutes, Some(25))]
    #[case("00:00:00", "12,22,30", PatternType::Minutes, Some(12))]
    #[case("00:00:00", "10,12,20/5,25-30,40-45/2,*/30", PatternType::Minutes, Some(0))]
    #[case("00:00:22", "10,12,20/5,25-30,40-45/2,*/30", PatternType::Minutes, Some(0))]
    #[case("00:22:00", "0", PatternType::Minutes, None)]
    #[case("00:22:00", "59", PatternType::Minutes, Some(59))]
    #[case("00:22:00", "*", PatternType::Minutes, Some(22))]
    #[case("00:22:00", "*/6", PatternType::Minutes, Some(24))]
    #[case("00:22:00", "0/2", PatternType::Minutes, Some(22))]
    #[case("00:22:00", "20/5", PatternType::Minutes, Some(25))]
    #[case("00:22:00", "10-30/5", PatternType::Minutes, Some(25))]
    #[case("00:22:00", "50-59/10", PatternType::Minutes, Some(50))]
    #[case("00:22:00", "0-5", PatternType::Minutes, None)]
    #[case("00:22:00", "25-30", PatternType::Minutes, Some(25))]
    #[case("00:22:00", "12,22,30", PatternType::Minutes, Some(22))]
    #[case("00:22:00", "10,12,20/5,25-30,40-45/2,*/30", PatternType::Minutes, Some(25))]
    #[case("00:22:22", "10,12,20/5,25-30,40-45/2,*/30", PatternType::Minutes, Some(25))]
    // Hours
    #[case("00:00:00", "0", PatternType::Hours, Some(0))]
    #[case("00:00:00", "23", PatternType::Hours, Some(23))]
    #[case("00:00:00", "*", PatternType::Hours, Some(0))]
    #[case("00:00:00", "*/6", PatternType::Hours, Some(0))]
    #[case("00:00:00", "0/2", PatternType::Hours, Some(0))]
    #[case("00:00:00", "12/5", PatternType::Hours, Some(12))]
    #[case("00:00:00", "10-20/5", PatternType::Hours, Some(10))]
    #[case("00:00:00", "18-23/2", PatternType::Hours, Some(18))]
    #[case("00:00:00", "0-5", PatternType::Hours, Some(0))]
    #[case("00:00:00", "10-15", PatternType::Hours, Some(10))]
    #[case("00:00:00", "1,5,15,22,23", PatternType::Hours, Some(1))]
    #[case("00:00:00", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, Some(0))]
    #[case("00:00:22", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, Some(0))]
    #[case("00:22:00", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, Some(0))]
    #[case("00:22:15", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, Some(0))]
    #[case("05:00:00", "0", PatternType::Hours, None)]
    #[case("05:00:00", "23", PatternType::Hours, Some(23))]
    #[case("05:00:00", "*", PatternType::Hours, Some(5))]
    #[case("05:00:00", "*/6", PatternType::Hours, Some(6))]
    #[case("05:00:00", "0/2", PatternType::Hours, Some(6))]
    #[case("05:00:00", "12/5", PatternType::Hours, Some(12))]
    #[case("05:00:00", "10-20/5", PatternType::Hours, Some(10))]
    #[case("05:00:00", "18-23/2", PatternType::Hours, Some(18))]
    #[case("05:00:00", "0-5", PatternType::Hours, Some(5))]
    #[case("05:00:00", "10-15", PatternType::Hours, Some(10))]
    #[case("05:00:00", "1,5,15,22,23", PatternType::Hours, Some(5))]
    #[case("05:00:00", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, Some(5))]
    #[case("05:00:35", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, Some(5))]
    #[case("05:33:00", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, Some(5))]
    #[case("05:29:43", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, Some(5))]
    #[case("12:00:00", "0", PatternType::Hours, None)]
    #[case("12:00:00", "23", PatternType::Hours, Some(23))]
    #[case("12:00:00", "*", PatternType::Hours, Some(12))]
    #[case("12:00:00", "*/6", PatternType::Hours, Some(12))]
    #[case("12:00:00", "0/2", PatternType::Hours, Some(12))]
    #[case("12:00:00", "12/5", PatternType::Hours, Some(12))]
    #[case("12:00:00", "10-20/5", PatternType::Hours, Some(15))]
    #[case("12:00:00", "18-23/2", PatternType::Hours, Some(18))]
    #[case("12:00:00", "0-5", PatternType::Hours, None)]
    #[case("12:00:00", "10-15", PatternType::Hours, Some(12))]
    #[case("12:00:00", "1,5,15,22,23", PatternType::Hours, Some(15))]
    #[case("12:00:00", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, Some(12))]
    #[case("12:00:35", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, Some(12))]
    #[case("12:13:00", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, Some(12))]
    #[case("12:23:59", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, Some(12))]
    #[case("19:00:00", "0", PatternType::Hours, None)]
    #[case("19:00:00", "23", PatternType::Hours, Some(23))]
    #[case("19:00:00", "*", PatternType::Hours, Some(19))]
    #[case("19:00:00", "*/6", PatternType::Hours, None)]
    #[case("19:00:00", "0/2", PatternType::Hours, Some(20))]
    #[case("19:00:00", "12/5", PatternType::Hours, Some(22))]
    #[case("19:00:00", "10-20/5", PatternType::Hours, Some(20))]
    #[case("19:00:00", "18-23/2", PatternType::Hours, Some(20))]
    #[case("19:00:00", "0-5", PatternType::Hours, None)]
    #[case("19:00:00", "10-15", PatternType::Hours, None)]
    #[case("19:00:00", "1,5,15,22,23", PatternType::Hours, Some(22))]
    #[case("19:00:00", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, Some(20))]
    #[case("19:00:45", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, Some(20))]
    #[case("19:45:00", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, Some(20))]
    #[case("19:45:12", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, Some(20))]
    #[case("23:00:00", "0", PatternType::Hours, None)]
    #[case("23:00:00", "23", PatternType::Hours, Some(23))]
    #[case("23:00:00", "*", PatternType::Hours, Some(23))]
    #[case("23:00:00", "*/6", PatternType::Hours, None)]
    #[case("23:00:00", "0/2", PatternType::Hours, None)]
    #[case("23:00:00", "12/5", PatternType::Hours, None)]
    #[case("23:00:00", "10-20/5", PatternType::Hours, None)]
    #[case("23:00:00", "18-23/2", PatternType::Hours, None)]
    #[case("23:00:00", "0-5", PatternType::Hours, None)]
    #[case("23:00:00", "10-15", PatternType::Hours, None)]
    #[case("23:00:00", "1,5,15,22,23", PatternType::Hours, Some(23))]
    #[case("23:00:19", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, None)]
    #[case("23:29:00", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, None)]
    #[case("23:33:11", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, None)]
    fn test_pattern_next_time_part(
        #[case] time: &str,
        #[case] input: &str,
        #[case] type_: PatternType,
        #[case] expected: Option<PatternValueType>,
    ) {
        let date_times = [
            DateTime::parse_from_rfc3339(format!("2024-01-01T{time}Z").as_str()).unwrap(),
            DateTime::parse_from_rfc3339(format!("2024-02-01T{time}Z").as_str()).unwrap(),
            DateTime::parse_from_rfc3339(format!("2024-02-29T{time}Z").as_str()).unwrap(),
            DateTime::parse_from_rfc3339(format!("2023-02-28T{time}Z").as_str()).unwrap(),
            DateTime::parse_from_rfc3339(format!("1999-05-13T{time}Z").as_str()).unwrap(),
            DateTime::parse_from_rfc3339(format!("1999-12-31T{time}Z").as_str()).unwrap(),
            DateTime::parse_from_rfc3339(format!("1970-06-01T{time}Z").as_str()).unwrap(),
            DateTime::parse_from_rfc3339(format!("1970-06-30T{time}Z").as_str()).unwrap(),
            DateTime::parse_from_rfc3339(format!("2099-01-01T{time}Z").as_str()).unwrap(),
            DateTime::parse_from_rfc3339(format!("2099-12-31T{time}Z").as_str()).unwrap(),
        ];

        let pattern = Pattern::parse(type_, input);

        assert!(
            pattern.is_ok(),
            "type = {type_:?}, pattern = {input}, error = {}",
            pattern.err().unwrap()
        );

        for mut now in date_times {
            assert_eq!(
                pattern.as_ref().unwrap().next(&mut now),
                expected,
                "first: type = {type_:?}, time = {now}, pattern = {input}",
                now = now.to_rfc3339()
            );
        }
    }

    #[rstest]
    // Days of month, 2024
    #[case("2024-01-01", "1", PatternType::Doms, Some(1))]
    #[case("2024-01-01", "01", PatternType::Doms, Some(1))]
    #[case("2024-01-01", "21", PatternType::Doms, Some(21))]
    #[case("2024-01-01", "31", PatternType::Doms, Some(31))]
    #[case("2024-01-05", "5", PatternType::Doms, Some(5))]
    #[case("2024-01-06", "5", PatternType::Doms, None)]
    #[case("2024-01-01", "*", PatternType::Doms, Some(1))]
    #[case("2024-01-01", "*/5", PatternType::Doms, Some(1))]
    #[case("2024-01-12", "*", PatternType::Doms, Some(12))]
    #[case("2024-01-22", "*/5", PatternType::Doms, Some(26))]
    #[case("2024-01-13", "5/5", PatternType::Doms, Some(15))]
    #[case("2024-01-22", "12/3", PatternType::Doms, Some(24))]
    #[case("2024-01-01", "5-10", PatternType::Doms, Some(5))]
    #[case("2024-01-01", "15-22/2", PatternType::Doms, Some(15))]
    #[case("2024-01-16", "15-20", PatternType::Doms, Some(16))]
    #[case("2024-01-17", "15-22/3", PatternType::Doms, Some(18))]
    #[case("2024-01-01", "L", PatternType::Doms, Some(31))]
    #[case("2024-02-01", "L", PatternType::Doms, Some(29))]
    #[case("2024-04-01", "L", PatternType::Doms, Some(30))]
    #[case("2021-02-01", "L", PatternType::Doms, Some(28))]
    #[case("2024-01-01", "15W", PatternType::Doms, Some(15))]
    #[case("2024-01-01", "14W", PatternType::Doms, Some(15))]
    #[case("2024-01-01", "13W", PatternType::Doms, Some(12))]
    #[case("2024-01-01", "7,2,15-19/2,*/5,L,3W", PatternType::Doms, Some(1))]
    #[case("2024-01-21", "7,2,15-19/2,*/5,L,3W", PatternType::Doms, Some(21))]
    #[case("2024-02-01", "7,2,15-19/2,*/5,L,3W", PatternType::Doms, Some(1))]
    #[case("2024-02-15", "7,2,15-19/2,*/5,L,3W", PatternType::Doms, Some(15))]
    #[case("2024-05-01", "7,2,15-19/2,*/5,L,7W", PatternType::Doms, Some(1))]
    #[case("2024-05-11", "7,2,15-19/2,*/5,L,12W", PatternType::Doms, Some(11))]
    #[case("2024-05-31", "7,2,15-19/2,*/5,L,12W", PatternType::Doms, Some(31))]
    #[case("2024-11-01", "7,2,15-19/2,*/5,L,7W", PatternType::Doms, Some(1))]
    #[case("2024-11-11", "7,2,15-19/2,*/5,L,12W", PatternType::Doms, Some(11))]
    #[case("2024-11-30", "7,2,15-19/2,*/5,L,12W", PatternType::Doms, Some(30))]
    // Days of month 1999
    #[case("1999-01-01", "7,2,15-19/2,*/5,L,3W", PatternType::Doms, Some(1))]
    #[case("1999-01-21", "7,2,15-19/2,*/5,L,3W", PatternType::Doms, Some(21))]
    #[case("1999-02-01", "7,2,15-19/2,*/5,L,3W", PatternType::Doms, Some(1))]
    #[case("1999-02-15", "7,2,15-19/2,*/5,L,3W", PatternType::Doms, Some(15))]
    #[case("1999-05-01", "7,2,15-19/2,*/5,L,7W", PatternType::Doms, Some(1))]
    #[case("1999-05-11", "7,2,15-19/2,*/5,L,12W", PatternType::Doms, Some(11))]
    #[case("1999-05-31", "7,2,15-19/2,*/5,L,12W", PatternType::Doms, Some(31))]
    #[case("1999-11-11", "7,2,15-19/2,*/5,L,12W", PatternType::Doms, Some(11))]
    #[case("1999-11-30", "7,2,15-19/2,*/5,L,12W", PatternType::Doms, Some(30))]
    //
    #[case("1999-12-30", "1-31", PatternType::Doms, Some(30))]
    #[case("1999-12-31", "1-31", PatternType::Doms, Some(31))]
    #[case("2004-02-27", "1-31", PatternType::Doms, Some(27))]
    #[case("2004-02-28", "1-31", PatternType::Doms, Some(28))]
    #[case("2004-02-29", "1-31", PatternType::Doms, Some(29))]
    #[case("2001-02-28", "1-31", PatternType::Doms, Some(28))]
    // Months
    #[case("2024-01-01", "1", PatternType::Months, Some(1))]
    #[case("2024-01-01", "01", PatternType::Months, Some(1))]
    #[case("2024-02-01", "1", PatternType::Months, None)]
    #[case("2024-02-01", "12", PatternType::Months, Some(12))]
    #[case("2024-01-01", "*", PatternType::Months, Some(1))]
    #[case("2024-01-01", "*/3", PatternType::Months, Some(1))]
    #[case("2024-05-01", "*/3", PatternType::Months, Some(7))]
    #[case("2024-03-01", "1/3", PatternType::Months, Some(4))]
    #[case("2024-06-01", "5/2", PatternType::Months, Some(7))]
    #[case("2024-05-01", "2-8", PatternType::Months, Some(5))]
    #[case("2024-01-01", "2-5", PatternType::Months, Some(2))]
    #[case("2024-01-01", "4,12,1-2,5/3,10-12/2", PatternType::Months, Some(1))]
    #[case("2024-06-01", "4,12,1-2,5/3,10-12/2", PatternType::Months, Some(8))]
    #[case("2024-12-11", "4,12,1-2,5/3,10-12/2", PatternType::Months, Some(12))]
    #[case("2024-01-01", "mar/3", PatternType::Months, Some(3))]
    #[case("2024-01-01", "jun-aug", PatternType::Months, Some(6))]
    // Years
    #[case("1970-01-01", "1970", PatternType::Years, Some(1970))]
    #[case("1970-01-01", "1971", PatternType::Years, Some(1971))]
    #[case("1980-01-01", "1970", PatternType::Years, None)]
    #[case("1999-01-01", "*", PatternType::Years, Some(1999))]
    #[case("2001-01-01", "*/10", PatternType::Years, Some(2010))]
    #[case("2001-01-01", "1970-2003", PatternType::Years, Some(2001))]
    #[case("1980-01-01", "1970-2000/7", PatternType::Years, Some(1984))]
    #[case("2001-01-01", "1970-2000/10", PatternType::Years, None)]
    #[case("2001-01-01", "1970-2055/10", PatternType::Years, Some(2010))]
    #[case("1991-11-11", "*/10,2090-2099/2,1999", PatternType::Years, Some(1999))]
    #[case("2027-11-11", "*/10,2090-2099/2,1999", PatternType::Years, Some(2030))]
    #[case("2091-02-28", "*/10,2090-2099/2,1999", PatternType::Years, Some(2092))]
    // Days of the week
    #[case("1970-01-01", "0", PatternType::Dows, Some(4))]
    #[case("1970-02-02", "sun", PatternType::Dows, Some(8))]
    #[case("1970-03-03", "mon-fri", PatternType::Dows, Some(3))]
    #[case("1970-01-01", "2-4", PatternType::Dows, Some(1))]
    #[case("1970-01-01", "*", PatternType::Dows, Some(1))]
    #[case("1970-01-01", "6,3", PatternType::Dows, Some(3))]
    #[case("1999-02-01", "4L", PatternType::Dows, Some(25))]
    #[case("2020-02-01", "6L", PatternType::Dows, Some(29))]
    #[case("2020-03-29", "6L", PatternType::Dows, None)]
    #[case("1970-01-01", "3#3", PatternType::Dows, Some(21))]
    #[case("2024-03-01", "1#1", PatternType::Dows, Some(4))]
    #[case("2020-02-01", "6#4", PatternType::Dows, Some(22))]
    #[case("2020-02-23", "6#4", PatternType::Dows, None)]
    #[case("2020-03-29", "6#4", PatternType::Dows, None)]
    #[case("1970-01-01", "1,3-5", PatternType::Dows, Some(1))]
    #[case("1970-01-03", "1,3-5", PatternType::Dows, Some(5))]
    #[case("1970-01-06", "1,3-5", PatternType::Dows, Some(7))]
    #[timeout(Duration::from_secs(1))]
    fn test_pattern_next_date_part(
        #[case] date: &str,
        #[case] input: &str,
        #[case] type_: PatternType,
        #[case] expected: Option<PatternValueType>,
    ) {
        let date_times = [
            DateTime::parse_from_rfc3339(format!("{date}T00:00:00Z").as_str()).unwrap(),
            DateTime::parse_from_rfc3339(format!("{date}T00:15:33Z").as_str()).unwrap(),
            DateTime::parse_from_rfc3339(format!("{date}T01:00:00Z").as_str()).unwrap(),
            DateTime::parse_from_rfc3339(format!("{date}T01:29:12Z").as_str()).unwrap(),
            DateTime::parse_from_rfc3339(format!("{date}T11:59:59Z").as_str()).unwrap(),
            DateTime::parse_from_rfc3339(format!("{date}T12:00:00Z").as_str()).unwrap(),
            DateTime::parse_from_rfc3339(format!("{date}T12:13:14Z").as_str()).unwrap(),
            DateTime::parse_from_rfc3339(format!("{date}T19:00:00Z").as_str()).unwrap(),
            DateTime::parse_from_rfc3339(format!("{date}T23:00:00Z").as_str()).unwrap(),
            DateTime::parse_from_rfc3339(format!("{date}T23:59:59Z").as_str()).unwrap(),
        ];

        let pattern = Pattern::parse(type_, input);

        assert!(
            pattern.is_ok(),
            "type = {type_:?}, pattern = {input}, error = {}",
            pattern.err().unwrap()
        );

        for now in date_times {
            let mut current = now;
            assert_eq!(
                pattern.as_ref().unwrap().next(&mut current),
                expected,
                "type = {type_:?}, time = {now}, pattern = {input}",
                now = now.to_rfc3339()
            );
        }
    }
}
