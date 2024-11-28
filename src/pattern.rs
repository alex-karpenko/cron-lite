use crate::{
    series::SeriesWithStep,
    utils::{self, days_in_month},
    Error, Result,
};
use chrono::{DateTime, Datelike, TimeZone, Timelike};
use std::{collections::BTreeSet, fmt::Display};

const MIN_YEAR: u16 = 1970;
const MIN_YEAR_STR: &str = "1970";
const MAX_YEAR: u16 = 2099;

pub(crate) type PatternValueType = u16;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Pattern {
    type_: PatternType,
    pattern: PatternItem,
}

impl Pattern {
    pub(crate) fn parse(type_: PatternType, input: &str) -> Result<Self> {
        if input.is_empty() {
            return Err(Error::InvalidCronPattern(input.to_owned()));
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
                            return Err(Error::InvalidRepeatingPattern(value.to_owned()));
                        }
                        repeater
                    } else {
                        return Err(Error::InvalidRepeatingPattern(value.to_owned()));
                    };

                    if base.contains('-') {
                        let (start, end) = base.split_once('-').unwrap();
                        let start = type_.parse(start)?;
                        let end = type_.parse(end)?;
                        if start >= end {
                            return Err(Error::InvalidRangeValue(value.to_owned()));
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
                        return Err(Error::InvalidRangeValue(value.to_owned()));
                    }
                    Ok(PatternItem::Range(start, end))
                } else if value.contains('#') && type_ == PatternType::Dows {
                    let mut parts = value.split('#');
                    let dow = parts.next().unwrap();
                    let number = parts.next().unwrap();
                    let number = utils::parse_digital_value(number, 1, 4);
                    if number.is_none() {
                        return Err(Error::InvalidDayOfWeekValue(value.to_owned()));
                    }
                    Ok(PatternItem::Sharp(type_.parse(dow)?, number.unwrap()))
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
            return Err(Error::InvalidCronPattern(input.to_owned()));
        }

        let pattern = if splitted.len() > 1 {
            PatternItem::List(splitted)
        } else {
            splitted.remove(0)
        };

        Ok(Self { type_, pattern })
    }

    pub(crate) fn iter_starting_from<Tz: TimeZone>(
        &self,
        start_date: &DateTime<Tz>,
    ) -> impl Iterator<Item = PatternValueType> {
        let (min, max) = self.type_.min_max();
        let max = if self.type_ == PatternType::Doms {
            days_in_month(
                start_date.year() as PatternValueType,
                start_date.month() as PatternValueType,
            )
        } else {
            max
        };

        let start = match self.type_ {
            PatternType::Seconds => start_date.second() as PatternValueType,
            PatternType::Minutes => start_date.minute() as PatternValueType,
            PatternType::Hours => start_date.hour() as PatternValueType,
            PatternType::Doms => start_date.day() as PatternValueType,
            PatternType::Months => start_date.month() as PatternValueType,
            PatternType::Dows => 0,
            PatternType::Years => start_date.year() as PatternValueType,
        };

        let series: BTreeSet<PatternValueType> = match &self.pattern {
            PatternItem::List(values) => {
                let mut result = BTreeSet::new();
                for pattern in values {
                    let item = Self {
                        type_: self.type_.clone(),
                        pattern: pattern.clone(),
                    };
                    let item_series = item.iter_starting_from(start_date).collect::<Vec<PatternValueType>>();
                    result.extend(item_series);
                }
                result
            }
            PatternItem::All => SeriesWithStep::new(min, max, 1, start).collect(),
            PatternItem::Particular(value) => {
                if *value >= start {
                    BTreeSet::from([*value])
                } else {
                    BTreeSet::new()
                }
            }
            PatternItem::Range(min, max) => SeriesWithStep::new(*min, *max, 1, *min)
                .filter(|v| *v >= start)
                .collect(),
            PatternItem::RepeatingValue(range_start, step) => {
                SeriesWithStep::new(*range_start, max, *step, *range_start)
                    .filter(|v| *v >= start)
                    .collect()
            }
            PatternItem::RepeatingRange(min, max, step) => SeriesWithStep::new(*min, *max, *step, *min)
                .filter(|v| *v >= start)
                .collect(),
            PatternItem::LastDow(dow) => BTreeSet::from([utils::last_dow(
                start_date.year() as PatternValueType,
                start_date.month() as PatternValueType,
                *dow,
            )]),
            PatternItem::LastDom => BTreeSet::from([utils::days_in_month(
                start_date.year() as PatternValueType,
                start_date.month() as PatternValueType,
            )]),
            PatternItem::Weekday(dom) => {
                let weekday = utils::nearest_weekday(
                    start_date.year() as PatternValueType,
                    start_date.month() as PatternValueType,
                    *dom,
                );
                if weekday >= start {
                    BTreeSet::from([weekday])
                } else {
                    BTreeSet::new()
                }
            }
            PatternItem::Sharp(dow, number) => BTreeSet::from([utils::nth_dow(
                start_date.year() as PatternValueType,
                start_date.month() as PatternValueType,
                *dow,
                *number,
            )]),
            PatternItem::Any => unreachable!(),
        };

        series.into_iter()
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.pattern)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum PatternType {
    Seconds = 0,
    Minutes = 1,
    Hours = 2,
    Doms = 3,
    Months = 4,
    Dows = 5,
    Years = 6,
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
                    Err(Error::InvalidDigitalValue(input.to_owned()))
                }
            }
            PatternType::Months | PatternType::Dows => {
                if let Some(value) = utils::parse_digital_value(input, min, max) {
                    Ok(value)
                } else if let Some(value) = utils::parse_string_value(input, &variants) {
                    Ok(value + starter_shift)
                } else {
                    Err(Error::InvalidMnemonicValue(input.to_owned()))
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum PatternItem {
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
    Sharp(PatternValueType, PatternValueType),
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
            PatternItem::Sharp(dow, number) => write!(f, "{}#{}", dow, number),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

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
            (PatternItem::Sharp(3, 2), "3#2"),
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
            let pattern = Pattern {
                type_: type_.clone(),
                pattern: item,
            };
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
            let pattern = Pattern::parse(type_.clone(), item);
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
            ("sun#1", PatternItem::Sharp(0, 1)),
            ("3#2", PatternItem::Sharp(3, 2)),
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
            let r = Pattern::parse(type_.clone(), item);
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
            matches!(type_.parse(input), Err(Error::InvalidDigitalValue(e)) | Err(Error::InvalidMnemonicValue(e)) if e == input)
        );
    }

    #[rstest]
    // Seconds
    #[case("00:00:00", "0", PatternType::Seconds, [0])]
    #[case("00:00:00", "00", PatternType::Seconds, [0])]
    #[case("00:00:00", "05", PatternType::Seconds, [5])]
    #[case("00:00:00", "59", PatternType::Seconds, [59])]
    #[case("00:00:00", "*", PatternType::Seconds, (0..=59).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "*/6", PatternType::Seconds, (0..=59).step_by(6).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "0/2", PatternType::Seconds, (0..=59).step_by(2).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "20/5", PatternType::Seconds, (20..=59).step_by(5).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "30/5", PatternType::Seconds, (30..=59).step_by(5).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "10-30/5", PatternType::Seconds, (10..=30).step_by(5).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "50-59/10", PatternType::Seconds, [50])]
    #[case("00:00:00", "0-5", PatternType::Seconds, (0..=5).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "25-30", PatternType::Seconds, (25..=30).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "12,22,30", PatternType::Seconds, [12,22,30])]
    #[case("00:00:00", "10,12,20/5,25-30,40-45/2,*/30", PatternType::Seconds, [0,10,12,20,25,26,27,28,29,30,35,40,42,44,45,50,55])]
    #[case("00:00:22", "0", PatternType::Seconds, [])]
    #[case("00:00:22", "59", PatternType::Seconds, [59])]
    #[case("00:00:22", "*", PatternType::Seconds, (22..=59).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:22", "*/6", PatternType::Seconds, (24..=59).step_by(6).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:22", "0/2", PatternType::Seconds, (22..=59).step_by(2).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:22", "20/5", PatternType::Seconds, (25..=59).step_by(5).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:22", "10-30/5", PatternType::Seconds, (25..=30).step_by(5).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:22", "50-59/10", PatternType::Seconds, [50])]
    #[case("00:00:22", "0-5", PatternType::Seconds, [])]
    #[case("00:00:22", "25-30", PatternType::Seconds, (25..=30).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:22", "12,22,30", PatternType::Seconds, [22,30])]
    #[case("00:00:22", "10,12,20/5,25-30,40-45/2,*/30", PatternType::Seconds, [25,26,27,28,29,30,35,40,42,44,45,50,55])]
    // Minutes
    #[case("00:00:00", "0", PatternType::Minutes, [0])]
    #[case("00:00:00", "59", PatternType::Minutes, [59])]
    #[case("00:00:00", "*", PatternType::Minutes, (0..=59).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "*/6", PatternType::Minutes, (0..=59).step_by(6).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "0/2", PatternType::Minutes, (0..=59).step_by(2).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "20/5", PatternType::Minutes, (20..=59).step_by(5).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "10-30/5", PatternType::Minutes, (10..=30).step_by(5).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "50-59/10", PatternType::Minutes, [50])]
    #[case("00:00:00", "0-5", PatternType::Minutes, (0..=5).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "25-30", PatternType::Minutes, (25..=30).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "12,22,30", PatternType::Minutes, [12,22,30])]
    #[case("00:00:00", "10,12,20/5,25-30,40-45/2,*/30", PatternType::Minutes, [0,10,12,20,25,26,27,28,29,30,35,40,42,44,45,50,55])]
    #[case("00:00:22", "10,12,20/5,25-30,40-45/2,*/30", PatternType::Minutes, [0,10,12,20,25,26,27,28,29,30,35,40,42,44,45,50,55])]
    #[case("00:22:00", "0", PatternType::Minutes, [])]
    #[case("00:22:00", "59", PatternType::Minutes, [59])]
    #[case("00:22:00", "*", PatternType::Minutes, (22..=59).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:22:00", "*/6", PatternType::Minutes, (24..=59).step_by(6).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:22:00", "0/2", PatternType::Minutes, (22..=59).step_by(2).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:22:00", "20/5", PatternType::Minutes, (25..=59).step_by(5).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:22:00", "10-30/5", PatternType::Minutes, (25..=30).step_by(5).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:22:00", "50-59/10", PatternType::Minutes, [50])]
    #[case("00:22:00", "0-5", PatternType::Minutes, [])]
    #[case("00:22:00", "25-30", PatternType::Minutes, (25..=30).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:22:00", "12,22,30", PatternType::Minutes, [22,30])]
    #[case("00:22:00", "10,12,20/5,25-30,40-45/2,*/30", PatternType::Minutes, [25,26,27,28,29,30,35,40,42,44,45,50,55])]
    #[case("00:22:22", "10,12,20/5,25-30,40-45/2,*/30", PatternType::Minutes, [25,26,27,28,29,30,35,40,42,44,45,50,55])]
    // Hours
    #[case("00:00:00", "0", PatternType::Hours, [0])]
    #[case("00:00:00", "23", PatternType::Hours, [23])]
    #[case("00:00:00", "*", PatternType::Hours, (0..=23).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "*/6", PatternType::Hours, (0..=23).step_by(6).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "0/2", PatternType::Hours, (0..=23).step_by(2).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "12/5", PatternType::Hours, (12..=23).step_by(5).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "10-20/5", PatternType::Hours, (10..=20).step_by(5).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "18-23/2", PatternType::Hours, [18,20,22])]
    #[case("00:00:00", "0-5", PatternType::Hours, (0..=5).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "10-15", PatternType::Hours, (10..=15).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("00:00:00", "1,5,15,22,23", PatternType::Hours, [1,5,15,22,23])]
    #[case("00:00:00", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, [0,3,4,5,7,8,9,10,11,12,13,14,16,20])]
    #[case("00:00:22", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, [0,3,4,5,7,8,9,10,11,12,13,14,16,20])]
    #[case("00:22:00", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, [0,3,4,5,7,8,9,10,11,12,13,14,16,20])]
    #[case("00:22:15", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, [0,3,4,5,7,8,9,10,11,12,13,14,16,20])]
    #[case("05:00:00", "0", PatternType::Hours, [])]
    #[case("05:00:00", "23", PatternType::Hours, [23])]
    #[case("05:00:00", "*", PatternType::Hours, (5..=23).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("05:00:00", "*/6", PatternType::Hours, (6..=23).step_by(6).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("05:00:00", "0/2", PatternType::Hours, (6..=23).step_by(2).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("05:00:00", "12/5", PatternType::Hours, (12..=23).step_by(5).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("05:00:00", "10-20/5", PatternType::Hours, (10..=20).step_by(5).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("05:00:00", "18-23/2", PatternType::Hours, [18,20,22])]
    #[case("05:00:00", "0-5", PatternType::Hours, [5])]
    #[case("05:00:00", "10-15", PatternType::Hours, (10..=15).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("05:00:00", "1,5,15,22,23", PatternType::Hours, [5,15,22,23])]
    #[case("05:00:00", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, [5,7,8,9,10,11,12,13,14,16,20])]
    #[case("05:00:35", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, [5,7,8,9,10,11,12,13,14,16,20])]
    #[case("05:33:00", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, [5,7,8,9,10,11,12,13,14,16,20])]
    #[case("05:29:43", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, [5,7,8,9,10,11,12,13,14,16,20])]
    #[case("12:00:00", "0", PatternType::Hours, [])]
    #[case("12:00:00", "23", PatternType::Hours, [23])]
    #[case("12:00:00", "*", PatternType::Hours, (12..=23).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("12:00:00", "*/6", PatternType::Hours, (12..=23).step_by(6).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("12:00:00", "0/2", PatternType::Hours, (12..=23).step_by(2).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("12:00:00", "12/5", PatternType::Hours, (12..=23).step_by(5).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("12:00:00", "10-20/5", PatternType::Hours, [15,20])]
    #[case("12:00:00", "18-23/2", PatternType::Hours, [18,20,22])]
    #[case("12:00:00", "0-5", PatternType::Hours, [])]
    #[case("12:00:00", "10-15", PatternType::Hours, (12..=15).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("12:00:00", "1,5,15,22,23", PatternType::Hours, [15,22,23])]
    #[case("12:00:00", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, [12,13,14,16,20])]
    #[case("12:00:35", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, [12,13,14,16,20])]
    #[case("12:13:00", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, [12,13,14,16,20])]
    #[case("12:23:59", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, [12,13,14,16,20])]
    #[case("19:00:00", "0", PatternType::Hours, [])]
    #[case("19:00:00", "23", PatternType::Hours, [23])]
    #[case("19:00:00", "*", PatternType::Hours, (19..=23).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("19:00:00", "*/6", PatternType::Hours, [])]
    #[case("19:00:00", "0/2", PatternType::Hours, (20..=23).step_by(2).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("19:00:00", "12/5", PatternType::Hours, [22])]
    #[case("19:00:00", "10-20/5", PatternType::Hours, [20])]
    #[case("19:00:00", "18-23/2", PatternType::Hours, [20,22])]
    #[case("19:00:00", "0-5", PatternType::Hours, [])]
    #[case("19:00:00", "10-15", PatternType::Hours, [])]
    #[case("19:00:00", "1,5,15,22,23", PatternType::Hours, [22,23])]
    #[case("19:00:00", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, [20])]
    #[case("19:00:45", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, [20])]
    #[case("19:45:00", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, [20])]
    #[case("19:45:12", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, [20])]
    #[case("23:00:00", "0", PatternType::Hours, [])]
    #[case("23:00:00", "23", PatternType::Hours, [23])]
    #[case("23:00:00", "*", PatternType::Hours, [23])]
    #[case("23:00:00", "*/6", PatternType::Hours, [])]
    #[case("23:00:00", "0/2", PatternType::Hours, [])]
    #[case("23:00:00", "12/5", PatternType::Hours, [])]
    #[case("23:00:00", "10-20/5", PatternType::Hours, [])]
    #[case("23:00:00", "18-23/2", PatternType::Hours, [])]
    #[case("23:00:00", "0-5", PatternType::Hours, [])]
    #[case("23:00:00", "10-15", PatternType::Hours, [])]
    #[case("23:00:00", "1,5,15,22,23", PatternType::Hours, [23])]
    #[case("23:00:19", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, [])]
    #[case("23:29:00", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, [])]
    #[case("23:33:11", "10,12,20/5,10-14,3-9/2,*/4", PatternType::Hours, [])]
    fn test_iter_starting_from_time_part(
        #[case] time: &str,
        #[case] input: &str,
        #[case] type_: PatternType,
        #[case] expected: impl Into<Vec<PatternValueType>>,
    ) {
        let now = DateTime::parse_from_rfc3339(format!("2024-01-01T{time}Z").as_str()).unwrap();

        let pattern = Pattern::parse(type_.clone(), input);
        assert!(
            pattern.is_ok(),
            "type = {type_:?}, pattern = {input}, error = {}",
            pattern.err().unwrap()
        );

        assert_eq!(
            pattern.unwrap().iter_starting_from(&now).collect::<Vec<_>>(),
            expected.into(),
            "type = {type_:?}, time = {time}, pattern = {input}"
        );
    }

    #[rstest]
    // Days of month, 2024
    #[case("2024-01-01", "1", PatternType::Doms, [1])]
    #[case("2024-01-01", "01", PatternType::Doms, [1])]
    #[case("2024-01-01", "21", PatternType::Doms, [21])]
    #[case("2024-01-01", "31", PatternType::Doms, [31])]
    #[case("2024-01-05", "5", PatternType::Doms, [5])]
    #[case("2024-01-06", "5", PatternType::Doms, [])]
    #[case("2024-01-01", "*", PatternType::Doms, (1..=31).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("2024-01-01", "*/5", PatternType::Doms, (1..=31).into_iter().step_by(5).collect::<Vec<PatternValueType>>())]
    #[case("2024-01-12", "*", PatternType::Doms, (12..=31).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("2024-01-22", "*/5", PatternType::Doms, (26..=31).into_iter().step_by(5).collect::<Vec<PatternValueType>>())]
    #[case("2024-01-13", "5/5", PatternType::Doms, (15..=31).into_iter().step_by(5).collect::<Vec<PatternValueType>>())]
    #[case("2024-01-22", "12/3", PatternType::Doms, [24,27,30])]
    #[case("2024-01-01", "5-10", PatternType::Doms, (5..=10).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("2024-01-01", "15-22/2", PatternType::Doms, (15..=22).into_iter().step_by(2).collect::<Vec<PatternValueType>>())]
    #[case("2024-01-16", "15-20", PatternType::Doms, (16..=20).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("2024-01-17", "15-22/3", PatternType::Doms, [18,21])]
    #[case("2024-01-01", "L", PatternType::Doms, [31])]
    #[case("2024-02-01", "L", PatternType::Doms, [29])]
    #[case("2024-04-01", "L", PatternType::Doms, [30])]
    #[case("2021-02-01", "L", PatternType::Doms, [28])]
    #[case("2024-01-01", "15W", PatternType::Doms, [15])]
    #[case("2024-01-01", "14W", PatternType::Doms, [15])]
    #[case("2024-01-01", "13W", PatternType::Doms, [12])]
    #[case("2024-01-01", "7,2,15-19/2,*/5,L,3W", PatternType::Doms, [1,2,3,6,7,11,15,16,17,19,21,26,31])]
    #[case("2024-01-21", "7,2,15-19/2,*/5,L,3W", PatternType::Doms, [21,26,31])]
    #[case("2024-02-01", "7,2,15-19/2,*/5,L,3W", PatternType::Doms, [1,2,6,7,11,15,16,17,19,21,26,29])]
    #[case("2024-02-15", "7,2,15-19/2,*/5,L,3W", PatternType::Doms, [15,16,17,19,21,26,29])]
    #[case("2024-05-01", "7,2,15-19/2,*/5,L,7W", PatternType::Doms, [1,2,6,7,11,15,16,17,19,21,26,31])]
    #[case("2024-05-11", "7,2,15-19/2,*/5,L,12W", PatternType::Doms, [11,13,15,16,17,19,21,26,31])]
    #[case("2024-05-31", "7,2,15-19/2,*/5,L,12W", PatternType::Doms, [31])]
    #[case("2024-11-01", "7,2,15-19/2,*/5,L,7W", PatternType::Doms, [1,2,6,7,11,15,16,17,19,21,26,30])]
    #[case("2024-11-11", "7,2,15-19/2,*/5,L,12W", PatternType::Doms, [11,12,15,16,17,19,21,26,30])]
    #[case("2024-11-30", "7,2,15-19/2,*/5,L,12W", PatternType::Doms, [30])]
    // Days of month 1999
    #[case("1999-01-01", "7,2,15-19/2,*/5,L,3W", PatternType::Doms, [1,2,4,6,7,11,15,16,17,19,21,26,31])]
    #[case("1999-01-21", "7,2,15-19/2,*/5,L,3W", PatternType::Doms, [21,26,31])]
    #[case("1999-02-01", "7,2,15-19/2,*/5,L,3W", PatternType::Doms, [1,2,3,6,7,11,15,16,17,19,21,26,28])]
    #[case("1999-02-15", "7,2,15-19/2,*/5,L,3W", PatternType::Doms, [15,16,17,19,21,26,28])]
    #[case("1999-05-01", "7,2,15-19/2,*/5,L,7W", PatternType::Doms, [1,2,6,7,11,15,16,17,19,21,26,31])]
    #[case("1999-05-11", "7,2,15-19/2,*/5,L,12W", PatternType::Doms, [11,12,15,16,17,19,21,26,31])]
    #[case("1999-05-31", "7,2,15-19/2,*/5,L,12W", PatternType::Doms, [31])]
    #[case("1999-11-11", "7,2,15-19/2,*/5,L,12W", PatternType::Doms, [11,12,15,16,17,19,21,26,30])]
    #[case("1999-11-30", "7,2,15-19/2,*/5,L,12W", PatternType::Doms, [30])]
    // Months
    #[case("2024-01-01", "1", PatternType::Months, [1])]
    #[case("2024-01-01", "01", PatternType::Months, [1])]
    #[case("2024-02-01", "1", PatternType::Months, [])]
    #[case("2024-02-01", "12", PatternType::Months, [12])]
    #[case("2024-01-01", "*", PatternType::Months, (1..=12).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("2024-01-01", "*/3", PatternType::Months, [1,4,7,10])]
    #[case("2024-05-01", "*/3", PatternType::Months, [7,10])]
    #[case("2024-03-01", "1/3", PatternType::Months, [4,7,10])]
    #[case("2024-06-01", "5/2", PatternType::Months, [7,9,11])]
    #[case("2024-05-01", "2-8", PatternType::Months, [5,6,7,8])]
    #[case("2024-01-01", "2-5", PatternType::Months, [2,3,4,5])]
    #[case("2024-01-01", "4,12,1-2,5/3,10-12/2", PatternType::Months, [1,2,4,5,8,10,11,12])]
    #[case("2024-06-01", "4,12,1-2,5/3,10-12/2", PatternType::Months, [8,10,11,12])]
    #[case("2024-12-11", "4,12,1-2,5/3,10-12/2", PatternType::Months, [12])]
    #[case("2024-01-01", "mar/3", PatternType::Months, [3,6,9,12])]
    #[case("2024-01-01", "jun-aug", PatternType::Months, [6,7,8])]
    // Years
    #[case("1970-01-01", "1970", PatternType::Years, [1970])]
    #[case("1970-01-01", "1971", PatternType::Years, [1971])]
    #[case("1980-01-01", "1970", PatternType::Years, [])]
    #[case("1999-01-01", "*", PatternType::Years, (1999..=2099).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("2001-01-01", "*/10", PatternType::Years, (2010..=2099).step_by(10).into_iter().collect::<Vec<PatternValueType>>())]
    #[case("2001-01-01", "1970-2003", PatternType::Years, [2001,2002,2003])]
    #[case("1980-01-01", "1970-2000/7", PatternType::Years, [1984,1991,1998])]
    #[case("2001-01-01", "1970-2000/10", PatternType::Years, [])]
    #[case("2001-01-01", "1970-2055/10", PatternType::Years, [2010,2020,2030,2040,2050])]
    #[case("1991-11-11", "*/10,2090-2099/2,1999", PatternType::Years, [1999,2000,2010,2020,2030,2040,2050,2060,2070,2080,2090,2092,2094,2096,2098])]
    #[case("2027-11-11", "*/10,2090-2099/2,1999", PatternType::Years, [2030,2040,2050,2060,2070,2080,2090,2092,2094,2096,2098])]
    #[case("2091-02-28", "*/10,2090-2099/2,1999", PatternType::Years, [2092,2094,2096,2098])]
    // Days of week
    #[case("1970-01-01", "0", PatternType::Dows, [0])]
    #[case("1970-01-01", "sun", PatternType::Dows, [0])]
    #[case("1970-01-01", "mon-fri", PatternType::Dows, [1,2,3,4,5])]
    #[case("1970-01-01", "2-4", PatternType::Dows, [2,3,4])]
    #[case("1970-01-01", "*", PatternType::Dows, [0,1,2,3,4,5,6])]
    #[case("1970-01-01", "6,3", PatternType::Dows, [3,6])]
    #[case("1999-02-01", "4L", PatternType::Dows, [25])]
    #[case("1970-01-01", "3#3", PatternType::Dows, [21])]
    #[case("2024-03-01", "1#1", PatternType::Dows, [4])]
    #[case("1970-01-01", "1,3-5", PatternType::Dows, [1,3,4,5])]

    fn test_iter_starting_from_date_part(
        #[case] date: &str,
        #[case] input: &str,
        #[case] type_: PatternType,
        #[case] expected: impl Into<Vec<PatternValueType>>,
    ) {
        let nows = [
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

        let pattern = Pattern::parse(type_.clone(), input);
        let expected: Vec<PatternValueType> = expected.into();

        assert!(
            pattern.is_ok(),
            "type = {type_:?}, pattern = {input}, error = {}",
            pattern.err().unwrap()
        );

        for now in nows {
            assert_eq!(
                &pattern.as_ref().unwrap().iter_starting_from(&now).collect::<Vec<_>>(),
                &expected,
                "type = {type_:?}, time = {now}, pattern = {input}",
                now = now.to_rfc3339()
            );
        }
    }
}
