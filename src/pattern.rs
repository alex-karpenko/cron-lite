use crate::{Error, Result};
use std::{
    fmt::{Debug, Display},
    ops::Index,
};

type PatternPartsSlice = [PatternPartType; 7];

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Pattern {
    pattern: String,
    parts: PatternPartsSlice,
}

impl Pattern {
    pub(crate) fn new(pattern: &str) -> Result<Self> {
        let mut parts = pattern.split_whitespace().collect::<Vec<_>>();
        let len = parts.len();
        if !(5..=7).contains(&len) {
            return Err(Error::InvalidCronPattern(pattern.to_string()));
        } else if len == 5 {
            parts.insert(0, "0");
            parts.insert(6, "*");
        } else if len == 6 {
            parts.insert(6, "*");
        }

        let parsed: PatternPartsSlice = [
            PatternPart::Seconds.parse(parts[0])?,
            PatternPart::Minutes.parse(parts[1])?,
            PatternPart::Hours.parse(parts[2])?,
            PatternPart::Doms.parse(parts[3])?,
            PatternPart::Months.parse(parts[4])?,
            PatternPart::Dows.parse(parts[5])?,
            PatternPart::Years.parse(parts[6])?,
        ];

        Ok(Self {
            pattern: pattern.to_string(),
            parts: parsed,
        })
    }
}

impl<T> Index<PatternPart> for [T] {
    type Output = T;

    fn index(&self, index: PatternPart) -> &Self::Output {
        let index = index as usize;
        &self[index]
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pattern = self
            .parts
            .iter()
            .map(|part| part.to_string())
            .collect::<Vec<_>>()
            .join(" ");
        write!(f, "{}", pattern)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum PatternPart {
    Seconds = 0,
    Minutes = 1,
    Hours = 2,
    Doms = 3,
    Months = 4,
    Dows = 5,
    Years = 6,
}

impl PatternPart {
    fn parse(&self, input: &str) -> Result<PatternPartType> {
        let value_parser: fn(&str) -> Result<PatternPartValue> = match self {
            PatternPart::Seconds => PatternPartValue::second,
            PatternPart::Minutes => PatternPartValue::minute,
            PatternPart::Hours => PatternPartValue::hour,
            PatternPart::Doms => PatternPartValue::dom,
            PatternPart::Months => PatternPartValue::month,
            PatternPart::Dows => PatternPartValue::dow,
            PatternPart::Years => PatternPartValue::year,
        };

        if input.is_empty() {
            return Err(Error::InvalidCronPattern(input.to_owned()));
        }

        let mut error_indicator = Ok(());
        let mut splitted = input
            .split(',')
            .map(|value| {
                if value == "*" {
                    Ok(PatternPartType::All)
                } else if value == "?" && [PatternPart::Dows, PatternPart::Doms].contains(self) {
                    Ok(PatternPartType::Any)
                } else if value.ends_with('L') && self == &PatternPart::Dows {
                    let value = value.trim_end_matches('L');
                    Ok(PatternPartType::LastDow(value_parser(value)?))
                } else if value == "L" && self == &PatternPart::Doms {
                    Ok(PatternPartType::LastDom)
                } else if value.ends_with('W') && self == &PatternPart::Doms {
                    let value = value.trim_end_matches('W');
                    Ok(PatternPartType::Weekday(value_parser(value)?))
                } else if value.contains('/') && self != &PatternPart::Dows {
                    let (base, repeater) = value.split_once('/').unwrap();
                    let base = if base == "*" {
                        match self {
                            PatternPart::Doms | PatternPart::Months => "1",
                            PatternPart::Years => "1970",
                            _ => "0",
                        }
                    } else {
                        base
                    };
                    let repeater = repeater.parse().unwrap();
                    if repeater < 2 {
                        return Err(Error::InvalidRepeatingPattern(value.to_owned()));
                    }
                    if base.contains('-') {
                        let (start, end) = base.split_once('-').unwrap();
                        let start = value_parser(start)?;
                        let end = value_parser(end)?;
                        if start >= end {
                            return Err(Error::InvalidRangeValue(value.to_owned()));
                        }
                        Ok(PatternPartType::RepeatingRange(start, end, repeater))
                    } else {
                        Ok(PatternPartType::RepeatingValue(value_parser(base)?, repeater))
                    }
                } else if value.contains('-') {
                    let (start, end) = value.split_once('-').unwrap();
                    let start = value_parser(start)?;
                    let end = value_parser(end)?;
                    if start >= end {
                        return Err(Error::InvalidRangeValue(value.to_owned()));
                    }
                    Ok(PatternPartType::Range(start, end))
                } else if value.contains('#') && self == &PatternPart::Dows {
                    let mut parts = value.split('#');
                    let dow = parts.next().unwrap();
                    let number = parts.next().unwrap();
                    let number = parse_digital_value(number, 1, 4);
                    if number.is_none() {
                        return Err(Error::InvalidDayOfWeekValue(value.to_owned()));
                    }
                    Ok(PatternPartType::Hash(
                        PatternPartValue::dow(dow)?,
                        number.unwrap() as u8,
                    ))
                } else {
                    Ok(PatternPartType::Particular(value_parser(value)?))
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
            || (splitted.len() > 1
                && (splitted.contains(&PatternPartType::All) || splitted.contains(&PatternPartType::Any)))
        {
            return Err(Error::InvalidCronPattern(input.to_owned()));
        }

        if splitted.len() > 1 {
            Ok(PatternPartType::List(splitted))
        } else {
            Ok(splitted.remove(0))
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum PatternPartType {
    All,
    Any,
    Particular(PatternPartValue),
    List(Vec<PatternPartType>),
    Range(PatternPartValue, PatternPartValue),
    RepeatingValue(PatternPartValue, u8),
    RepeatingRange(PatternPartValue, PatternPartValue, u8),
    LastDow(PatternPartValue),
    LastDom,
    Weekday(PatternPartValue),
    Hash(PatternPartValue, u8),
}

impl Display for PatternPartType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PatternPartType::All => write!(f, "*"),
            PatternPartType::Any => write!(f, "?"),
            PatternPartType::Particular(value) => write!(f, "{value}"),
            PatternPartType::List(values) => {
                let values = values.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(",");
                write!(f, "{}", values)
            }
            PatternPartType::Range(start, end) => write!(f, "{start}-{end}"),
            PatternPartType::RepeatingValue(value, repeater) => write!(f, "{value}/{repeater}"),
            PatternPartType::RepeatingRange(start, end, repeater) => {
                write!(f, "{start}-{end}/{repeater}")
            }
            PatternPartType::LastDow(value) => write!(f, "{value}L"),
            PatternPartType::LastDom => write!(f, "L"),
            PatternPartType::Weekday(value) => write!(f, "{value}W"),
            PatternPartType::Hash(value, number) => write!(f, "{value}#{number}"),
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum PatternPartValue {
    Year(u16),
    Dow(u8),
    Month(u8),
    Dom(u8),
    Hour(u8),
    Minute(u8),
    Second(u8),
}

impl Display for PatternPartValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PatternPartValue::Year(year) => write!(f, "{year}"),
            PatternPartValue::Dow(dow) => write!(
                f,
                "{}",
                capitalize(Self::DAYS_OF_WEEK[*dow as usize].to_lowercase().as_str())
            ),
            PatternPartValue::Month(month) => {
                write!(
                    f,
                    "{}",
                    capitalize(Self::MONTHS[*month as usize - 1].to_lowercase().as_str())
                )
            }
            PatternPartValue::Dom(dom) => write!(f, "{dom}"),
            PatternPartValue::Hour(hour) => write!(f, "{hour}"),
            PatternPartValue::Minute(minute) => write!(f, "{minute}"),
            PatternPartValue::Second(second) => write!(f, "{second}"),
        }
    }
}
impl PatternPartValue {
    const DAYS_OF_WEEK: [&str; 7] = ["SUN", "MON", "TUE", "WED", "THU", "FRI", "SAT"];
    const MONTHS: [&str; 12] = [
        "JAN", "FEB", "MAR", "APR", "MAY", "JUN", "JUL", "AUG", "SEP", "OCT", "NOV", "DEC",
    ];

    fn year(input: &str) -> Result<Self> {
        if let Some(year) = parse_digital_value(input, 1970, 2099) {
            Ok(Self::Year(year))
        } else {
            Err(Error::InvalidYearValue(input.to_owned()))
        }
    }

    fn hour(input: &str) -> Result<Self> {
        if let Some(hour) = parse_digital_value(input, 0, 23) {
            Ok(Self::Hour(hour as u8))
        } else {
            Err(Error::InvalidHourValue(input.to_owned()))
        }
    }

    fn minute(input: &str) -> Result<Self> {
        if let Some(minute) = parse_digital_value(input, 0, 59) {
            Ok(Self::Minute(minute as u8))
        } else {
            Err(Error::InvalidMinuteValue(input.to_owned()))
        }
    }

    fn second(input: &str) -> Result<Self> {
        if let Some(second) = parse_digital_value(input, 0, 59) {
            Ok(Self::Second(second as u8))
        } else {
            Err(Error::InvalidSecondValue(input.to_owned()))
        }
    }

    fn month(input: &str) -> Result<Self> {
        if let Some(month) = parse_digital_value(input, 1, 12) {
            Ok(Self::Month(month as u8))
        } else if let Some(month) = parse_string_value(input, &Self::MONTHS) {
            Ok(Self::Month((month + 1) as u8))
        } else {
            Err(Error::InvalidMonthValue(input.to_owned()))
        }
    }

    fn dom(input: &str) -> Result<Self> {
        if let Some(dom) = parse_digital_value(input, 1, 31) {
            Ok(Self::Dom(dom as u8))
        } else {
            Err(Error::InvalidDayOfMonthValue(input.to_owned()))
        }
    }

    fn dow(input: &str) -> Result<Self> {
        if let Some(dow) = parse_digital_value(input, 0, 6) {
            Ok(Self::Dow(dow as u8))
        } else if let Some(dow) = parse_string_value(input, &Self::DAYS_OF_WEEK) {
            Ok(Self::Dow(dow as u8))
        } else {
            Err(Error::InvalidDayOfWeekValue(input.to_owned()))
        }
    }
}

fn parse_digital_value(input: &str, min: u16, max: u16) -> Option<u16> {
    let value = input.parse::<u16>();
    if let Ok(value) = value {
        if value < min || value > max {
            None
        } else {
            Some(value)
        }
    } else {
        None
    }
}

fn parse_string_value(input: &str, array: &[&str]) -> Option<usize> {
    if input.is_empty() {
        None
    } else {
        array.iter().position(|&x| x.to_uppercase() == input.to_uppercase())
    }
}

fn capitalize(s: &str) -> String {
    let mut c = s.chars();
    match c.next() {
        None => String::new(),
        Some(f) => f.to_uppercase().collect::<String>() + c.as_str(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pattern_display() {
        assert_eq!(Pattern::new("*/5 * * * *").unwrap().to_string(), "0 0/5 * * * * *");
        assert_eq!(Pattern::new("0 0/5 * * * * *").unwrap().to_string(), "0 0/5 * * * * *");
        assert_eq!(Pattern::new("* * * * * * *").unwrap().to_string(), "* * * * * * *");
        assert_eq!(
            Pattern::new("0 1 2 3 4 5 2024").unwrap().to_string(),
            "0 1 2 3 Apr Fri 2024"
        );
        assert_eq!(
            Pattern::new("0 1/2 */3 3 4 5 1970,1980-1990,2000-2050/3")
                .unwrap()
                .to_string(),
            "0 1/2 0/3 3 Apr Fri 1970,1980-1990,2000-2050/3"
        );
    }

    #[test]
    fn test_pattern_part_value_display() {
        assert_eq!(PatternPartValue::Year(2023).to_string(), "2023");
        assert_eq!(PatternPartValue::Dow(0).to_string(), "Sun");
        assert_eq!(PatternPartValue::Dow(6).to_string(), "Sat");
        assert_eq!(PatternPartValue::Month(1).to_string(), "Jan");
        assert_eq!(PatternPartValue::Month(12).to_string(), "Dec");
        assert_eq!(PatternPartValue::Dom(15).to_string(), "15");
        assert_eq!(PatternPartValue::Hour(9).to_string(), "9");
        assert_eq!(PatternPartValue::Minute(30).to_string(), "30");
        assert_eq!(PatternPartValue::Second(45).to_string(), "45");
    }

    #[test]
    fn test_pattern_part_type_display() {
        let test_cases = vec![
            (PatternPartType::All, "*"),
            (PatternPartType::Any, "?"),
            (PatternPartType::Particular(PatternPartValue::Hour(5)), "5"),
            (
                PatternPartType::List(vec![
                    PatternPartType::Particular(PatternPartValue::Month(3)),
                    PatternPartType::Particular(PatternPartValue::Month(1)),
                ]),
                "Mar,Jan",
            ),
            (
                PatternPartType::Range(PatternPartValue::Hour(2), PatternPartValue::Hour(5)),
                "2-5",
            ),
            (
                PatternPartType::RepeatingValue(PatternPartValue::Minute(15), 30),
                "15/30",
            ),
            (
                PatternPartType::RepeatingRange(PatternPartValue::Second(0), PatternPartValue::Second(30), 5),
                "0-30/5",
            ),
            (PatternPartType::LastDow(PatternPartValue::Dow(1)), "MonL"),
            (PatternPartType::LastDom, "L"),
            (PatternPartType::Weekday(PatternPartValue::Dom(15)), "15W"),
            (PatternPartType::Hash(PatternPartValue::Dow(3), 2), "Wed#2"),
            (
                PatternPartType::List(vec![
                    PatternPartType::Particular(PatternPartValue::Hour(3)),
                    PatternPartType::Particular(PatternPartValue::Hour(1)),
                    PatternPartType::Range(PatternPartValue::Hour(2), PatternPartValue::Hour(5)),
                    PatternPartType::RepeatingValue(PatternPartValue::Hour(12), 3),
                    PatternPartType::RepeatingRange(PatternPartValue::Hour(10), PatternPartValue::Hour(22), 4),
                ]),
                "3,1,2-5,12/3,10-22/4",
            ),
        ];

        for (pattern_type, expected) in test_cases {
            assert_eq!(pattern_type.to_string(), expected);
        }
    }

    #[test]
    fn test_capitalize_empty_string() {
        assert_eq!(capitalize(""), "");
    }

    #[test]
    fn test_capitalize_single_char() {
        assert_eq!(capitalize("a"), "A");
        assert_eq!(capitalize("z"), "Z");
    }

    #[test]
    fn test_capitalize_word() {
        assert_eq!(capitalize("hello"), "Hello");
        assert_eq!(capitalize("world"), "World");
    }

    #[test]
    fn test_capitalize_already_capitalized() {
        assert_eq!(capitalize("Hello"), "Hello");
        assert_eq!(capitalize("WORLD"), "WORLD");
    }

    #[test]
    fn test_capitalize_with_numbers() {
        assert_eq!(capitalize("123abc"), "123abc");
        assert_eq!(capitalize("a123bc"), "A123bc");
    }

    #[test]
    fn test_capitalize_with_special_chars() {
        assert_eq!(capitalize("@hello"), "@hello");
        assert_eq!(capitalize("hello!"), "Hello!");
    }

    #[test]
    fn test_parse_digital_value_valid_value_within_range() {
        assert_eq!(parse_digital_value("5", 0, 10), Some(5));
        assert_eq!(parse_digital_value("0", 0, 10), Some(0));
        assert_eq!(parse_digital_value("10", 0, 10), Some(10));
    }

    #[test]
    fn test_parse_digital_value_value_below_minimum() {
        assert_eq!(parse_digital_value("5", 10, 20), None);
    }

    #[test]
    fn test_parse_digital_value_value_above_maximum() {
        assert_eq!(parse_digital_value("25", 0, 20), None);
    }

    #[test]
    fn test_parse_digital_value_invalid_input() {
        assert_eq!(parse_digital_value("abc", 0, 10), None);
        assert_eq!(parse_digital_value("", 0, 10), None);
        assert_eq!(parse_digital_value("-1", 0, 10), None);
        assert_eq!(parse_digital_value("1.5", 0, 10), None);
    }

    #[test]
    fn test_parse_digital_value_edge_cases() {
        // Test with min equal to max
        assert_eq!(parse_digital_value("5", 5, 5), Some(5));
        assert_eq!(parse_digital_value("4", 5, 5), None);
        assert_eq!(parse_digital_value("6", 5, 5), None);

        // Test with large valid numbers
        assert_eq!(parse_digital_value("65535", 0, 65535), Some(65535));
    }

    #[test]
    fn test_valid_year() {
        assert_eq!(PatternPartValue::year("1970").unwrap(), PatternPartValue::Year(1970));
        assert_eq!(PatternPartValue::year("2099").unwrap(), PatternPartValue::Year(2099));
        assert_eq!(PatternPartValue::year("2000").unwrap(), PatternPartValue::Year(2000));
    }

    #[test]
    fn test_invalid_year() {
        assert!(matches!(PatternPartValue::year("1969"), Err(Error::InvalidYearValue(e)) if e == "1969"));
        assert!(matches!(PatternPartValue::year("2100"), Err(Error::InvalidYearValue(e)) if e == "2100"));
        assert!(matches!(PatternPartValue::year("abc"), Err(Error::InvalidYearValue(e)) if e == "abc"));
        assert!(matches!(PatternPartValue::year("-1"), Err(Error::InvalidYearValue(e)) if e == "-1"));
    }

    #[test]
    fn test_valid_dom() {
        assert_eq!(PatternPartValue::dom("1").unwrap(), PatternPartValue::Dom(1));
        assert_eq!(PatternPartValue::dom("12").unwrap(), PatternPartValue::Dom(12));
        assert_eq!(PatternPartValue::dom("31").unwrap(), PatternPartValue::Dom(31));
    }

    #[test]
    fn test_invalid_dom() {
        assert!(matches!(PatternPartValue::dom("0"), Err(Error::InvalidDayOfMonthValue(e)) if e == "0"));
        assert!(matches!(PatternPartValue::dom("-1"), Err(Error::InvalidDayOfMonthValue(e)) if e == "-1"));
        assert!(matches!(PatternPartValue::dom("32"), Err(Error::InvalidDayOfMonthValue(e)) if e == "32"));
        assert!(matches!(PatternPartValue::dom("256"), Err(Error::InvalidDayOfMonthValue(e)) if e == "256"));
        assert!(matches!(PatternPartValue::dom("abc"), Err(Error::InvalidDayOfMonthValue(e)) if e == "abc"));
    }

    #[test]
    fn test_valid_hour() {
        assert_eq!(PatternPartValue::hour("0").unwrap(), PatternPartValue::Hour(0));
        assert_eq!(PatternPartValue::hour("12").unwrap(), PatternPartValue::Hour(12));
        assert_eq!(PatternPartValue::hour("23").unwrap(), PatternPartValue::Hour(23));
    }

    #[test]
    fn test_invalid_hour() {
        assert!(matches!(PatternPartValue::hour("24"), Err(Error::InvalidHourValue(e)) if e == "24"));
        assert!(matches!(PatternPartValue::hour("-1"), Err(Error::InvalidHourValue(e)) if e == "-1"));
        assert!(matches!(PatternPartValue::hour("256"), Err(Error::InvalidHourValue(e)) if e == "256"));
        assert!(matches!(PatternPartValue::hour("abc"), Err(Error::InvalidHourValue(e)) if e == "abc"));
    }

    #[test]
    fn test_valid_minute() {
        assert_eq!(PatternPartValue::minute("0").unwrap(), PatternPartValue::Minute(0));
        assert_eq!(PatternPartValue::minute("33").unwrap(), PatternPartValue::Minute(33));
        assert_eq!(PatternPartValue::minute("59").unwrap(), PatternPartValue::Minute(59));
    }

    #[test]
    fn test_invalid_minute() {
        assert!(matches!(PatternPartValue::minute("60"), Err(Error::InvalidMinuteValue(e)) if e == "60"));
        assert!(matches!(PatternPartValue::minute("-1"), Err(Error::InvalidMinuteValue(e)) if e == "-1"));
        assert!(matches!(PatternPartValue::minute("256"), Err(Error::InvalidMinuteValue(e)) if e == "256"));
        assert!(matches!(PatternPartValue::minute("abc"), Err(Error::InvalidMinuteValue(e)) if e == "abc"));
    }

    #[test]
    fn test_valid_second() {
        assert_eq!(PatternPartValue::second("0").unwrap(), PatternPartValue::Second(0));
        assert_eq!(PatternPartValue::second("33").unwrap(), PatternPartValue::Second(33));
        assert_eq!(PatternPartValue::second("59").unwrap(), PatternPartValue::Second(59));
    }

    #[test]
    fn test_invalid_second() {
        assert!(matches!(PatternPartValue::second("60"), Err(Error::InvalidSecondValue(e)) if e == "60"));
        assert!(matches!(PatternPartValue::second("-1"), Err(Error::InvalidSecondValue(e)) if e == "-1"));
        assert!(matches!(PatternPartValue::second("256"), Err(Error::InvalidSecondValue(e)) if e == "256"));
        assert!(matches!(PatternPartValue::second("abc"), Err(Error::InvalidSecondValue(e)) if e == "abc"));
    }

    #[test]
    fn test_parse_string_value() {
        // Test data
        let test_array = &[
            "sunday",
            "monday",
            "tuesday",
            "wednesday",
            "thursday",
            "friday",
            "saturday",
        ];

        // Test valid cases with different casing
        assert_eq!(parse_string_value("monday", test_array), Some(1));
        assert_eq!(parse_string_value("FRIDAY", test_array), Some(5));
        assert_eq!(parse_string_value("SuNdAy", test_array), Some(0));

        // Test first and last elements
        assert_eq!(parse_string_value("sunday", test_array), Some(0));
        assert_eq!(parse_string_value("saturday", test_array), Some(6));

        // Test invalid cases
        assert_eq!(parse_string_value("", test_array), None);
        assert_eq!(parse_string_value("invalid_day", test_array), None);

        // Test with different array
        let months = &["jan", "feb", "mar"];
        assert_eq!(parse_string_value("feb", months), Some(1));
        assert_eq!(parse_string_value("FEB", months), Some(1));
        assert_eq!(parse_string_value("dec", months), None);
    }

    #[test]
    fn test_parse_string_value_empty_array() {
        let empty_array: &[&str] = &[];
        assert_eq!(parse_string_value("test", empty_array), None);
    }

    #[test]
    fn test_parse_string_value_whitespace() {
        let array = &["test", "value"];
        assert_eq!(parse_string_value(" test ", array), None);
        assert_eq!(parse_string_value("\ttest", array), None);
    }

    #[test]
    fn test_valid_month_numeric() {
        assert_eq!(PatternPartValue::month("1").unwrap(), PatternPartValue::Month(1));
        assert_eq!(PatternPartValue::month("6").unwrap(), PatternPartValue::Month(6));
        assert_eq!(PatternPartValue::month("12").unwrap(), PatternPartValue::Month(12));
    }
    #[test]
    fn test_valid_month_string() {
        assert_eq!(PatternPartValue::month("jan").unwrap(), PatternPartValue::Month(1));
        assert_eq!(PatternPartValue::month("JUN").unwrap(), PatternPartValue::Month(6));
        assert_eq!(PatternPartValue::month("DeC").unwrap(), PatternPartValue::Month(12));
    }

    #[test]
    fn test_invalid_month_numeric() {
        assert!(matches!(PatternPartValue::month("0"), Err(Error::InvalidMonthValue(e)) if e == "0"));
        assert!(matches!(PatternPartValue::month("13"), Err(Error::InvalidMonthValue(e)) if e == "13"));
        assert!(matches!(PatternPartValue::month("-1"), Err(Error::InvalidMonthValue(e)) if e == "-1"));
        assert!(matches!(PatternPartValue::month("256"), Err(Error::InvalidMonthValue(e)) if e == "256"));
    }

    #[test]
    fn test_invalid_month_string() {
        assert!(matches!(PatternPartValue::month(""), Err(Error::InvalidMonthValue(e)) if e.is_empty()));
        assert!(matches!(PatternPartValue::month("invalid"), Err(Error::InvalidMonthValue(e)) if e == "invalid"));
        assert!(matches!(PatternPartValue::month("j@n"), Err(Error::InvalidMonthValue(e)) if e == "j@n"));
        assert!(matches!(PatternPartValue::month("ja"), Err(Error::InvalidMonthValue(e)) if e == "ja"));
    }

    #[test]
    fn test_valid_dow_numeric() {
        assert_eq!(PatternPartValue::dow("0").unwrap(), PatternPartValue::Dow(0));
        assert_eq!(PatternPartValue::dow("6").unwrap(), PatternPartValue::Dow(6));
        assert_eq!(PatternPartValue::dow("3").unwrap(), PatternPartValue::Dow(3));
    }

    #[test]
    fn test_valid_dow_string() {
        assert_eq!(PatternPartValue::dow("sun").unwrap(), PatternPartValue::Dow(0));
        assert_eq!(PatternPartValue::dow("MON").unwrap(), PatternPartValue::Dow(1));
        assert_eq!(PatternPartValue::dow("Sat").unwrap(), PatternPartValue::Dow(6));
    }

    #[test]
    fn test_invalid_dow_numeric() {
        assert!(matches!(PatternPartValue::dow("7"), Err(Error::InvalidDayOfWeekValue(e)) if e == "7"));
        assert!(matches!(PatternPartValue::dow("13"), Err(Error::InvalidDayOfWeekValue(e)) if e == "13"));
        assert!(matches!(PatternPartValue::dow("-1"), Err(Error::InvalidDayOfWeekValue(e)) if e == "-1"));
        assert!(matches!(PatternPartValue::dow("256"), Err(Error::InvalidDayOfWeekValue(e)) if e == "256"));
    }

    #[test]
    fn test_invalid_dow_string() {
        assert!(matches!(PatternPartValue::dow(""), Err(Error::InvalidDayOfWeekValue(e)) if e.is_empty()));
        assert!(matches!(PatternPartValue::dow("invalid"), Err(Error::InvalidDayOfWeekValue(e)) if e == "invalid"));
        assert!(matches!(PatternPartValue::dow("we"), Err(Error::InvalidDayOfWeekValue(e)) if e == "we"));
        assert!(matches!(
            PatternPartValue::dow("M@n"),
            Err(Error::InvalidDayOfWeekValue(e)) if e == "M@n"
        ));
    }

    #[test]
    fn test_pattern_part_split_valid_single_values() {
        // Test All patterns
        assert_eq!(PatternPart::Seconds.parse("*").unwrap(), PatternPartType::All);
        assert_eq!(PatternPart::Minutes.parse("*").unwrap(), PatternPartType::All);
        assert_eq!(PatternPart::Hours.parse("*").unwrap(), PatternPartType::All);
        assert_eq!(PatternPart::Doms.parse("*").unwrap(), PatternPartType::All);
        assert_eq!(PatternPart::Months.parse("*").unwrap(), PatternPartType::All);
        assert_eq!(PatternPart::Dows.parse("*").unwrap(), PatternPartType::All);
        assert_eq!(PatternPart::Years.parse("*").unwrap(), PatternPartType::All);

        // Test Any pattern
        assert_eq!(PatternPart::Dows.parse("?").unwrap(), PatternPartType::Any);
        assert_eq!(PatternPart::Doms.parse("?").unwrap(), PatternPartType::Any);

        // Test RepeatingValue pattern, with *
        assert_eq!(
            PatternPart::Seconds.parse("*/5").unwrap(),
            PatternPartType::RepeatingValue(PatternPartValue::Second(0), 5)
        );
        assert_eq!(
            PatternPart::Minutes.parse("*/10").unwrap(),
            PatternPartType::RepeatingValue(PatternPartValue::Minute(0), 10)
        );
        assert_eq!(
            PatternPart::Hours.parse("*/2").unwrap(),
            PatternPartType::RepeatingValue(PatternPartValue::Hour(0), 2)
        );
        assert_eq!(
            PatternPart::Doms.parse("*/3").unwrap(),
            PatternPartType::RepeatingValue(PatternPartValue::Dom(1), 3)
        );
        assert_eq!(
            PatternPart::Months.parse("*/4").unwrap(),
            PatternPartType::RepeatingValue(PatternPartValue::Month(1), 4)
        );
        assert_eq!(
            PatternPart::Years.parse("*/10").unwrap(),
            PatternPartType::RepeatingValue(PatternPartValue::Year(1970), 10)
        );

        // Test RepeatingValue pattern, with number
        assert_eq!(
            PatternPart::Seconds.parse("0/5").unwrap(),
            PatternPartType::RepeatingValue(PatternPartValue::Second(0), 5)
        );
        assert_eq!(
            PatternPart::Minutes.parse("10/10").unwrap(),
            PatternPartType::RepeatingValue(PatternPartValue::Minute(10), 10)
        );
        assert_eq!(
            PatternPart::Hours.parse("5/2").unwrap(),
            PatternPartType::RepeatingValue(PatternPartValue::Hour(5), 2)
        );
        assert_eq!(
            PatternPart::Doms.parse("2/3").unwrap(),
            PatternPartType::RepeatingValue(PatternPartValue::Dom(2), 3)
        );
        assert_eq!(
            PatternPart::Months.parse("3/2").unwrap(),
            PatternPartType::RepeatingValue(PatternPartValue::Month(3), 2)
        );
        assert_eq!(
            PatternPart::Years.parse("2000/5").unwrap(),
            PatternPartType::RepeatingValue(PatternPartValue::Year(2000), 5)
        );

        // Test RepeatingRange pattern
        assert_eq!(
            PatternPart::Seconds.parse("10-30/5").unwrap(),
            PatternPartType::RepeatingRange(PatternPartValue::Second(10), PatternPartValue::Second(30), 5)
        );
        assert_eq!(
            PatternPart::Minutes.parse("5-40/10").unwrap(),
            PatternPartType::RepeatingRange(PatternPartValue::Minute(5), PatternPartValue::Minute(40), 10)
        );
        assert_eq!(
            PatternPart::Hours.parse("0-12/2").unwrap(),
            PatternPartType::RepeatingRange(PatternPartValue::Hour(0), PatternPartValue::Hour(12), 2)
        );
        assert_eq!(
            PatternPart::Doms.parse("1-15/5").unwrap(),
            PatternPartType::RepeatingRange(PatternPartValue::Dom(1), PatternPartValue::Dom(15), 5)
        );
        assert_eq!(
            PatternPart::Months.parse("4-10/2").unwrap(),
            PatternPartType::RepeatingRange(PatternPartValue::Month(4), PatternPartValue::Month(10), 2)
        );
        assert_eq!(
            PatternPart::Months.parse("JAN-AUG/3").unwrap(),
            PatternPartType::RepeatingRange(PatternPartValue::Month(1), PatternPartValue::Month(8), 3)
        );
        assert_eq!(
            PatternPart::Years.parse("1980-2050/12").unwrap(),
            PatternPartType::RepeatingRange(PatternPartValue::Year(1980), PatternPartValue::Year(2050), 12)
        );

        // Test Range pattern
        assert_eq!(
            PatternPart::Seconds.parse("10-20").unwrap(),
            PatternPartType::Range(PatternPartValue::Second(10), PatternPartValue::Second(20))
        );
        assert_eq!(
            PatternPart::Minutes.parse("0-30").unwrap(),
            PatternPartType::Range(PatternPartValue::Minute(0), PatternPartValue::Minute(30))
        );
        assert_eq!(
            PatternPart::Hours.parse("9-20").unwrap(),
            PatternPartType::Range(PatternPartValue::Hour(9), PatternPartValue::Hour(20))
        );
        assert_eq!(
            PatternPart::Doms.parse("1-5").unwrap(),
            PatternPartType::Range(PatternPartValue::Dom(1), PatternPartValue::Dom(5))
        );
        assert_eq!(
            PatternPart::Months.parse("1-6").unwrap(),
            PatternPartType::Range(PatternPartValue::Month(1), PatternPartValue::Month(6))
        );
        assert_eq!(
            PatternPart::Dows.parse("0-2").unwrap(),
            PatternPartType::Range(PatternPartValue::Dow(0), PatternPartValue::Dow(2))
        );
        assert_eq!(
            PatternPart::Years.parse("2000-2006").unwrap(),
            PatternPartType::Range(PatternPartValue::Year(2000), PatternPartValue::Year(2006))
        );

        // Test Range pattern with mnemonic names
        assert_eq!(
            PatternPart::Months.parse("FEB-JUN").unwrap(),
            PatternPartType::Range(PatternPartValue::Month(2), PatternPartValue::Month(6))
        );
        assert_eq!(
            PatternPart::Dows.parse("MON-WED").unwrap(),
            PatternPartType::Range(PatternPartValue::Dow(1), PatternPartValue::Dow(3))
        );

        // Test Hash pattern for day of week
        assert_eq!(
            PatternPart::Dows.parse("MON#2").unwrap(),
            PatternPartType::Hash(PatternPartValue::Dow(1), 2)
        );
        assert_eq!(
            PatternPart::Dows.parse("6#3").unwrap(),
            PatternPartType::Hash(PatternPartValue::Dow(6), 3)
        );

        // Test Particular value
        assert_eq!(
            PatternPart::Seconds.parse("12").unwrap(),
            PatternPartType::Particular(PatternPartValue::Second(12))
        );
        assert_eq!(
            PatternPart::Minutes.parse("30").unwrap(),
            PatternPartType::Particular(PatternPartValue::Minute(30))
        );
        assert_eq!(
            PatternPart::Hours.parse("12").unwrap(),
            PatternPartType::Particular(PatternPartValue::Hour(12))
        );
        assert_eq!(
            PatternPart::Doms.parse("15").unwrap(),
            PatternPartType::Particular(PatternPartValue::Dom(15))
        );
        assert_eq!(
            PatternPart::Months.parse("6").unwrap(),
            PatternPartType::Particular(PatternPartValue::Month(6))
        );
        assert_eq!(
            PatternPart::Months.parse("DEC").unwrap(),
            PatternPartType::Particular(PatternPartValue::Month(12))
        );
        assert_eq!(
            PatternPart::Dows.parse("3").unwrap(),
            PatternPartType::Particular(PatternPartValue::Dow(3))
        );
        assert_eq!(
            PatternPart::Dows.parse("FRI").unwrap(),
            PatternPartType::Particular(PatternPartValue::Dow(5))
        );
        assert_eq!(
            PatternPart::Years.parse("2023").unwrap(),
            PatternPartType::Particular(PatternPartValue::Year(2023))
        );

        // Test last and weekday
        assert_eq!(
            PatternPart::Dows.parse("4L").unwrap(),
            PatternPartType::LastDow(PatternPartValue::Dow(4))
        );
        assert_eq!(
            PatternPart::Dows.parse("FriL").unwrap(),
            PatternPartType::LastDow(PatternPartValue::Dow(5))
        );
        assert_eq!(PatternPart::Doms.parse("L").unwrap(), PatternPartType::LastDom);
        assert_eq!(
            PatternPart::Doms.parse("22W").unwrap(),
            PatternPartType::Weekday(PatternPartValue::Dom(22))
        );
    }

    #[test]
    fn test_pattern_part_split_valid_list_values() {
        // Test comma-separated list
        assert_eq!(
            PatternPart::Hours.parse("9,10,11").unwrap(),
            PatternPartType::List(vec![
                PatternPartType::Particular(PatternPartValue::Hour(9)),
                PatternPartType::Particular(PatternPartValue::Hour(10)),
                PatternPartType::Particular(PatternPartValue::Hour(11))
            ])
        );

        assert_eq!(
            PatternPart::Seconds.parse("5,10-20,33/2,*/3,40-59/4").unwrap(),
            PatternPartType::List(vec![
                PatternPartType::Particular(PatternPartValue::Second(5)),
                PatternPartType::Range(PatternPartValue::Second(10), PatternPartValue::Second(20)),
                PatternPartType::RepeatingValue(PatternPartValue::Second(33), 2),
                PatternPartType::RepeatingValue(PatternPartValue::Second(0), 3),
                PatternPartType::RepeatingRange(PatternPartValue::Second(40), PatternPartValue::Second(59), 4),
            ])
        );

        assert_eq!(
            PatternPart::Months.parse("9,JAN,mar,*/2").unwrap(),
            PatternPartType::List(vec![
                PatternPartType::Particular(PatternPartValue::Month(9)),
                PatternPartType::Particular(PatternPartValue::Month(1)),
                PatternPartType::Particular(PatternPartValue::Month(3)),
                PatternPartType::RepeatingValue(PatternPartValue::Month(1), 2)
            ])
        );

        assert_eq!(
            PatternPart::Dows.parse("mon,FrI,0").unwrap(),
            PatternPartType::List(vec![
                PatternPartType::Particular(PatternPartValue::Dow(1)),
                PatternPartType::Particular(PatternPartValue::Dow(5)),
                PatternPartType::Particular(PatternPartValue::Dow(0))
            ])
        );

        assert_eq!(
            PatternPart::Doms.parse("1,5-12,24W,L").unwrap(),
            PatternPartType::List(vec![
                PatternPartType::Particular(PatternPartValue::Dom(1)),
                PatternPartType::Range(PatternPartValue::Dom(5), PatternPartValue::Dom(12)),
                PatternPartType::Weekday(PatternPartValue::Dom(24)),
                PatternPartType::LastDom,
            ])
        );
    }

    #[test]
    fn test_pattern_part_split_invalid_single_values() {
        // Test invalid single values
        assert!(PatternPart::Seconds.parse("-1").is_err());
        assert!(PatternPart::Seconds.parse("60").is_err());
        assert!(PatternPart::Seconds.parse(" 50").is_err());

        assert!(PatternPart::Minutes.parse("-1").is_err());
        assert!(PatternPart::Minutes.parse("60").is_err());
        assert!(PatternPart::Minutes.parse(" 20").is_err());

        assert!(PatternPart::Hours.parse("-1").is_err());
        assert!(PatternPart::Hours.parse("24").is_err());
        assert!(PatternPart::Hours.parse(" 12").is_err());

        assert!(PatternPart::Doms.parse("-1").is_err());
        assert!(PatternPart::Doms.parse("0").is_err());
        assert!(PatternPart::Doms.parse("32").is_err());
        assert!(PatternPart::Doms.parse(" 5").is_err());

        assert!(PatternPart::Months.parse("-1").is_err());
        assert!(PatternPart::Months.parse("0").is_err());
        assert!(PatternPart::Months.parse("13").is_err());
        assert!(PatternPart::Months.parse(" 6").is_err());
        assert!(PatternPart::Months.parse("JANUARY").is_err());
        assert!(PatternPart::Months.parse(" JAN").is_err());

        assert!(PatternPart::Dows.parse("-1").is_err());
        assert!(PatternPart::Dows.parse("7").is_err());
        assert!(PatternPart::Dows.parse(" 4").is_err());
        assert!(PatternPart::Dows.parse("Sunday").is_err());
        assert!(PatternPart::Dows.parse(" MON").is_err());

        assert!(PatternPart::Years.parse("-1").is_err());
        assert!(PatternPart::Years.parse("0").is_err());
        assert!(PatternPart::Years.parse("1969").is_err());
        assert!(PatternPart::Years.parse("2100").is_err());
        assert!(PatternPart::Years.parse(" 2023").is_err());

        // Test patterns with invalid ranges
        assert!(PatternPart::Seconds.parse("10-20-30").is_err());
        assert!(PatternPart::Seconds.parse("10-").is_err());
        assert!(PatternPart::Seconds.parse("-20").is_err());
        assert!(PatternPart::Seconds.parse("abc-20").is_err());

        assert!(PatternPart::Months.parse("feb-jan").is_err());
        assert!(PatternPart::Months.parse("5-3").is_err());
        assert!(PatternPart::Months.parse(" 1-3").is_err());

        // Test patterns with invalid repeating values
        assert!(PatternPart::Hours.parse("*/0").is_err());
        assert!(PatternPart::Hours.parse("0/0").is_err());
        assert!(PatternPart::Hours.parse("-1/0").is_err());
        assert!(PatternPart::Hours.parse("10/1").is_err());

        // Test patterns with invalid repeating ranges
        assert!(PatternPart::Doms.parse("10-5/2").is_err());
        assert!(PatternPart::Doms.parse("0-12/0").is_err());
        assert!(PatternPart::Doms.parse(" 0-12/3").is_err());
        assert!(PatternPart::Years.parse("1980-2050/0").is_err());

        // Test patterns with invalid hash patterns
        assert!(PatternPart::Dows.parse("MON#0").is_err());
        assert!(PatternPart::Dows.parse("MON#").is_err());
        assert!(PatternPart::Dows.parse("MON#abc").is_err());
        assert!(PatternPart::Dows.parse("MON#-1").is_err());

        //Test patterns with invalid last day
        assert!(PatternPart::Dows.parse("MODL").is_err());
        assert!(PatternPart::Dows.parse("L#2").is_err());
        assert!(PatternPart::Dows.parse("L#").is_err());
        assert!(PatternPart::Doms.parse(" L").is_err());
        assert!(PatternPart::Doms.parse("L ").is_err());
        assert!(PatternPart::Doms.parse("1L").is_err());

        // Test patterns with invalid question mark
        assert!(PatternPart::Seconds.parse("?").is_err());
        assert!(PatternPart::Minutes.parse("?").is_err());
        assert!(PatternPart::Hours.parse("?").is_err());
        assert!(PatternPart::Months.parse("?").is_err());
        assert!(PatternPart::Years.parse("?").is_err());
    }

    #[test]
    fn test_pattern_part_split_invalid_list_values() {
        // Test invalid list values
        assert!(PatternPart::Seconds.parse("5, 10-20, 33/2, */3, 40-59/4, abc").is_err());
        assert!(PatternPart::Seconds.parse("5, 10-20, 33/2, */3, 40-59/4, 60").is_err());
        assert!(PatternPart::Seconds.parse("5, 10-20, 33/2, */3, 40-59/4, -1").is_err());

        assert!(PatternPart::Minutes.parse("30, 45, 60, 75").is_err());
        assert!(PatternPart::Minutes.parse("30, 45, 60, -1").is_err());

        assert!(PatternPart::Hours.parse("12, 24, 36, abc").is_err());
        assert!(PatternPart::Hours.parse("12, 24, 36, -1").is_err());

        assert!(PatternPart::Doms.parse("15, 30, 45, 60, abc").is_err());
        assert!(PatternPart::Doms.parse("15, 30, 45, 60, -1").is_err());

        assert!(PatternPart::Months.parse("6, JAN, mar, */2, abc").is_err());
        assert!(PatternPart::Months.parse("6, JAN, mar, */2, 13").is_err());

        assert!(PatternPart::Dows.parse("3, mon, Fri, abc").is_err());
        assert!(PatternPart::Dows.parse("3, mon, Fri, 7").is_err());

        assert!(PatternPart::Dows.parse("1, 5-12, 24W, L, abc").is_err());
        assert!(PatternPart::Dows.parse("1, 5-12, 24W, L, 8").is_err());

        // Test case with asterisk and other values in the list
        assert!(PatternPart::Dows.parse("*,1").is_err());
        assert!(PatternPart::Dows.parse("2,*").is_err());
        assert!(PatternPart::Dows.parse("?,2").is_err());
        assert!(PatternPart::Doms.parse("*,1").is_err());
        assert!(PatternPart::Doms.parse("2,*").is_err());
        assert!(PatternPart::Doms.parse("?,2").is_err());

        assert!(PatternPart::Seconds.parse(",*").is_err());
        assert!(PatternPart::Seconds.parse("1,*").is_err());
        assert!(PatternPart::Years.parse("1977,*").is_err());
    }

    #[test]
    fn test_pattern_parsing_valid() {
        assert_eq!(
            Pattern::new("0 12 * * *").unwrap(),
            Pattern {
                pattern: "0 12 * * *".to_string(),
                parts: [
                    PatternPartType::Particular(PatternPartValue::Second(0)),
                    PatternPartType::Particular(PatternPartValue::Minute(0)),
                    PatternPartType::Particular(PatternPartValue::Hour(12)),
                    PatternPartType::All,
                    PatternPartType::All,
                    PatternPartType::All,
                    PatternPartType::All
                ]
            }
        );

        assert_eq!(
            Pattern::new(
                "15/5 5-20/2 12,13,22 1-12/2,15W,L 12,JAN,Feb-MAr,Aug/3 mon,fri#4,SatL 2000-2020/2,2050,2060/5"
            )
            .unwrap(),
            Pattern {
                pattern:
                    "15/5 5-20/2 12,13,22 1-12/2,15W,L 12,JAN,Feb-MAr,Aug/3 mon,fri#4,SatL 2000-2020/2,2050,2060/5"
                        .to_string(),
                parts: [
                    PatternPartType::RepeatingValue(PatternPartValue::Second(15), 5),
                    PatternPartType::RepeatingRange(PatternPartValue::Minute(5), PatternPartValue::Minute(20), 2),
                    PatternPartType::List(vec![
                        PatternPartType::Particular(PatternPartValue::Hour(12)),
                        PatternPartType::Particular(PatternPartValue::Hour(13)),
                        PatternPartType::Particular(PatternPartValue::Hour(22))
                    ]),
                    PatternPartType::List(vec![
                        PatternPartType::RepeatingRange(PatternPartValue::Dom(1), PatternPartValue::Dom(12), 2),
                        PatternPartType::Weekday(PatternPartValue::Dom(15)),
                        PatternPartType::LastDom
                    ]),
                    PatternPartType::List(vec![
                        PatternPartType::Particular(PatternPartValue::Month(12)),
                        PatternPartType::Particular(PatternPartValue::Month(1)),
                        PatternPartType::Range(PatternPartValue::Month(2), PatternPartValue::Month(3)),
                        PatternPartType::RepeatingValue(PatternPartValue::Month(8), 3)
                    ]),
                    PatternPartType::List(vec![
                        PatternPartType::Particular(PatternPartValue::Dow(1)),
                        PatternPartType::Hash(PatternPartValue::Dow(5), 4),
                        PatternPartType::LastDow(PatternPartValue::Dow(6))
                    ]),
                    PatternPartType::List(vec![
                        PatternPartType::RepeatingRange(PatternPartValue::Year(2000), PatternPartValue::Year(2020), 2),
                        PatternPartType::Particular(PatternPartValue::Year(2050)),
                        PatternPartType::RepeatingValue(PatternPartValue::Year(2060), 5)
                    ])
                ]
            }
        );
    }

    #[test]
    fn test_pattern_part_indexing() {
        let arr = [1, 2, 3, 4, 5, 6, 7];

        assert_eq!(arr[PatternPart::Seconds], 1);
        assert_eq!(arr[PatternPart::Minutes], 2);
        assert_eq!(arr[PatternPart::Hours], 3);
        assert_eq!(arr[PatternPart::Doms], 4);
        assert_eq!(arr[PatternPart::Months], 5);
        assert_eq!(arr[PatternPart::Dows], 6);
        assert_eq!(arr[PatternPart::Years], 7);
    }
}
