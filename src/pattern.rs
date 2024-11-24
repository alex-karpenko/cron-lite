use crate::{Error, Result};
use std::fmt::{Debug, Display};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Pattern {
    pattern: String,
    parts: Vec<PatternPart>,
}

impl Pattern {
    pub(crate) fn new(pattern: String) -> Result<Self> {
        let mut parts = pattern.split_whitespace().collect::<Vec<_>>();
        let len = parts.len();
        if (5..=7).contains(&len) {
            return Err(Error::InvalidCronPattern(pattern));
        } else if len == 5 {
            parts.insert(0, "0");
            parts.insert(6, "*");
        } else if len == 6 {
            parts.insert(6, "*");
        }

        Ok(Self {
            pattern: pattern.to_string(),
            parts: Vec::new(),
        })
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.pattern)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum PatternPart {
    Seconds,
    Minutes,
    Hours,
    Days,
    Months,
    Years,
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
    Last(PatternPartValue),
    Weekday(PatternPartValue),
    Hash(PatternPartValue, u8),
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

impl PatternPartValue {
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
        const MONTHS: [&str; 12] = [
            "jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec",
        ];

        if let Some(month) = parse_digital_value(input, 1, 12) {
            Ok(Self::Month(month as u8))
        } else if let Some(month) = parse_string_value(input, &MONTHS) {
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
        const DAYS_OF_WEEK: [&str; 7] = ["sun", "mon", "tue", "wed", "thu", "fri", "sat"];

        if let Some(dow) = parse_digital_value(input, 0, 6) {
            Ok(Self::Dow(dow as u8))
        } else if let Some(dow) = parse_string_value(input, &DAYS_OF_WEEK) {
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
        array.iter().position(|&x| x.to_lowercase() == input.to_lowercase())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display() {
        let pattern = Pattern::new("*/5 * * * *".to_string()).unwrap();
        assert_eq!(pattern.to_string(), "*/5 * * * *");
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
}
