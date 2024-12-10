/// Common utility functions.
use crate::pattern::PatternValueType;
use std::cmp::Ordering;

/// Converts string into unsigned number with bounds validation.
pub(crate) fn parse_digital_value(
    input: &str,
    min: PatternValueType,
    max: PatternValueType,
) -> Option<PatternValueType> {
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

/// Converts string with mnemonic value representation into unsigned number.
pub(crate) fn parse_string_value(input: &str, values: &[&str]) -> Option<PatternValueType> {
    if input.is_empty() {
        None
    } else {
        values
            .iter()
            .position(|&x| x.to_uppercase() == input.to_uppercase())
            .map(|i| i as PatternValueType)
    }
}

/// Returns `true` if provided year is leap.
#[inline]
pub(crate) fn is_leap_year(year: PatternValueType) -> bool {
    year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)
}

/// Returns number of days in specified month.
pub(crate) fn days_in_month(year: PatternValueType, month: PatternValueType) -> PatternValueType {
    if month == 0 || month > 12 {
        panic!("Invalid month: {month}");
    }

    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if is_leap_year(year) => 29,
        2 => 28,
        _ => unreachable!(),
    }
}

/// Calculates day of week for specified date.
pub(crate) fn day_of_week(year: PatternValueType, month: PatternValueType, day: PatternValueType) -> PatternValueType {
    if day == 0 || month == 0 || month > 12 || day > days_in_month(year, month) {
        panic!("Invalid date: {year:04}-{month:02}-{day:02}");
    }

    let month_offset: PatternValueType = if is_leap_year(year) {
        [0, 3, 4, 0, 2, 5, 0, 3, 6, 1, 4, 6]
    } else {
        [0, 3, 3, 6, 1, 4, 6, 2, 5, 0, 3, 5]
    }[(month - 1) as usize];

    let year = year - 1;

    ((day + month_offset + 5 * (year % 4) + 4 * (year % 100) + 6 * (year % 400)) % 7) as PatternValueType
}

/// Returns day in the month for the last specified day of the week.
pub(crate) fn last_dow(year: PatternValueType, month: PatternValueType, dow: PatternValueType) -> PatternValueType {
    if month == 0 || month > 12 || dow > 6 {
        panic!("Invalid month or day of week: {month:02}/{dow}");
    }

    let mut last_day = days_in_month(year, month);

    while day_of_week(year, month, last_day) != dow {
        last_day -= 1;
    }

    last_day
}

/// Returns date (day in the month) of the specified N-th day of the week.
pub(crate) fn nth_dow(
    year: PatternValueType,
    month: PatternValueType,
    dow: PatternValueType,
    n: PatternValueType,
) -> PatternValueType {
    if month == 0 || month > 12 || dow > 6 || n == 0 || n > 4 {
        panic!("Invalid month, day of week or nth occurrence: {month:02}/{dow}/{n}");
    }

    let first_dow = day_of_week(year, month, 1);

    let mut day = 1 + (n - 1) * 7;

    match first_dow.cmp(&dow) {
        Ordering::Greater => day += 7 - (first_dow - dow),
        Ordering::Less => day += dow - first_dow,
        Ordering::Equal => {}
    }

    if day > days_in_month(year, month) {
        panic!("Invalid date: {year:04}-{month:02}-{day:02}");
    }

    day
}

/// Returns date of the weekday (not Sundays or Saturday) nearest to the specified date in the same month.
pub(crate) fn nearest_weekday(
    year: PatternValueType,
    month: PatternValueType,
    day: PatternValueType,
) -> PatternValueType {
    if day == 0 || month == 0 || month > 12 || day > days_in_month(year, month) {
        panic!("Invalid date: {year:04}-{month:02}-{day:02}");
    }

    let dow = day_of_week(year, month, day);
    let days_in_month = days_in_month(year, month);

    // middle of the week
    if dow > 0 && dow < 6 {
        day
    } else if dow == 0 {
        // sunday
        if day == days_in_month {
            day - 2
        } else {
            day + 1
        }
    } else {
        // saturday
        if day > 1 {
            day - 1
        } else {
            day + 2
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;
    use std::time::Duration;

    #[test]
    fn parse_digital_value_valid_value_within_range() {
        assert_eq!(parse_digital_value("5", 0, 10), Some(5));
        assert_eq!(parse_digital_value("0", 0, 10), Some(0));
        assert_eq!(parse_digital_value("10", 0, 10), Some(10));
    }

    #[test]
    fn parse_digital_value_value_below_minimum() {
        assert_eq!(parse_digital_value("5", 10, 20), None);
    }

    #[test]
    fn parse_digital_value_value_above_maximum() {
        assert_eq!(parse_digital_value("25", 0, 20), None);
    }

    #[test]
    fn parse_digital_value_invalid_input() {
        assert_eq!(parse_digital_value("abc", 0, 10), None);
        assert_eq!(parse_digital_value("", 0, 10), None);
        assert_eq!(parse_digital_value("-1", 0, 10), None);
        assert_eq!(parse_digital_value("1.5", 0, 10), None);
    }

    #[test]
    fn parse_digital_value_edge_cases() {
        // Test with min equal to max
        assert_eq!(parse_digital_value("5", 5, 5), Some(5));
        assert_eq!(parse_digital_value("4", 5, 5), None);
        assert_eq!(parse_digital_value("6", 5, 5), None);

        // Test with large valid numbers
        assert_eq!(parse_digital_value("65535", 0, 65535), Some(65535));
    }

    #[test]
    fn parse_string_value_regular() {
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

        // Test with a different array
        let months = &["jan", "feb", "mar"];
        assert_eq!(parse_string_value("feb", months), Some(1));
        assert_eq!(parse_string_value("FEB", months), Some(1));
        assert_eq!(parse_string_value("dec", months), None);
    }

    #[test]
    fn parse_string_value_empty_array() {
        let empty_array: &[&str] = &[];
        assert_eq!(parse_string_value("test", empty_array), None);
    }

    #[test]
    fn parse_string_value_whitespace() {
        let array = &["test", "value"];
        assert_eq!(parse_string_value(" test ", array), None);
        assert_eq!(parse_string_value("\ttest", array), None);
    }

    #[rstest]
    // Test leap years divisible by 4 but not 100
    #[case(2024, true)]
    #[case(1996, true)]
    // Test leap years divisible by 400
    #[case(2000, true)]
    #[case(1600, true)]
    // Test non-leap years not divisible by 4
    #[case(2023, false)]
    #[case(2021, false)]
    // Test non-leap years divisible by 100 but not 400
    #[case(1900, false)]
    #[case(2100, false)]
    fn test_is_leap_year(#[case] year: PatternValueType, #[case] expected: bool) {
        assert_eq!(
            is_leap_year(year),
            expected,
            "{year:} is {}",
            if expected { "leap" } else { "not-leap" }
        );
    }

    #[rstest]
    // Test months with 31 days
    #[case(2023, 1, 31)] // January
    #[case(2023, 3, 31)] // March
    #[case(2023, 5, 31)] // May
    #[case(2023, 7, 31)] // July
    #[case(2023, 8, 31)] // August
    #[case(2023, 10, 31)] // October
    #[case(2023, 12, 31)] // December
    // Test months with 30 days
    #[case(2023, 4, 30)] // April
    #[case(2023, 6, 30)] // June
    #[case(2023, 9, 30)] // September
    #[case(2023, 11, 30)] // November
    // Test February in non-leap year
    #[case(2023, 2, 28)]
    // Test February in leap years
    #[case(2024, 2, 29)]
    #[case(2020, 2, 29)]
    #[case(2000, 2, 29)]
    // Test February in century years (not leap unless divisible by 400)
    #[case(1900, 2, 28)]
    #[case(2100, 2, 28)]
    fn test_days_in_month(
        #[case] y: PatternValueType,
        #[case] m: PatternValueType,
        #[case] expected: PatternValueType,
    ) {
        assert_eq!(days_in_month(y, m), expected, "{y:04}-{m:02} has {expected} days");
    }

    #[rstest]
    #[case(2023, 0)]
    #[case(2023, 13)]
    #[should_panic(expected = "Invalid month")]
    fn test_days_in_month_invalid(#[case] y: PatternValueType, #[case] m: PatternValueType) {
        days_in_month(y, m);
    }

    #[rstest]
    // Test regular days
    #[case(2023, 12, 25, 1)] // Monday
    #[case(2024, 1, 1, 1)] // Monday
    #[case(2025, 1, 1, 3)] // Wednesday
    #[case(2024, 2, 29, 4)] // Thursday (leap year)
    #[case(2023, 1, 1, 0)] // Sunday
    // Test edge cases
    #[case(2000, 1, 1, 6)] // Saturday (century leap year)
    #[case(1900, 1, 1, 1)] // Monday (non-leap century year)
    // Test different months
    #[case(2023, 3, 15, 3)] // Wednesday
    #[case(2023, 7, 4, 2)] // Tuesday
    #[case(2023, 10, 31, 2)] // Tuesday
    // Randomly picked days
    #[case(1971, 8, 21, 6)]
    #[case(1945, 6, 22, 5)]
    #[case(2020, 2, 29, 6)]
    #[case(2099, 1, 1, 4)]
    #[case(2100, 1, 1, 5)]
    #[case(2400, 1, 1, 6)]
    fn test_day_of_week(
        #[case] y: PatternValueType,
        #[case] m: PatternValueType,
        #[case] d: PatternValueType,
        #[case] expected: PatternValueType,
    ) {
        assert_eq!(
            day_of_week(y, m, d),
            expected,
            "date {y}-{m:02}-{d:02}, should be {expected}"
        );
    }

    #[rstest]
    #[case(2023, 2, 29)]
    #[case(2024, 0, 1)]
    #[case(2023, 13, 22)]
    #[case(2025, 1, 0)]
    #[case(2024, 1, 32)]
    #[case(2023, 4, 31)]
    #[should_panic(expected = "Invalid date: ")]

    fn test_day_of_week_invalid_date(
        #[case] y: PatternValueType,
        #[case] m: PatternValueType,
        #[case] d: PatternValueType,
    ) {
        day_of_week(y, m, d);
    }

    #[rstest]
    // Test last Sunday of different months
    #[case(2023, 12, 0, 31)] // Last Sunday of December 2023
    #[case(2023, 11, 0, 26)] // Last Sunday of November 2023
    #[case(2024, 2, 0, 25)] // Last Sunday of February 2024 (leap year)
    #[case(2023, 2, 0, 26)] // Last Sunday of February 2023 (non-leap year)
    // Test last day of different weekdays
    #[case(2023, 12, 1, 25)] // Last Monday of December 2023
    #[case(2023, 12, 2, 26)] // Last Tuesday of December 2023
    #[case(2023, 12, 3, 27)] // Last Wednesday of December 2023
    #[case(2023, 12, 4, 28)] // Last Thursday of December 2023
    #[case(2023, 12, 5, 29)] // Last Friday of December 2023
    #[case(2023, 12, 6, 30)] // Last Saturday of December 2023
    // Test edge cases
    #[case(2000, 2, 0, 27)] // Last Sunday of February in century leap year
    #[case(1900, 2, 0, 25)] // Last Sunday of February in non-leap century year
    #[timeout(Duration::from_secs(1))]
    fn test_last_dow(
        #[case] y: PatternValueType,
        #[case] m: PatternValueType,
        #[case] dow: PatternValueType,
        #[case] expected: PatternValueType,
    ) {
        assert_eq!(
            last_dow(y, m, dow),
            expected,
            "Last {} of {}-{:02} should be {}",
            [
                "Sunday",
                "Monday",
                "Tuesday",
                "Wednesday",
                "Thursday",
                "Friday",
                "Saturday"
            ][dow as usize],
            y,
            m,
            expected
        );
    }

    #[rstest]
    #[case(2023, 0, 0)] // Invalid month 0
    #[case(2023, 13, 0)] // Invalid month 13
    #[case(2023, 1, 7)] // Invalid day of week 7
    #[should_panic(expected = "Invalid month or day of week: ")]
    fn test_last_dow_invalid(#[case] y: PatternValueType, #[case] m: PatternValueType, #[case] dow: PatternValueType) {
        last_dow(y, m, dow);
    }

    #[rstest]
    // Test first occurrence of different weekdays
    #[case(2023, 12, 0, 1, 3)] // First Sunday of December 2023
    #[case(2023, 12, 1, 1, 4)] // First Monday of December 2023
    #[case(2023, 12, 2, 1, 5)] // First Tuesday of December 2023
    #[case(2023, 12, 3, 1, 6)] // First Wednesday of December 2023
    #[case(2023, 12, 4, 1, 7)] // First Thursday of December 2023
    #[case(2023, 12, 5, 1, 1)] // First Friday of December 2023
    #[case(2023, 12, 6, 1, 2)] // First Saturday of December 2023

    // Test different occurrences of the same weekday
    #[case(2023, 12, 0, 2, 10)] // Second Sunday of December 2023
    #[case(2023, 12, 0, 3, 17)] // Third Sunday of December 2023
    #[case(2023, 12, 0, 4, 24)] // Fourth Sunday of December 2023

    // Test edge cases
    #[case(2000, 2, 1, 4, 28)] // Fourth Monday of February in century leap year
    #[case(1900, 2, 3, 4, 28)] // Fourth Wednesday of February in non-leap century year

    // 1st DOM is Monday
    #[case(2024, 1, 1, 1, 1)]
    #[case(2024, 1, 1, 2, 8)]
    #[case(2024, 1, 2, 3, 16)]
    #[case(2024, 1, 3, 3, 17)]
    #[case(2024, 1, 4, 3, 18)]
    #[case(2024, 1, 5, 3, 19)]
    #[case(2024, 1, 6, 3, 20)]
    #[case(2024, 1, 0, 3, 21)]

    fn test_nth_dow(
        #[case] y: PatternValueType,
        #[case] m: PatternValueType,
        #[case] dow: PatternValueType,
        #[case] n: PatternValueType,
        #[case] expected: PatternValueType,
    ) {
        assert_eq!(
            nth_dow(y, m, dow, n),
            expected,
            "{}{} {} of {}-{:02} should be {}",
            n,
            match n {
                1 => "st",
                2 => "nd",
                3 => "rd",
                _ => "th",
            },
            [
                "Sunday",
                "Monday",
                "Tuesday",
                "Wednesday",
                "Thursday",
                "Friday",
                "Saturday"
            ][dow as usize],
            y,
            m,
            expected
        );
    }

    #[rstest]
    #[case(2023, 0, 0, 1)] // Invalid month 0
    #[case(2023, 13, 0, 1)] // Invalid month 13
    #[case(2023, 1, 7, 1)] // Invalid day of week 7
    #[case(2023, 1, 0, 0)] // Invalid nth 0
    #[case(2023, 1, 0, 5)] // Invalid nth 5
    #[case(2023, 1, 0, 6)] // Invalid nth 6
    #[case(2023, 12, 0, 6)] // Fifth Sunday of December 2023 (doesn't exist)
    #[should_panic(expected = "Invalid month, day of week or nth occurrence:")]
    fn test_nth_dow_invalid(
        #[case] y: PatternValueType,
        #[case] m: PatternValueType,
        #[case] dow: PatternValueType,
        #[case] n: PatternValueType,
    ) {
        nth_dow(y, m, dow, n);
    }

    #[rstest]
    // Test regular weekdays (Monday-Friday)
    #[case(2024, 1, 1, 1)] // Monday -> same day
    #[case(2024, 1, 2, 2)] // Tuesday -> same day
    #[case(2024, 1, 3, 3)] // Wednesday -> same day
    #[case(2024, 1, 4, 4)] // Thursday -> same day
    #[case(2024, 1, 5, 5)] // Friday -> same day

    // Test weekends
    #[case(2024, 1, 6, 5)] // Saturday -> Friday
    #[case(2024, 1, 7, 8)] // Sunday -> Monday

    // Test month boundaries
    #[case(2024, 1, 31, 31)] // Wednesday -> same day
    #[case(2024, 2, 1, 1)] // Thursday -> same day

    // Test leap year February
    #[case(2024, 2, 29, 29)] // Thursday -> same day

    // Test non-leap year February
    #[case(2023, 2, 28, 28)] // Tuesday -> same day

    // Test various months
    #[case(2024, 4, 30, 30)] // Tuesday -> same day
    #[case(2024, 6, 29, 28)] // Saturday -> Friday
    #[case(2024, 6, 30, 28)] // Sunday -> Monday (July 1)
    #[case(2024, 12, 31, 31)] // Tuesday -> same day

    // Test edge cases
    #[case(2024, 3, 31, 29)] // Last day is Sunday
    #[case(2024, 8, 31, 30)] // Last day is Saturday
    #[case(2024, 6, 1, 3)] // The first day is Saturday
    #[case(2024, 9, 1, 2)] // The first day is Sunday

    fn test_nearest_weekday(
        #[case] y: PatternValueType,
        #[case] m: PatternValueType,
        #[case] d: PatternValueType,
        #[case] expected: PatternValueType,
    ) {
        assert_eq!(
            nearest_weekday(y, m, d),
            expected,
            "Nearest weekday to {y}-{m:02}-{d:02} should be {y}-{m:02}-{expected:02}"
        );
    }

    #[rstest]
    #[case(2024, 0, 1)] // Invalid month 0
    #[case(2024, 13, 1)] // Invalid month 13
    #[case(2024, 1, 0)] // Invalid day 0
    #[case(2024, 1, 32)] // Invalid day 32
    #[case(2024, 4, 31)] // Invalid day 31 for April
    #[case(2023, 2, 29)] // Invalid day 29 for February in non-leap year
    #[should_panic(expected = "Invalid date")]
    fn test_nearest_weekday_invalid(
        #[case] y: PatternValueType,
        #[case] m: PatternValueType,
        #[case] d: PatternValueType,
    ) {
        nearest_weekday(y, m, d);
    }
}
