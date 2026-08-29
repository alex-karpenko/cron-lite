/// Generator of a series of numbers.
use std::ops::{Add, Sub};

/// Generator (iterator) state.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SeriesWithStep<T: Copy> {
    max: T,
    step: T,
    next: Option<T>,
}

impl<T> SeriesWithStep<T>
where
    T: Copy + Add<Output = T> + Sub<Output = T> + PartialOrd,
{
    /// Constructs a new series generator.
    ///
    /// # Panics
    /// Panics if `max < min`, `start` is out of bounds (`start < min || start > max`), or `step` is 0.
    /// In practice, callers in `pattern.rs` validate range bounds and steps prior to construction.
    #[inline]
    #[allow(clippy::eq_op)]
    pub fn new(min: T, max: T, step: T, start: T) -> Self {
        assert!(max >= min, "max value is less than min value");
        assert!(
            !(start < min || start > max),
            "start value is less than min or greater than max"
        );
        let zero = step - step;
        assert!(step > zero, "step value is 0");

        let next = if start == min {
            min
        } else {
            let mut next = min;
            while next < start {
                if max - next < step {
                    break;
                }
                next = next + step;
            }
            next
        };

        let next = (start..=max).contains(&next).then_some(next);

        Self { max, step, next }
    }
}

impl<T> Iterator for SeriesWithStep<T>
where
    T: Copy + Add<Output = T> + Sub<Output = T> + PartialOrd,
{
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let current = self.next?;
        if self.max - current < self.step {
            self.next = None;
        } else {
            self.next = Some(current + self.step);
        }
        Some(current)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;
    use rstest_reuse::{apply, template};
    use std::time::Duration;

    #[template]
    #[rstest]
    #[timeout(Duration::from_secs(1))]
    #[case(0, 5, 1, 0, vec![0, 1, 2, 3, 4, 5])]
    #[case(0, 5, 2, 0, vec![0, 2, 4])]
    #[case(0, 5, 5, 0 , vec![0, 5])]
    #[case(0, 5, 6, 0 , vec![0])]
    #[case(0, 5, 10, 0, vec![0])]
    #[case(0, 15, 5, 0, vec![0, 5, 10, 15])]
    #[case(0, 15, 5, 1, vec![5, 10, 15])]
    #[case(0, 15, 5, 4, vec![5, 10, 15])]
    #[case(0, 15, 5, 5, vec![5, 10, 15])]
    #[case(0, 15, 5, 6, vec![10, 15])]
    #[case(0, 15, 5, 6, vec![10, 15])]
    #[case(10, 39, 20, 10, vec![10, 30])]
    #[case(10, 40, 30, 20, vec![40])]
    #[case(10, 40, 31, 20, vec![])]
    fn series_with_step<T>(
        #[case] min: T,
        #[case] max: T,
        #[case] step: T,
        #[case] start: T,
        #[case] expected: Vec<T>,
    ) {
    }

    #[apply(series_with_step)]
    fn series_with_step_u8(min: u8, max: u8, step: u8, start: u8, expected: Vec<u8>) {
        assert_eq!(
            SeriesWithStep::<u8>::new(min, max, step, start).collect::<Vec<u8>>(),
            expected
        );
    }

    #[apply(series_with_step)]
    fn series_with_step_u16(min: u16, max: u16, step: u16, start: u16, expected: Vec<u16>) {
        assert_eq!(
            SeriesWithStep::<u16>::new(min, max, step, start).collect::<Vec<u16>>(),
            expected
        );
    }

    #[template]
    #[rstest]
    #[timeout(Duration::from_secs(1))]
    #[case(10, 5, 1, 6)]
    #[case(0, 5, 0, 0)]
    #[case(10, 5, 1, 0)]
    #[case(10, 5, 0, 0)]
    #[case(0, 5, 1, 6)]
    #[case(2, 5, 1, 1)]
    fn series_should_panic<T>(#[case] min: T, #[case] max: T, #[case] step: T, #[case] start: T) {}

    // Each case below panics for a different reason (max < min, start out of bounds, or
    // step == 0) so the shared `expected` substring below only asserts the common part of
    // SeriesWithStep::new's panic messages, not a single specific one.
    #[apply(series_should_panic)]
    #[should_panic(expected = "value")]
    fn series_should_panic_u8(min: u8, max: u8, step: u8, start: u8) {
        SeriesWithStep::<u8>::new(min, max, step, start);
    }

    #[apply(series_should_panic)]
    #[should_panic(expected = "value")]
    fn series_should_panic_u16(min: u16, max: u16, step: u16, start: u16) {
        SeriesWithStep::<u16>::new(min, max, step, start);
    }

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn series_boundary_no_overflow_u8() {
        assert_eq!(
            SeriesWithStep::<u8>::new(254, 255, 2, 254).collect::<Vec<_>>(),
            vec![254]
        );
    }

    #[rstest]
    #[timeout(Duration::from_secs(1))]
    fn series_boundary_no_overflow_u16() {
        assert_eq!(
            SeriesWithStep::<u16>::new(65534, 65535, 2, 65534).collect::<Vec<_>>(),
            vec![65534]
        );
    }
}
