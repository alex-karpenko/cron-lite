/// Generator of numbers series.
use std::ops::{Add, AddAssign};

/// Generator (iterator) state.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct SeriesWithStep<T: Copy> {
    max: T,
    step: T,
    next: T,
}

impl<T> SeriesWithStep<T>
where
    T: Copy + Add + AddAssign + PartialOrd,
    <T as Add>::Output: PartialOrd<T>,
{
    /// Caller is responsible to ensure that
    /// maximum serial value (max+step) isn't greater than type's maximum.
    ///
    /// Panics if one of the parameters is out of bounds.
    #[inline]
    pub(crate) fn new(min: T, max: T, step: T, start: T) -> Self {
        if max < min {
            panic!("max value is less than min value");
        }

        if start < min || start > max {
            panic!("start value is less than min or greater than max");
        }

        if min + step == min {
            panic!("step value is 0");
        }

        let next = if start == min {
            min
        } else {
            let mut next = min;
            while next < start {
                next += step;
            }
            next
        };

        Self { next, max, step }
    }
}

impl<T> Iterator for SeriesWithStep<T>
where
    T: Copy + Add + AddAssign + PartialOrd,
{
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.next > self.max {
            None
        } else {
            let current = self.next;
            self.next += self.step;
            Some(current)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;
    use rstest_reuse::{apply, template};

    #[template]
    #[rstest]
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
    #[case(10, 5, 1, 6)]
    #[case(0, 5, 0, 0)]
    #[case(10, 5, 1, 0)]
    #[case(10, 5, 0, 0)]
    #[case(0, 5, 1, 6)]
    #[case(2, 5, 1, 1)]
    fn series_should_panic<T>(#[case] min: T, #[case] max: T, #[case] step: T, #[case] start: T) {}

    #[apply(series_should_panic)]
    #[should_panic]
    fn series_should_panic_u8(min: u8, max: u8, step: u8, start: u8) {
        SeriesWithStep::<u8>::new(min, max, step, start);
    }

    #[apply(series_should_panic)]
    #[should_panic]
    fn series_should_panic_u16(min: u16, max: u16, step: u16, start: u16) {
        SeriesWithStep::<u16>::new(min, max, step, start);
    }

    #[test]
    #[should_panic]
    fn series_should_panic_by_overflow_u8() {
        SeriesWithStep::<u8>::new(254, 255, 2, 254);
    }

    #[test]
    #[should_panic]
    fn series_should_panic_by_overflow_u16() {
        SeriesWithStep::<u16>::new(65534, 65535, 2, 65534);
    }
}
