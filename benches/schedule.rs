use chrono::DateTime;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use cron_lite::Schedule;

const EXPRESSIONS: &[&str] = &[
    "@hourly",
    "0 * * * * * *",
    "0 * * * 1,7 * *",
    "0 * * * 2/2 * *",
    "0 * * * 6 * *",
    "0 * * * 6-12/3 * *",
    "0 * * * JAN-DEC *",
];

const NOW: &[&str] = &["1999-12-31T23:59:59Z", "2000-01-01T00:00:00Z", "2099-12-31T23:59:59Z"];
const TAKE_SAMPLES: usize = 10_000;

#[cfg(feature = "tz")]
const TIME_ZONES: &[&str] = &["UTC", "EET", "Europe/Kyiv"];

pub fn new_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("new");
    for expression in EXPRESSIONS {
        group.bench_with_input(BenchmarkId::from_parameter(expression), expression, |b, e| {
            b.iter(|| Schedule::new(*e).unwrap())
        });

        #[cfg(feature = "tz")]
        for tz in TIME_ZONES {
            let expression = format!("TZ={tz} {expression}");
            group.bench_with_input(BenchmarkId::from_parameter(expression.clone()), &expression, |b, e| {
                b.iter(|| Schedule::new(e).unwrap())
            });
        }
    }
    group.finish();
}

pub fn upcoming_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("upcoming");
    for expression in EXPRESSIONS {
        for now_str in NOW {
            let now = DateTime::parse_from_rfc3339(now_str).unwrap();
            let schedule = Schedule::new(*expression).unwrap();
            group.bench_with_input(
                BenchmarkId::from_parameter(format!("{now_str}/{expression}")),
                &(now, &schedule),
                |b, (now, schedule)| b.iter(|| schedule.upcoming(now)),
            );

            #[cfg(feature = "tz")]
            for tz in TIME_ZONES {
                let expression = format!("TZ={tz} {expression}");
                let schedule = Schedule::new(&expression).unwrap();
                group.bench_with_input(
                    BenchmarkId::from_parameter(format!("{now_str}/{expression}")),
                    &(now, &schedule),
                    |b, (now, schedule)| b.iter(|| schedule.upcoming(now)),
                );
            }
        }
    }
    group.finish();
}

pub fn iter_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("iter");
    for expression in EXPRESSIONS {
        for now_str in NOW {
            let now = DateTime::parse_from_rfc3339(now_str).unwrap();
            let schedule = Schedule::new(*expression).unwrap();
            group.bench_with_input(
                BenchmarkId::from_parameter(format!("{now_str}/{expression}")),
                &(now, &schedule),
                |b, (now, schedule)| b.iter(|| schedule.iter(now).take(TAKE_SAMPLES).count()),
            );

            #[cfg(feature = "tz")]
            for tz in TIME_ZONES {
                let expression = format!("TZ={tz} {expression}");
                let schedule = Schedule::new(&expression).unwrap();
                group.bench_with_input(
                    BenchmarkId::from_parameter(format!("{now_str}/{expression}")),
                    &(now, &schedule),
                    |b, (now, schedule)| b.iter(|| schedule.iter(now).take(TAKE_SAMPLES).count()),
                );
            }
        }
    }
    group.finish();
}

criterion_group!(benches, new_benchmark, upcoming_benchmark, iter_benchmark);
criterion_main!(benches);
