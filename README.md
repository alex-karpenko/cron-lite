# cron-lite

Lightweight cron expression parser and time series generator.

<p>
<a href="https://github.com/alex-karpenko/cron-lite/actions/workflows/ci.yaml" rel="nofollow"><img src="https://img.shields.io/github/actions/workflow/status/alex-karpenko/cron-lite/ci.yaml?label=ci" alt="CI status"></a>
<a href="https://github.com/alex-karpenko/cron-lite/actions/workflows/audit.yaml" rel="nofollow"><img src="https://img.shields.io/github/actions/workflow/status/alex-karpenko/cron-lite/audit.yaml?label=audit" alt="Audit status"></a>
<a href="https://docs.rs/cron-lite" rel="nofollow"><img src="https://img.shields.io/docsrs/cron-lite" alt="docs.rs status"></a>
<a href="https://crates.io/crates/cron-lite" rel="nofollow"><img src="https://img.shields.io/crates/v/cron-lite" alt="Version at Crates.io"></a>
<a href="https://app.codecov.io/github/alex-karpenko/cron-lite" rel="nofollow"><img src="https://img.shields.io/codecov/c/github/alex-karpenko/cron-lite" alt="License"></a>
<a href="https://github.com/alex-karpenko/cron-lite/blob/HEAD/LICENSE" rel="nofollow"><img src="https://img.shields.io/github/license/alex-karpenko/cron-lite" alt="License"></a>
</p>

This tiny crate is intended to:

- parse almost all kinds of popular cron schedule formats;
- generate a series of timestamps according to the schedule.

It has a single external dependency - [chrono](https://crates.io/crates/chrono) (with default features set).

_This is not a cron job scheduler or runner._ If you need a scheduler/runner, look
for [sacs](https://crates.io/crates/sacs) or
any [other similar crate](https://crates.io/search?q=async%20cron%20scheduler).

## Cron schedule format

Traditionally, cron schedule expression has a 5-field format: minutes, hours, days, months, and days of the week.
This crate uses such a format by default, but two optional fields may be added, seconds and years:

- if _seconds_ is empty, `0` is used by default;
- if _years_ is empty, `*` is used by default;
- if a 6-field schedule is specified, then _seconds_ is assumed to be the first field, and years defaults to empty.

The table below describes valid values and patterns of each field:

| Field        | Required | Allowed values  | Allowed special characters |
| ------------ | -------- | --------------- | -------------------------- |
| Seconds      | No       | 0-59            | * , - /                    |
| Minutes      | Yes      | 0-59            | * , - /                    |
| Hours        | Yes      | 0-23            | * , - /                    |
| Day of Month | Yes      | 1-31            | * , - / ? L W              |
| Month        | Yes      | 1-12 or JAN-DEC | * , - /                    |
| Day of Week  | Yes      | 0-6 or SUN-SAT  | * , - ? L #                |
| Year         | No       | 1970-2099       | * , - /                    |

Patterns meanings:

- `*` - each possible value, i.e. `0,1,2,...,59` for minutes;
- `,` - list of values or patterns, i.e. `1,7,12`, `SUN,FRI`;
- `-` - range of values, i.e. `0-15`, `JAN-MAR`;
- `/` - repeating values, i.e. `*/12`, `10/5`, `30-59/2`;
- `L` - last day of the month (for month field), or last particular day of the week (for weekday field), i.e. `L` or
  `5L`;
- `W` - the weekday (not Sunday or Saturday), nearest to the specified days of month in the same month, i.e. `22W`;
- `#` - specific day of the week, i.e. `fri#1`, `1#4`;
- `?` - for days of month or week means that the value doesn't matter: if day of month is specified (not `*`), then
  day of week should be `?`, and vice versa.

Also, short aliases for well-known schedule expressions are allowed:

| Alias                      | Expression    |
| -------------------------- | ------------- |
| `@yearly` (or `@annually`) | 0 0 0 1 1 ? * |
| `@monthly`                 | 0 0 0 1 * ? * |
| `@weekly`                  | 0 0 0 ? * 0 * |
| `@daily` (or `@midnight`)  | 0 0 0 * * * * |
| `@hourly`                  | 0 0 * * * * * |

Some additional information, field descriptions, and relationships may be
found [here](https://en.wikipedia.org/wiki/Cron#Cron_expression) (this is not complete or exhaustive documentation).

### Schedule with timezone

If the `tz` feature is enabled, it's possible to prefix a cron schedule with a timezone, for example:

- `TZ=Europe/Paris @monthly`
- `TZ=EET 0 12 * * *`

## How to use

The single entity of the crate is a `Schedule` structure, which has several basic methods:

- `new()`: constructor to parse and validate the provided schedule;
- `upcoming()`: returns the time of the next schedule's event, starting from the provided timestamp;
- `iter()`: returns an `Iterator` which produces a series of timestamps according to the schedule;
- `sleep()`: falls asleep until the time of the upcoming schedule's event (`async` feature only);
- `stream()`: constructs a `Stream` which asynchronously generates events right at the scheduled time (`async`
  feature only).

### Example with `upcoming`

```rust
use chrono::Utc;
use cron_lite::{Result, Schedule};

fn main() -> Result<()> {
    let schedule = Schedule::new("0 0 0 * * *")?;
    let now = Utc::now();

    // Get the next event's timestamp starting from now
    let next = schedule.upcoming(&now).unwrap();
    println!("next: {next}");

    Ok(())
}
```

### Example with `iter`

```rust
use chrono::Utc;
use cron_lite::{Result, Schedule};

fn main() -> Result<()> {
    let schedule = Schedule::new("0 0 0 * * *")?;
    let now = Utc::now();

    // Get the next 10 timestamps starting from now
    schedule.iter(&now).take(10).for_each(|t| println!("next: {t}"));

    Ok(())
}
```

### Example with `stream`

```rust
use chrono::Local;
use cron_lite::{CronEvent, Result, Schedule};
use futures::stream::StreamExt;
async fn stream() -> Result<()> {
    let schedule = Schedule::new("*/15 * * * * *")?;
    let now = Local::now();
    // Wake up every 15 seconds 10 times starting from now but skip the first event.
    let mut s = schedule.stream(&now).skip(1).take(10);
    while let Some(event) = s.next().await {
        assert!(matches!(event, CronEvent::Ok(_)));
        println!("next: {event:?}");
    }
    Ok(())
}
```

## Feature flags

* `serde`: adds [`Serialize`](https://docs.rs/serde/latest/serde/trait.Serialize.html) and [
  `Deserialize`](https://docs.rs/serde/latest/serde/trait.Deserialize.html) trait implementations for `Schedule`.
* `tz`: enables support of cron [schedules with timezone](#schedule-with-timezone).
* `async`: adds several methods to use in async environments. See the module's documentation for details.

## Breaking changes: upgrading to 0.4.0 from the earlier versions

Version 0.4.0 hardens the public `CronError`/`CronEvent` API, eliminates unnecessary heap allocations, and closes a parsing-cost DoS gap:

1. **`CronError`'s two-field variants are now named-field structs, not tuples.** `InvalidCronPattern`,
   `InvalidDigitalValue`, `InvalidMnemonicValue`, `InvalidDayOfWeekValue`, `InvalidRangeValue`, and
   `InvalidRepeatingPattern` changed from `Variant(String, String)` to `Variant { value: String, field: String }`
   (or `{ pattern: String, field: String }` for the two pattern-holding variants). This mainly affects code that
   destructures these variants by position.
2. **`CronError` and `CronEvent` are now `#[non_exhaustive]`.** Any `match` that doesn't already end with a
   wildcard arm will fail to compile. This is what lets us add error/event variants in the future without another
   breaking release — for example, 0.4.0 itself adds `CronError::TooManyPatternValues`, returned when a schedule
   field's comma-separated list exceeds the number of distinct values that field can legally hold (a guard against
   parsing/evaluating adversarially large cron strings).
3. **`TryFrom<&String>` was removed.** Use `TryFrom<&str>` instead (e.g. `Schedule::try_from(s.as_str())` or `Schedule::try_from(&s[..])`).
4. **`ScheduleIterator` is now a public concrete type.** `Schedule::iter` and `Schedule::into_iter` return
   named `ScheduleIterator<Tz>` rather than opaque `impl Iterator<Item = DateTime<Tz>>`, enabling the iterator type to be stored in struct fields.
5. **`Schedule::new` now accepts `impl AsRef<str>`** instead of `impl Into<String>`, eliminating upfront heap allocation when passing string slices.

### Migration guide

**If you pattern-match on `CronError`'s two-field variants**, switch from positional to named-field syntax:

```rust
// before 0.4.0
match err {
    CronError::InvalidDigitalValue(value, field) => println!("{field}: {value}"),
    // ...
}

// 0.4.0+
match err {
    CronError::InvalidDigitalValue { value, field } => println!("{field}: {value}"),
    // ...
}
```

**If you exhaustively `match` on `CronError` or `CronEvent`** (no `_` arm), add one:

```rust
// 0.4.0+
match err {
    CronError::InvalidCronSchedule(_) => { /* ... */ }
    CronError::InvalidDaysPattern(_) => { /* ... */ }
    // ... other variants you handle ...
    _ => { /* handle any other/future variant */ }
}
```

**If you used `Schedule::try_from(&my_string)` with a borrowed `&String`**, borrow as `&str`:

```rust
// before 0.4.0
let schedule = Schedule::try_from(&my_string)?;

// 0.4.0+
let schedule = Schedule::try_from(my_string.as_str())?;
```

**If you handle `Schedule::new` errors generically** (e.g. just via `Display`/`to_string()`), no change is needed —
only variant *construction* and *exhaustive destructuring* are affected.

## License

This project is licensed under the [MIT license](LICENSE).
