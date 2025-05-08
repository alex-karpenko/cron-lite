//! Lightweight cron expression parser and time series generator.
#![deny(unsafe_code, warnings, missing_docs)]

//! This is a tiny crate, intended to:
//! - parse almost all kinds of popular cron schedule formats;
//! - generate series of timestamps according to the schedule.
//!
//! It has a single external dependency - [chrono](https://crates.io/crates/chrono).
//!
//! _This is not a cron jobs scheduler or runner._ If you need a scheduler/runner,
//! look for [sacs](https://crates.io/crates/sacs)
//! of any [other similar crate](https://crates.io/search?q=async%20cron%20scheduler).
//!
//! ## Cron schedule format
//!
//! Traditionally, cron schedule expression has a 5-fields format: minutes, hours, days, months and days of week.
//! This crate uses such a format by default, but two optional fields may be added, seconds and years:
//! - if _seconds_ is empty, `0` is used by default;
//! - if _years_ is empty, `*` is used by default;
//! - if 6-fields schedule is specified, then _seconds_ filed is assumed as first and years as empty (default).
//!
//! The table below describes valid values and patterns of each field:
//!
//! | Field        | Required | Allowed values  | Allowed special characters |
//! |--------------|----------|-----------------|----------------------------|
//! | Seconds      | No       | 0-59            | * , - /                    |
//! | Minutes      | Yes      | 0-59            | * , - /                    |
//! | Hours        | Yes      | 0-23            | * , - /                    |
//! | Day of Month | Yes      | 1-31            | * , - / ? L W              |
//! | Month        | Yes      | 1-12 or JAN-DEC | * , - /                    |
//! | Day of Week  | Yes      | 0-6 or SUN-SAT  | * , - ? L #                |
//! | Year         | No       | 1970-2099       | * , - /                    |
//!
//! Patterns meanings:
//! - `*` - each possible value, i.e. `0,1,2,...,59` for minutes;
//! - `,` - list of values or patterns, i.e. `1,7,12`, `SUN,FRI`;
//! - `-` - range of values, i.e. `0-15`, `JAN-MAR`;
//! - `/` - repeating values, i.e. `*/12`, `10/5`, `30-59/2`;
//! - `L` - last day of the month (for month field), or last particular day of the week (for weekday field), i.e. `L` or `5L`;
//! - `W` - the weekday (not Sunday or Saturday), nearest to the specified days of month in the same month, i.e. `22W`;
//! - `#` - specific day of the week, i.e. `fri#1`, `1#4`;
//! - `?` - for days of month or week means that value doesn't matter: if day of month is specified (not `*`), then day of week should be `?` and vise versa.
//!
//! Also, short aliases for well-known schedule expressions are allowed:
//!
//! | Alias                      | Expression    |
//! |----------------------------|---------------|
//! | `@yearly` (or `@annually`) | 0 0 0 1 1 ? * |
//! | `@monthly`                 | 0 0 0 1 * ? * |
//! | `@weekly`                  | 0 0 0 ? * 0 * |
//! | `@daily` (or `@midnight`)  | 0 0 0 * * * * |
//! | `@hourly`                  | 0 0 * * * * * |
//!
//! Some additional information and fields description and relationships may be found [here](https://en.wikipedia.org/wiki/Cron#Cron_expression) (this is not complete or exceptional documentation).
//!
//! ### Schedule with timezone
//! If `tz` feature is enabled, it's possible to prefix cron schedule with timezone, for example:
//! - `TZ=Europe/Paris @monthly`
//! - `TZ=EET 0 12 * * *`
//!
//! ## How to use
//!
//! The single public entity of the crate is a [`Schedule`] structure, which has three basic methods:
//! - [new()](Schedule::new): constructor to parse and validate provided schedule;
//! - [upcoming()](Schedule::upcoming): returns time of the next schedule's event, starting from the provided timestamp;
//! - [iter()](Schedule::iter): returns an `Iterator` which produces a series of timestamps according to the schedule.
//!
//! ### Example with `upcoming`
//! ```rust
//! use chrono::Utc;
//! use cron_lite::{Result, Schedule};
//!
//! fn upcoming() -> Result<()> {
//!     let schedule = Schedule::new("0 0 0 * * *")?;
//!     let now = Utc::now();
//!
//!     // Get the next event's timestamp starting from now
//!     let next = schedule.upcoming(&now);
//!     assert!(next.is_some());
//!
//!     println!("next: {:?}", next.unwrap());
//!
//!
//!     Ok(())
//! }
//! ```
//!
//! ### Example with `iter`
//! ```rust
//! use chrono::Utc;
//! use cron_lite::{Result, Schedule};
//!
//! fn iterator() -> Result<()> {
//!     let schedule = Schedule::new("0 0 0 * * *")?;
//!     let now = Utc::now();
//!
//!     // Get the next 10 timestamps starting from now
//!     schedule.iter(&now).take(10).for_each(|t| println!("next: {t}"));
//!
//!     Ok(())
//! }
//! ```
//!
//! # Feature flags
//! * `serde`: adds [`Serialize`](https://docs.rs/serde/latest/serde/trait.Serialize.html) and [`Deserialize`](https://docs.rs/serde/latest/serde/trait.Deserialize.html) trait implementation for [`Schedule`].
//! * `tz`: enables support of cron [schedules with timezone](#schedule-with-timezone).

/// Primitives related to async cron events generation.
#[cfg(feature = "async")]
pub mod asyncronous;
/// Crate specific Error implementation.
pub mod error;
mod pattern;
/// Cron schedule pattern parser and upcoming event generator.
pub mod schedule;
mod series;
mod utils;

// Re-export of public entities.
#[cfg(feature = "async")]
pub use asyncronous::CronEvent;
#[cfg(feature = "async")]
pub use asyncronous::CronWaiter;

pub use error::CronError;
pub use schedule::Schedule;

/// Convenient alias for `Result`.
pub type Result<T, E = CronError> = std::result::Result<T, E>;
