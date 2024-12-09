//! Lightweight cron expression parser and time series generator.
#![deny(unsafe_code, warnings, missing_docs)]

/// Crate specific Errors implementation.
pub mod error;
mod pattern;
/// Cron schedule pattern parser and upcoming event generator.
pub mod schedule;
mod series;
mod utils;

/// Re-export of public entities.
pub use error::CronError;
pub use schedule::Schedule;

/// Convenient alias for `Result`.
pub type Result<T, E = CronError> = std::result::Result<T, E>;
