use chrono::Utc;
use cron_lite::{Result, Schedule};
use rstest::rstest;
use std::time::Duration;

#[rstest]
#[timeout(Duration::from_secs(1))]
fn upcoming() -> Result<()> {
    let schedule = Schedule::new("0 0 0 * * *")?;
    let now = Utc::now();

    // Get the next event's timestamp starting from now
    let next = schedule.upcoming(&now).unwrap();
    println!("next: {next}");

    Ok(())
}
