use chrono::Utc;
use cron_lite::{Result, Schedule};
use rstest::rstest;
use std::time::Duration;

#[rstest]
#[timeout(Duration::from_secs(1))]
fn iter() -> Result<()> {
    let schedule = Schedule::new("0 0 0 * * *")?;
    let now = Utc::now();

    // Get the next 10 timestamps starting from now
    schedule.iter(&now).take(20000).for_each(|t| println!("next: {t}"));

    Ok(())
}

#[rstest]
#[timeout(Duration::from_secs(1))]
fn into_iter() -> Result<()> {
    let schedule = Schedule::new("0 0 0 * * *")?;
    let now = Utc::now();

    // Get the next 10 timestamps starting from now
    schedule.into_iter(&now).take(20000).for_each(|t| println!("next: {t}"));

    Ok(())
}
