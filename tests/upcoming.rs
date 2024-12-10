use chrono::Utc;
use cron_light::{Result, Schedule};

#[test]
fn upcoming() -> Result<()> {
    let schedule = Schedule::new("0 0 0 * * *")?;
    let now = Utc::now();

    // Get the next event's timestamp starting from now
    let next = schedule.upcoming(&now).unwrap();
    println!("next: {next}");

    Ok(())
}
