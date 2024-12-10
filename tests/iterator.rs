use chrono::Utc;
use cron_lite::{Result, Schedule};

#[test]
fn iterator() -> Result<()> {
    let schedule = Schedule::new("0 0 0 * * *")?;
    let now = Utc::now();

    // Get the next 10 timestamps starting from now
    schedule.iter(&now).take(10).for_each(|t| println!("next: {t}"));

    Ok(())
}
