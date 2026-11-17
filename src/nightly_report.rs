//! Per-result records for the nightly report.
//!
//! The nightly workflow sets `CLICK_NIGHTLY_REPORT_DIR`. The mdtest and
//! example-project harnesses and `click audit` then append one JSON line per
//! fixture, project, or failed audit site to `<dir>/<source>.jsonl`, and
//! `scripts/nightly-report.py` turns those lines, with nextest's JUnit output,
//! into the report published on the `nightly-reports` branch
//! (`docs/internals/testing.md`, "Nightly report"). Without the variable,
//! recording does nothing.

use std::io::Write;
use std::sync::Mutex;

/// The environment variable naming the report directory.
pub const REPORT_DIR: &str = "CLICK_NIGHTLY_REPORT_DIR";

/// One result: which `kind` of check (`mdtest`, `example`, `audit`), its
/// `name` as the report's reproduction command selects it, whether it passed,
/// how long it ran, and its diagnostics when it failed.
pub struct NightlyResult<'a> {
    pub kind: &'a str,
    pub name: &'a str,
    pub passed: bool,
    pub seconds: f64,
    pub message: Option<&'a str>,
}

static WRITE: Mutex<()> = Mutex::new(());

/// Appends `result` to `<CLICK_NIGHTLY_REPORT_DIR>/<source>.jsonl`. A record
/// that cannot be written is reported on stderr and otherwise ignored: the
/// report is a summary of the run, never part of its verdict.
pub fn record(source: &str, result: &NightlyResult<'_>) {
    let Some(directory) = std::env::var_os(REPORT_DIR) else {
        return;
    };
    let line = serde_json::json!({
        "kind": result.kind,
        "name": result.name,
        "passed": result.passed,
        "seconds": (result.seconds * 100.0).round() / 100.0,
        "message": result.message,
    })
    .to_string();
    let path = std::path::Path::new(&directory).join(format!("{source}.jsonl"));
    let _guard = WRITE
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let written = std::fs::create_dir_all(&directory).and_then(|()| {
        let mut file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)?;
        file.write_all(format!("{line}\n").as_bytes())
    });
    if let Err(error) = written {
        eprintln!(
            "warning: could not record a nightly result in `{}`: {error}",
            path.display()
        );
    }
}
