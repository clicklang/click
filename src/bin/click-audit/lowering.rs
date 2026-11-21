//! `click audit raise-lower` and `click audit fact-stability`: the lowering
//! audits (`docs/internals/raise-lower-principle.md`). Each verifies every
//! proof container the expansion audit walks with its records switched on,
//! then reports one headline: how many of the items it checked fail.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use click::cli::{self, MdTestExpectation, VerificationInput, source_refs};
use click::instrumentation::LoweringAudit;

use super::{AuditSource, audit_targets, load_audit_source};

/// The outcome of one lowering audit run.
pub(super) struct LoweringReport {
    pub(super) headline: String,
    /// Containers whose verification outcome under the audit disagreed with
    /// their expectation: an audit must not change a proof.
    pub(super) changed_outcomes: Vec<String>,
}

pub(super) fn name(audit: LoweringAudit) -> &'static str {
    match audit {
        LoweringAudit::RaiseLower => "raise-lower",
        LoweringAudit::FactStability => "fact-stability",
    }
}

/// Runs `audit` over every proof container under `path`, recording to
/// `records`.
pub(super) fn run(
    audit: LoweringAudit,
    path: &Path,
    records: &Path,
) -> Result<LoweringReport, String> {
    let targets = audit_targets(path)?;
    if let Some(parent) = records.parent() {
        fs::create_dir_all(parent)
            .map_err(|error| format!("failed to create `{}`: {error}", parent.display()))?;
    }
    if records.exists() {
        fs::remove_file(records)
            .map_err(|error| format!("failed to replace `{}`: {error}", records.display()))?;
    }
    audit
        .record_to(Some(records))
        .map_err(|error| format!("failed to open `{}`: {error}", records.display()))?;
    println!(
        "{} audit: verifying {} proof containers",
        name(audit),
        targets.len()
    );
    let workers = std::thread::available_parallelism().map_or(1, usize::from);
    let changed = cli::run_parallel(&targets, workers, |target| verify_target(target));
    let checked = audit.checked();
    audit
        .record_to(None)
        .map_err(|error| format!("failed to close `{}`: {error}", records.display()))?;
    let lines = fs::read_to_string(records).unwrap_or_default();
    let headline = match audit {
        LoweringAudit::RaiseLower => raise_lower_headline(&lines, records),
        LoweringAudit::FactStability => fact_stability_headline(&lines, checked, records),
    };
    Ok(LoweringReport {
        headline,
        changed_outcomes: changed
            .into_iter()
            .map(|(index, message)| format!("{}: {message}", targets[index].display()))
            .collect(),
    })
}

/// Verifies one container on a named verifier thread, so each record names
/// the container it came from. An outcome its expectation does not predict
/// is returned as an error.
fn verify_target(target: &PathBuf) -> Result<(), String> {
    let thread = target.file_name().map_or_else(
        || target.display().to_string(),
        |name| name.to_string_lossy().into_owned(),
    );
    let path = target.clone();
    let outcome = std::thread::Builder::new()
        .name(thread)
        .stack_size(64 * 1024 * 1024)
        .spawn(
            move || -> Result<(Result<(), String>, Option<MdTestExpectation>), String> {
                let source = load_audit_source(&path)?;
                let expectation = source
                    .mdtest
                    .as_ref()
                    .and_then(|mdtest| mdtest.expectation.clone());
                Ok((verify_source(&source), expectation))
            },
        )
        .map_err(|error| format!("failed to start a verifier thread: {error}"))?
        .join()
        .map_err(|_| "the verifier thread panicked".to_string())??;
    match outcome {
        (Ok(()), Some(MdTestExpectation::FailContains(expected))) => Err(format!(
            "verified, but its expectation is a failure containing `{expected}`"
        )),
        (Err(error), None | Some(MdTestExpectation::Pass)) => Err(format!(
            "failed to verify: {}",
            error.lines().next().unwrap_or_default()
        )),
        _ => Ok(()),
    }
}

/// Verifies a whole proof container, as `click verify` and the mdtest
/// harness do.
fn verify_source(source: &AuditSource) -> Result<(), String> {
    use click::surface::{verify_c_sources, verify_project_with_summary};
    match (&source.project, &source.inputs) {
        (Some(project), inputs) => {
            let (_, verification) = verify_project_with_summary(project, &inputs.program_inputs())
                .map_err(|error| error.report())?;
            verification.map(|_| ()).map_err(|error| error.report())
        }
        (None, VerificationInput::Bundle(sources)) => {
            verify_c_sources(&source.click_source, &source_refs(sources))
                .map(|_| ())
                .map_err(|error| error.report())
        }
        (None, _) => Err("a prepared program needs a Click project".to_string()),
    }
}

/// The raise-lower outcomes that break the principle: no raised form, a
/// raised form that does not lower, or one that lowers to another term.
const FAILING_ROUND_TRIPS: [&str; 4] = ["unraised", "unlowered", "differs", "polarity"];

/// One headline over the distinct facts and goals the audit checked: a fact
/// is counted once per container and claim, however many steps restate it.
fn raise_lower_headline(lines: &str, records: &Path) -> String {
    let mut checked = BTreeSet::new();
    let mut failing = BTreeSet::new();
    let mut unchecked = BTreeSet::new();
    let mut outcomes = BTreeMap::<&str, usize>::new();
    for line in lines.lines() {
        let fields = line.split('\t').collect::<Vec<_>>();
        let [outcome, _, _, claim, _, _, original, ..] = fields[..] else {
            continue;
        };
        let container = fields.get(9).copied().unwrap_or("");
        let key = (container, claim, original);
        if outcome == "no-state" {
            unchecked.insert(key);
            continue;
        }
        checked.insert(key);
        if FAILING_ROUND_TRIPS.contains(&outcome) && failing.insert(key) {
            *outcomes.entry(outcome).or_default() += 1;
        }
    }
    format!(
        "raise-lower audit: {} failing of {} facts checked ({}); {} not checkable (no fixed state); {}; records: {}",
        failing.len(),
        checked.len(),
        percent(failing.len(), checked.len()),
        unchecked.difference(&checked).count(),
        breakdown(&outcomes),
        records.display()
    )
}

/// One headline over the lowerings the audit checked: a lowering fails when
/// facts changed its term or chose among its paths.
fn fact_stability_headline(lines: &str, checked: usize, records: &Path) -> String {
    let mut outcomes = BTreeMap::<&str, usize>::new();
    for line in lines.lines() {
        let outcome = line.split('\t').next().unwrap_or("");
        let outcome = if outcome.starts_with("paths:") {
            "paths"
        } else {
            outcome
        };
        *outcomes.entry(outcome).or_default() += 1;
    }
    let failing =
        outcomes.get("differs").copied().unwrap_or(0) + outcomes.get("paths").copied().unwrap_or(0);
    format!(
        "fact-stability audit: {failing} failing of {checked} lowerings checked ({}); {} refused without facts (tracked); records: {}",
        percent(failing, checked),
        outcomes.get("refused").copied().unwrap_or(0),
        records.display()
    )
}

fn percent(part: usize, whole: usize) -> String {
    if whole == 0 {
        return "0%".to_string();
    }
    format!("{:.1}%", 100.0 * part as f64 / whole as f64)
}

fn breakdown(outcomes: &BTreeMap<&str, usize>) -> String {
    FAILING_ROUND_TRIPS
        .iter()
        .map(|outcome| format!("{} {outcome}", outcomes.get(outcome).copied().unwrap_or(0)))
        .collect::<Vec<_>>()
        .join(", ")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn record(outcome: &str, claim: &str, original: &str, container: &str) -> String {
        format!("{outcome}\tfact\tkind\t{claim}\tstep\twritten\t{original}\t\t\t{container}\n")
    }

    /// A fact counts once per container, claim and rendering; a fact at no
    /// fixed state counts only as not checkable.
    #[test]
    fn the_raise_lower_headline_counts_distinct_facts() {
        let lines = [
            record("same", "f.contract", "x == 1", "a.md"),
            record("same", "f.contract", "x == 1", "a.md"),
            record("unraised", "f.contract", "y == 2", "a.md"),
            record("unraised", "f.contract", "y == 2", "a.md"),
            record("differs", "f.contract", "y == 2", "b.md"),
            record("no-state", "g.contract", "z == 3", "a.md"),
        ]
        .concat();
        let headline = raise_lower_headline(&lines, Path::new("r.tsv"));
        assert!(
            headline.starts_with(
                "raise-lower audit: 2 failing of 3 facts checked (66.7%); 1 not checkable"
            ),
            "{headline}"
        );
        assert!(
            headline.contains("1 unraised, 0 unlowered, 1 differs, 0 polarity"),
            "{headline}"
        );
    }

    /// A fact-dependent term or path choice fails; a refusal is tracked.
    #[test]
    fn the_fact_stability_headline_counts_failing_lowerings() {
        let lines = "differs\ts\ta\tb\tt\npaths:2\ts\ta\t\tt\nrefused\ts\ta\t\tt\n";
        let headline = fact_stability_headline(lines, 40, Path::new("f.tsv"));
        assert!(
            headline.starts_with(
                "fact-stability audit: 2 failing of 40 lowerings checked (5.0%); 1 refused"
            ),
            "{headline}"
        );
    }
}
