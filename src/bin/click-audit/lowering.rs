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
    /// The failures in full, or the first of them, with reproduce commands.
    pub(super) failures: String,
    /// Containers that did not verify as their expectation says. The gate
    /// and the slow-tests job own those verdicts; the audit lists them so a
    /// count it reports can be read beside them.
    pub(super) unexpected_outcomes: Vec<String>,
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
    claims: &[String],
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
    let unexpected = cli::run_parallel(&targets, workers, |target| verify_target(target));
    let checked = audit.checked();
    audit
        .record_to(None)
        .map_err(|error| format!("failed to close `{}`: {error}", records.display()))?;
    let mut lines = fs::read_to_string(records).unwrap_or_default();
    if !claims.is_empty() && audit == LoweringAudit::RaiseLower {
        lines = lines
            .lines()
            .filter(|line| {
                line.split('\t')
                    .nth(3)
                    .is_some_and(|claim| claims.iter().any(|selected| selected == claim))
            })
            .map(|line| format!("{line}\n"))
            .collect();
    }
    let counts = match audit {
        LoweringAudit::RaiseLower => raise_lower_counts(&lines),
        LoweringAudit::FactStability => fact_stability_counts(&lines, checked),
    };
    let failures = match audit {
        LoweringAudit::RaiseLower => raise_lower_failures(&lines),
        LoweringAudit::FactStability => fact_stability_failures(&lines),
    };
    write_failures(audit, &failures, records)?;
    let unexpected_outcomes = unexpected
        .into_iter()
        .map(|(index, message)| format!("{}: {message}", targets[index].display()))
        .collect::<Vec<_>>();
    write_counts(audit, &counts, unexpected_outcomes.len(), records)?;
    let changed_path = records.with_extension("unexpected.tsv");
    fs::write(
        &changed_path,
        unexpected_outcomes
            .iter()
            .map(|line| format!("{line}\n"))
            .collect::<String>(),
    )
    .map_err(|error| format!("failed to write `{}`: {error}", changed_path.display()))?;
    Ok(LoweringReport {
        headline: headline(audit, &counts, records),
        failures: render_failures(audit, &failures, records),
        unexpected_outcomes,
    })
}

/// `path` relative to the current directory when it lies under it.
fn relative_path(path: &Path) -> PathBuf {
    std::env::current_dir()
        .ok()
        .and_then(|directory| path.strip_prefix(directory).ok().map(Path::to_path_buf))
        .unwrap_or_else(|| path.to_path_buf())
}

/// How many failures a run prints in full; the rest are in the failures file.
const PRINTED_FAILURES: usize = 10;

/// One distinct failing fact (raise-lower) or lowering (fact stability), as
/// a reader picks it to fix.
struct Failure {
    outcome: String,
    container: String,
    /// The raise-lower claim, or the fact-stability lowering site.
    place: String,
    original: String,
    /// The raised Surface form, or the fact-free lowering.
    other: String,
    /// What the raised form lowered to, for `differs`.
    lowered: String,
}

impl Failure {
    /// The command that checks just this failure's container (and claim).
    fn reproduce(&self, audit: LoweringAudit) -> String {
        let container = cli::shell_quote(&self.container);
        match audit {
            LoweringAudit::RaiseLower => format!(
                "click audit raise-lower --claim {} {container}",
                cli::shell_quote(&self.place)
            ),
            LoweringAudit::FactStability => format!("click audit fact-stability {container}"),
        }
    }
}

/// Each distinct failing raise-lower fact, in record order.
fn raise_lower_failures(lines: &str) -> Vec<Failure> {
    let mut seen = BTreeSet::new();
    let mut failures = Vec::new();
    for line in lines.lines() {
        let fields = line.split('\t').collect::<Vec<_>>();
        let [outcome, _, _, claim, _, _, original, raised, lowered, ..] = fields[..] else {
            continue;
        };
        let container = fields.get(9).copied().unwrap_or("");
        if FAILING_ROUND_TRIPS.contains(&outcome) && seen.insert((container, claim, original)) {
            failures.push(Failure {
                outcome: outcome.to_string(),
                container: container.to_string(),
                place: claim.to_string(),
                original: original.to_string(),
                other: raised.to_string(),
                lowered: lowered.to_string(),
            });
        }
    }
    failures
}

/// Each distinct fact-dependent lowering, in record order.
fn fact_stability_failures(lines: &str) -> Vec<Failure> {
    let mut seen = BTreeSet::new();
    let mut failures = Vec::new();
    for line in lines.lines() {
        let fields = line.split('\t').collect::<Vec<_>>();
        let [outcome, site, with_facts, fact_free, container, ..] = fields[..] else {
            continue;
        };
        if (outcome == "differs" || outcome.starts_with("paths:"))
            && seen.insert((container, site, with_facts))
        {
            failures.push(Failure {
                outcome: outcome.to_string(),
                container: container.to_string(),
                place: site.to_string(),
                original: with_facts.to_string(),
                other: fact_free.to_string(),
                lowered: String::new(),
            });
        }
    }
    failures
}

/// `<records>.failures.tsv`: outcome, container, claim or site, original,
/// raised form or fact-free lowering, lowered form, and the command that
/// reproduces it, one failure per line.
fn write_failures(
    audit: LoweringAudit,
    failures: &[Failure],
    records: &Path,
) -> Result<(), String> {
    let path = records.with_extension("failures.tsv");
    let text = failures
        .iter()
        .map(|failure| {
            format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                failure.outcome,
                failure.container,
                failure.place,
                failure.original,
                failure.other,
                failure.lowered,
                failure.reproduce(audit)
            )
        })
        .collect::<String>();
    fs::write(&path, text).map_err(|error| format!("failed to write `{}`: {error}", path.display()))
}

/// The failures a run prints: each in full when there are few, otherwise
/// the first few and where the rest are.
fn render_failures(audit: LoweringAudit, failures: &[Failure], records: &Path) -> String {
    let (original, other) = match audit {
        LoweringAudit::RaiseLower => ("fact", "raised"),
        LoweringAudit::FactStability => ("with facts", "without facts"),
    };
    let mut text = String::new();
    for (index, failure) in failures.iter().take(PRINTED_FAILURES).enumerate() {
        text.push_str(&format!(
            "  {}. {} in `{}` ({})\n       {original}: {}\n",
            index + 1,
            failure.outcome,
            failure.place,
            failure.container,
            failure.original,
        ));
        if !failure.other.is_empty() {
            text.push_str(&format!("       {other}: {}\n", failure.other));
        }
        if !failure.lowered.is_empty() {
            text.push_str(&format!("       lowered: {}\n", failure.lowered));
        }
        text.push_str(&format!("       reproduce: {}\n", failure.reproduce(audit)));
    }
    if failures.len() > PRINTED_FAILURES {
        text.push_str(&format!(
            "  ... and {} more; each with its reproduce command in {}\n",
            failures.len() - PRINTED_FAILURES,
            records.with_extension("failures.tsv").display()
        ));
    }
    text
}

/// What one lowering audit counted.
struct Counts {
    failing: usize,
    checked: usize,
    /// Raise-lower facts at no fixed state; fact-stability `refused`
    /// lowerings. Both are tracked, not failing.
    tracked: usize,
    /// Each outcome's count of distinct items.
    outcomes: BTreeMap<String, usize>,
}

/// `<records>.counts.tsv`, `outcome<TAB>count`: the headline's numbers,
/// `failing`, `checked`, `tracked` and `unexpected` (containers that did not
/// verify as their expectation says), then each outcome's count, for the
/// nightly report.
fn write_counts(
    audit: LoweringAudit,
    counts: &Counts,
    unexpected: usize,
    records: &Path,
) -> Result<(), String> {
    let path = records.with_extension("counts.tsv");
    let mut text = format!(
        "failing\t{}\nchecked\t{}\ntracked\t{}\nunexpected\t{unexpected}\n",
        counts.failing, counts.checked, counts.tracked
    );
    for (outcome, count) in &counts.outcomes {
        text.push_str(&format!("{outcome}\t{count}\n"));
    }
    fs::write(&path, text).map_err(|error| {
        format!(
            "failed to write the {} counts `{}`: {error}",
            name(audit),
            path.display()
        )
    })
}

fn headline(audit: LoweringAudit, counts: &Counts, records: &Path) -> String {
    match audit {
        LoweringAudit::RaiseLower => format!(
            "raise-lower audit: {} failing of {} facts checked ({}); {} not checkable (no fixed state); {}; records: {}",
            counts.failing,
            counts.checked,
            percent(counts.failing, counts.checked),
            counts.tracked,
            breakdown(&counts.outcomes),
            records.display()
        ),
        LoweringAudit::FactStability => format!(
            "fact-stability audit: {} failing of {} lowerings checked ({}); {} refused without facts (tracked); records: {}",
            counts.failing,
            counts.checked,
            percent(counts.failing, counts.checked),
            counts.tracked,
            records.display()
        ),
    }
}

/// Verifies one container on a named verifier thread, so each record names
/// the container it came from. An outcome its expectation does not predict
/// is returned as an error.
fn verify_target(target: &PathBuf) -> Result<(), String> {
    // The thread's name names the container in each record, as the path a
    // reproduce command takes from where the audit ran.
    let thread = relative_path(target).display().to_string();
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

/// The distinct facts and goals the audit checked: a fact is counted once
/// per container, claim and rendering, however many steps restate it.
fn raise_lower_counts(lines: &str) -> Counts {
    let mut checked = BTreeSet::new();
    let mut failing = BTreeSet::new();
    let mut unchecked = BTreeSet::new();
    let mut by_outcome = BTreeMap::<&str, BTreeSet<(&str, &str, &str)>>::new();
    for line in lines.lines() {
        let fields = line.split('\t').collect::<Vec<_>>();
        let [outcome, _, _, claim, _, _, original, ..] = fields[..] else {
            continue;
        };
        let container = fields.get(9).copied().unwrap_or("");
        let key = (container, claim, original);
        by_outcome.entry(outcome).or_default().insert(key);
        if outcome == "no-state" {
            unchecked.insert(key);
            continue;
        }
        checked.insert(key);
        if FAILING_ROUND_TRIPS.contains(&outcome) {
            failing.insert(key);
        }
    }
    Counts {
        failing: failing.len(),
        checked: checked.len(),
        tracked: unchecked.difference(&checked).count(),
        outcomes: by_outcome
            .into_iter()
            .map(|(outcome, keys)| (outcome.to_string(), keys.len()))
            .collect(),
    }
}

/// A lowering fails when facts changed its term or chose among its paths.
fn fact_stability_counts(lines: &str, checked: usize) -> Counts {
    let mut outcomes = BTreeMap::<String, usize>::new();
    for line in lines.lines() {
        let outcome = line.split('\t').next().unwrap_or("");
        let outcome = if outcome.starts_with("paths:") {
            "paths"
        } else {
            outcome
        };
        *outcomes.entry(outcome.to_string()).or_default() += 1;
    }
    let count = |outcome: &str| outcomes.get(outcome).copied().unwrap_or(0);
    Counts {
        failing: count("differs") + count("paths"),
        checked,
        tracked: count("refused"),
        outcomes,
    }
}

fn percent(part: usize, whole: usize) -> String {
    if whole == 0 {
        return "0%".to_string();
    }
    format!("{:.1}%", 100.0 * part as f64 / whole as f64)
}

fn breakdown(outcomes: &BTreeMap<String, usize>) -> String {
    FAILING_ROUND_TRIPS
        .iter()
        .map(|outcome| format!("{} {outcome}", outcomes.get(*outcome).copied().unwrap_or(0)))
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
        let headline = headline(
            LoweringAudit::RaiseLower,
            &raise_lower_counts(&lines),
            Path::new("r.tsv"),
        );
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
        let headline = headline(
            LoweringAudit::FactStability,
            &fact_stability_counts(lines, 40),
            Path::new("f.tsv"),
        );
        assert!(
            headline.starts_with(
                "fact-stability audit: 2 failing of 40 lowerings checked (5.0%); 1 refused"
            ),
            "{headline}"
        );
    }
}
