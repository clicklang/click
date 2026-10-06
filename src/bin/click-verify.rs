use std::cell::RefCell;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::env;
use std::fs;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use click::cli::{
    CInput, LoadedTarget, RunLimits, containing_directory, load_sidecar_inputs, load_target_inputs,
    lone_sidecar_project_root, looks_like_mdtest, looks_like_source_location, parse_duration,
    parse_source_location, parse_work_limit, select_sidecars, source_refs, with_run_limits,
};
use click::instrumentation::VerificationPhase;
use click::languages::c::source as c_source;
use click::languages::c::target::CTarget;
#[cfg(test)]
use click::surface::verify_c0_sources;
use click::surface::{
    ClickError, ClickErrorKind, ClickProject, VerifiedCTheorem, accepted_proof_trace,
    c0_incremental_selection, c0_prepared_project_selected_proof_names,
    c0_prepared_project_summary, c0_prepared_project_tactic_source_position,
    c0_project_selected_proof_names, c0_project_summary, c0_project_tactic_source_position,
    nested_tactic_source_position, program_prepared_project_summary,
    program_prepared_project_tactic_source_position, selected_c_target,
    tactic_arm_containing_position, tactic_have_body_contains_position,
    tactic_line_has_multiple_starts, tactic_source_at_position, tactic_starts_on_line,
    verify_c0_prepared_project, verify_c0_prepared_project_at,
    verify_c0_prepared_project_functions, verify_c0_prepared_project_theorem, verify_c0_project,
    verify_c0_project_at, verify_c0_project_functions, verify_c0_project_theorem,
    verify_program_prepared_project, verify_program_prepared_project_at, verifying_source_paths,
    with_proof_trace,
};

const USAGE: &str = "\
usage: click verify [--work-limit <UNITS>] [--time-limit <DURATION>] <sidecar.click|mdtest.md>[:<line>:<column>]
       click verify --trace-proof <PROOF> [--trace-to <LINE[:COLUMN]>] <sidecar.click|mdtest.md>
       click verify [--work-limit <UNITS>] [--time-limit <DURATION>] <project-directory|examples-directory>
       click verify --changed-since <REVISION> [--explain] <sidecar.click|directory>

Verifies proofs owned by the selected sidecar, or, when a one-based
:LINE:COLUMN suffix is supplied, only the proof unit containing that source
location. Imported declarations and unselected C function contracts are
assumptions; their proof bodies are not recursively selected.

An mdtest is verified from its embedded ```c or ```cpp and ```click blocks,
prepared exactly as the mdtests gate prepares them. Locations are lines of
the markdown file. Verify reports the proof outcome itself; it does not
consult the ```expect block, so an expected-failure mdtest exits nonzero.

Given a directory, verifies every sidecar in it: either the project directory
itself when it holds sidecars, or each immediate subdirectory that does. This
is the command to run after applying an expansion emitted by `click expand`.

Verdicts are deterministic: every tactic has a per-class work budget, and each
selected sidecar, mdtest, or proof unit has a whole-run budget of
`--work-limit` units (default 50000000). The same source spends the same
units on any machine under any load. `--time-limit` (default 10m) is only a
wall-clock crash-containment bound for a hung or CPU-starved run; a run it
stops says so, and that is not a verdict about the proof.

`--trace-proof PROOF` verifies one C function or one pure theorem of the
sidecar, by name, and shows checked fact and resource changes on the path to
the failing tactic, or an accepted path when the proof succeeds. `--trace-to`
selects a written tactic by source line (and column when the line has several
tactics) within the selected proof.
Ordinary proof errors suggest this command with the failing proof filled in.

`--allow-sorry` enables the dev-only `sorry` proof hole: a proof unit whose
body is exactly `sorry();` is admitted without checking. This is purely a
debugging tool for reducing a failure to its minimal shape; it is never
sound. Admissions are reported loudly, never recorded in incremental
baselines or caches, and `click audit`, `click expand`, and `scripts/check.sh`
never enable the flag, so sorry can never sneak into a passing gate.";

const INCREMENTAL_CACHE_SCHEMA: &str = "click-verified-v1";
type LoadedSidecar = (String, Vec<(String, String)>);

#[derive(Clone, Debug, Eq, PartialEq)]
struct Arguments {
    target: String,
    limits: RunLimits,
    changed_since: Option<String>,
    explain: bool,
    allow_sorry: bool,
    trace_proof: Option<String>,
    trace_to: Option<TraceTo>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TraceTo {
    line: usize,
    column: Option<usize>,
}

fn main() {
    if let Err(message) = entry() {
        if message.starts_with("proof error:")
            || message.starts_with("proof error in `")
            || message.starts_with("syntax error:")
            || message.starts_with("type error:")
            || message.starts_with("internal error:")
        {
            eprintln!("{message}");
        } else {
            eprintln!("click-verify: {message}");
        }
        std::process::exit(1);
    }
}

fn entry() -> Result<(), String> {
    entry_with(env::args().skip(1))
}

pub(crate) fn entry_with(arguments: impl IntoIterator<Item = String>) -> Result<(), String> {
    let raw = arguments.into_iter().collect::<Vec<_>>();
    if matches!(raw.as_slice(), [argument] if argument == "--help" || argument == "-h") {
        println!("{USAGE}");
        return Ok(());
    }
    let arguments = parse_arguments(raw)?;
    if arguments.trace_proof.is_some()
        && (arguments.changed_since.is_some()
            || arguments.explain
            || arguments.allow_sorry
            || looks_like_source_location(&arguments.target)
            || Path::new(&arguments.target).is_dir())
    {
        return Err(
            "`--trace-proof` requires one sidecar file without a location, incremental options, or `--allow-sorry`"
                .to_string(),
        );
    }
    if arguments.trace_to.is_some() && arguments.trace_proof.is_none() {
        return Err("`--trace-to` requires `--trace-proof`".to_string());
    }
    if arguments.allow_sorry {
        // An admission records what an ordinary run did not check, so it
        // cannot say which proofs a baseline still has to check, and it must
        // never be recorded as verified.
        if arguments.changed_since.is_some() {
            return Err("`--allow-sorry` cannot be combined with `--changed-since`".to_string());
        }
        let arguments = Arguments {
            allow_sorry: false,
            ..arguments
        };
        return click::surface::with_allow_sorry(|| run(arguments));
    }
    run(arguments)
}

fn run(arguments: Arguments) -> Result<(), String> {
    if let Some(revision) = &arguments.changed_since {
        let path = Path::new(&arguments.target);
        return verify_changed(path, revision, arguments.limits, arguments.explain);
    }
    if arguments.explain {
        return Err("`--explain` requires `--changed-since`".to_string());
    }
    if looks_like_source_location(&arguments.target) {
        let (click_path, line, column) = parse_source_location(&arguments.target)?;
        return verify_location(&click_path, line, column, arguments.limits);
    }
    let path = Path::new(&arguments.target);
    if path.is_dir() {
        verify_directory(path, arguments.limits)
    } else {
        let project_root = lone_sidecar_project_root(path)?;
        verify_file(
            path,
            arguments.limits,
            Some(&project_root),
            arguments.trace_proof.as_deref(),
            arguments.trace_to.as_ref(),
        )
    }
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<Arguments, String> {
    let mut target = None;
    let mut limits = RunLimits::verify();
    let mut changed_since = None;
    let mut explain = false;
    let mut allow_sorry = false;
    let mut trace_proof = None;
    let mut trace_to = None;
    let mut parse_options = true;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        if parse_options && argument == "--" {
            parse_options = false;
        } else if parse_options && argument == "--time-limit" {
            let value = arguments
                .next()
                .ok_or_else(|| format!("missing duration after `--time-limit`\n{USAGE}"))?;
            limits.time = parse_duration(&value)?;
        } else if parse_options && argument == "--work-limit" {
            let value = arguments
                .next()
                .ok_or_else(|| format!("missing unit count after `--work-limit`\n{USAGE}"))?;
            limits.work = parse_work_limit(&value)?;
        } else if parse_options && argument == "--changed-since" {
            if changed_since.is_some() {
                return Err("`--changed-since` may only be supplied once".to_string());
            }
            changed_since = Some(
                arguments
                    .next()
                    .ok_or_else(|| format!("missing revision after `--changed-since`\n{USAGE}"))?,
            );
        } else if parse_options && argument == "--explain" {
            explain = true;
        } else if parse_options && argument == "--allow-sorry" {
            allow_sorry = true;
        } else if parse_options && argument == "--trace-proof" {
            if trace_proof.is_some() {
                return Err("`--trace-proof` may only be supplied once".to_string());
            }
            trace_proof = Some(
                arguments
                    .next()
                    .ok_or_else(|| format!("missing proof name after `--trace-proof`\n{USAGE}"))?,
            );
        } else if parse_options && argument == "--trace-to" {
            if trace_to.is_some() {
                return Err("`--trace-to` may only be supplied once".to_string());
            }
            let value = arguments
                .next()
                .ok_or_else(|| format!("missing source location after `--trace-to`\n{USAGE}"))?;
            let (line, column) = value
                .split_once(':')
                .map_or((value.as_str(), None), |(line, column)| {
                    (line, Some(column))
                });
            let line = line
                .parse::<usize>()
                .ok()
                .filter(|line| *line > 0)
                .ok_or_else(|| "`--trace-to` needs a positive LINE[:COLUMN]".to_string())?;
            let column = column
                .map(|column| {
                    column
                        .parse::<usize>()
                        .ok()
                        .filter(|column| *column > 0)
                        .ok_or_else(|| "`--trace-to` needs a positive LINE[:COLUMN]".to_string())
                })
                .transpose()?;
            trace_to = Some(TraceTo { line, column });
        } else if parse_options && argument.starts_with('-') {
            return Err(format!("unknown option `{argument}`\n{USAGE}"));
        } else if target.replace(argument).is_some() {
            return Err(USAGE.to_string());
        }
    }
    Ok(Arguments {
        target: target.ok_or_else(|| USAGE.to_string())?,
        limits,
        changed_since,
        explain,
        allow_sorry,
        trace_proof,
        trace_to,
    })
}

fn resolve_trace_target(
    source: &str,
    line_offset: usize,
    target: &TraceTo,
) -> Result<click::surface::SourcePosition, String> {
    let line = target
        .line
        .checked_sub(line_offset)
        .filter(|line| *line > 0)
        .ok_or_else(|| format!("tactic@{} is outside the Click source", target.line))?;
    let starts = tactic_starts_on_line(source, line).map_err(click_message)?;
    let selected = match target.column {
        Some(column) => starts
            .into_iter()
            .find(|position| position.column == column)
            .ok_or_else(|| {
                format!(
                    "no written tactic starts at tactic@{}:{column}",
                    target.line
                )
            })?,
        None => match starts.as_slice() {
            [position] => position.clone(),
            [] => {
                return Err(format!(
                    "no written tactic starts at tactic@{}",
                    target.line
                ));
            }
            _ => {
                let outer = starts
                    .iter()
                    .filter(|position| {
                        !tactic_line_has_multiple_starts(source, position).unwrap_or(true)
                    })
                    .collect::<Vec<_>>();
                match outer.as_slice() {
                    [position] => (*position).clone(),
                    _ => {
                        return Err(format!(
                            "several tactics start on line {}; use --trace-to LINE:COLUMN",
                            target.line
                        ));
                    }
                }
            }
        },
    };
    Ok(selected)
}

/// Verifies every sidecar under a project or examples directory, reporting
/// each one as it passes so a long run shows progress.
fn verify_directory(path: &Path, limits: RunLimits) -> Result<(), String> {
    let selection = select_sidecars(path)?;
    let sidecars = selection.sidecars().collect::<Vec<_>>();
    let projects = &selection.projects;
    let project_root = selection.project_root.as_path();
    for sidecar in &sidecars {
        verify_file(sidecar, limits, Some(project_root), None, None)?;
        println!("verified {}", display_path(sidecar, path));
    }
    println!(
        "verified {} sidecar{} in {} project{}",
        sidecars.len(),
        plural(sidecars.len()),
        projects.len(),
        plural(projects.len())
    );
    Ok(())
}

fn verify_changed(
    path: &Path,
    revision: &str,
    limits: RunLimits,
    explain_only: bool,
) -> Result<(), String> {
    if looks_like_mdtest(path) {
        return Err(format!(
            "`--changed-since` selects sidecars from a git baseline and does not take an mdtest; run `click verify {}` without it",
            path.display()
        ));
    }
    let selection = select_sidecars(path)?;
    let project_root = selection.project_root.as_path();
    let mut sidecars = selection
        .sidecars()
        .map(Path::to_path_buf)
        .collect::<Vec<_>>();
    sidecars.sort();
    let repo = git_repo_root(path)?;
    let baseline_commit = git_commit_id(&repo, revision)?;

    let mut verified = 0usize;
    let mut skipped = 0usize;
    for sidecar in sidecars {
        let sidecar = fs::canonicalize(&sidecar)
            .map_err(|error| format!("failed to resolve `{}`: {error}", sidecar.display()))?;
        // Loading, selection, the dependency summary, and verification of
        // one sidecar all run inside that sidecar's limits.
        let outcome = with_run_limits("click verify", limits, || {
            verify_changed_sidecar(
                &sidecar,
                project_root,
                &repo,
                &baseline_commit,
                revision,
                explain_only,
            )
        })?;
        match outcome {
            ChangedSidecar::Explained => {}
            ChangedSidecar::Skipped => skipped += 1,
            ChangedSidecar::Verified => {
                verified += 1;
                println!("  result: verified");
            }
        }
    }
    if explain_only {
        println!("dry run: no proofs were executed");
    } else {
        println!(
            "incremental verification completed: {verified} sidecars verified, {skipped} unchanged sidecars skipped"
        );
    }
    Ok(())
}

/// What `--changed-since` did with one sidecar.
enum ChangedSidecar {
    Explained,
    Skipped,
    Verified,
}

fn verify_changed_sidecar(
    sidecar: &Path,
    project_root: &Path,
    repo: &Path,
    baseline_commit: &str,
    revision: &str,
    explain_only: bool,
) -> Result<ChangedSidecar, String> {
    let (click_source, project, inputs) = {
        let _phase = VerificationPhase::new("project loading");
        load_sidecar_inputs(sidecar, Some(project_root))?
    };
    if inputs.is_prepared() {
        return Err(
            "`--changed-since` is not supported for compiler-prepared projects".to_string(),
        );
    }
    let sources = match &inputs {
        CInput::Bundle(sources) => sources.clone(),
        CInput::Prepared(_) | CInput::PreparedProgram(_) => unreachable!(),
    };
    let refs = source_refs(&sources);
    let baseline_attested = has_full_verification_marker(
        repo,
        baseline_commit,
        sidecar,
        click::surface::selected_project_c_target(&project).map_err(click_message)?,
    )?;
    let mut full_rebuild = !baseline_attested;
    let mut reasons = if !baseline_attested {
        vec![format!(
            "baseline commit {baseline_commit} has no valid full-verification marker for this sidecar and verifier binary"
        )]
    } else {
        Vec::new()
    };
    if let Some(reason) = imported_project_rebuild_reason(&project) {
        full_rebuild = true;
        reasons = vec![reason.to_string()];
    }
    let (selected, reused) = if full_rebuild {
        (
            c0_project_selected_proof_names(&project, &refs)
                .map_err(|error| located_click_message(error, sidecar, &project, 0))?,
            Vec::new(),
        )
    } else if let Some((baseline_click, baseline_sources)) =
        load_baseline_sidecar(repo, baseline_commit, sidecar)?
    {
        let baseline_refs = source_refs(&baseline_sources);
        let selection =
            c0_incremental_selection(&click_source, &refs, &baseline_click, &baseline_refs)
                .map_err(click_message)?;
        full_rebuild = selection.full_rebuild;
        reasons = selection.reasons;
        (selection.selected_functions, selection.reused_functions)
    } else {
        full_rebuild = true;
        reasons
            .push("sidecar or one of its declared C sources is absent at the baseline".to_string());
        (
            c0_project_selected_proof_names(&project, &refs)
                .map_err(|error| located_click_message(error, sidecar, &project, 0))?,
            Vec::new(),
        )
    };

    print_incremental_selection(
        sidecar,
        revision,
        &selected,
        &reused,
        &reasons,
        full_rebuild,
    );
    if explain_only {
        return Ok(ChangedSidecar::Explained);
    }
    if !full_rebuild && selected.is_empty() {
        return Ok(ChangedSidecar::Skipped);
    }
    let summary = {
        let _phase = VerificationPhase::new("external dependency summary");
        c0_project_summary(&project, &refs)
            .map_err(|error| located_click_message(error, sidecar, &project, 0))?
    };
    let verified_theorems = if full_rebuild {
        verify_c0_project(&project, &refs)
    } else {
        verify_c0_project_functions(&project, &refs, selected.clone())
    }
    .map_err(|error| proof_error_report(&error, sidecar, false, &project, &inputs, 0, None))?;
    print_external_dependencies(&summary.external_dependencies, &verified_theorems);
    if full_rebuild
        && project.modules().len() == 1
        && project.c_profile().is_none()
        && let Err(message) = record_full_verification(
            sidecar,
            &click_source,
            &sources,
            &[baseline_commit.to_string()],
        )
    {
        eprintln!("click-verify: warning: could not record incremental baseline: {message}");
    }
    Ok(ChangedSidecar::Verified)
}

fn imported_project_rebuild_reason(project: &ClickProject) -> Option<&'static str> {
    if project.c_profile().is_some() {
        return Some(
            "the sidecar uses project C configuration; conservative full rebuild prevents reuse across configuration changes",
        );
    }
    (project.modules().len() > 1).then_some(
        "the sidecar has Click imports; conservative import-aware rebuild of the selected entry scope",
    )
}

fn click_message(error: click::surface::ClickError) -> String {
    error.concise_report()
}

/// Where the declaration a failure is about is written: the one the failure
/// records, or else the last name its message quotes that the source
/// declares. A check that fails outside the per-declaration pass still names
/// what it refused (``resource `cell` has fields``, ``in theorem `t` ``), and
/// the declaration it names is the source to show.
fn failure_declaration_position(
    error: &ClickError,
    report: &str,
    source: &str,
) -> Option<click::surface::SourcePosition> {
    let recorded = || {
        error.proof_declaration().and_then(|declaration| {
            click::surface::click_declaration_source_position(source, declaration)
        })
    };
    // A proof failure records the declaration it arose in. A declaration
    // check records only which declaration was being visited, which a check
    // made between visits does not update, so what its message names wins.
    if error.kind() == ClickErrorKind::Proof
        && let Some(position) = recorded()
    {
        return Some(position);
    }
    report
        .split('`')
        .skip(1)
        .step_by(2)
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .filter(|quoted| {
            !quoted.is_empty()
                && quoted
                    .chars()
                    .all(|character| character.is_alphanumeric() || character == '_')
        })
        .find_map(|name| click::surface::click_declaration_source_position(source, name))
        .or_else(recorded)
}

/// [`click_message`], followed by where the declaration the failure is about
/// is written when the failure records one. A declaration that fails its
/// checks is reported before any proof runs, so it has no tactic to show.
fn located_click_message(
    error: click::surface::ClickError,
    sidecar: &Path,
    project: &ClickProject,
    line_offset: usize,
) -> String {
    let mut report = error.concise_report();
    if let Some(source) = project.entry_source()
        && let Some(position) = failure_declaration_position(&error, &report, source)
        && let Some(excerpt) = source_excerpt(sidecar, source, &position, line_offset)
    {
        report.push_str("\n\n");
        report.push_str(&excerpt);
    }
    report
}

fn shell_word(value: &str) -> String {
    if value
        .bytes()
        .all(|byte| byte.is_ascii_alphanumeric() || b"/._-".contains(&byte))
    {
        value.to_owned()
    } else {
        format!("'{}'", value.replace('\'', "'\\''"))
    }
}

fn proof_error_report(
    error: &ClickError,
    sidecar: &Path,
    show_trace: bool,
    project: &ClickProject,
    inputs: &CInput,
    line_offset: usize,
    trace_target: Option<&click::surface::SourcePosition>,
) -> String {
    let (mut report, mut context) = error.concise_report_parts();
    if let Some(source) = project.entry_source()
        && let Some(position) = proof_source_position(error, project, inputs, source)
    {
        let mut has_full_tactic = false;
        if let Some(formatted) = format_source_tactic_at_position(source, &position, line_offset) {
            if let Some(index) = context.iter().position(|line| line.starts_with("tactic: ")) {
                context[index] = formatted;
            } else {
                context.insert(0, formatted);
            }
            has_full_tactic = true;
        }
        if !has_full_tactic
            && let Some(excerpt) = source_excerpt(sidecar, source, &position, line_offset)
        {
            context.push(excerpt);
        }
    }
    if context.is_empty()
        || !context
            .iter()
            .any(|line| line.starts_with("tactic@") || line.starts_with("  --> "))
    {
        // No tactic of the proof could be shown. A failure that knows its
        // declaration, or at least its claim, shows where that is written.
        let declaration = error.proof_declaration().or_else(|| {
            error
                .proof_claim_label()
                .and_then(|claim| claim.split_once('.'))
                .map(|(declaration, _)| declaration)
        });
        if matches!(error.kind(), ClickErrorKind::Proof | ClickErrorKind::Type)
            && let Some(source) = project.entry_source()
            && let Some(position) = declaration
                .filter(|_| error.kind() == ClickErrorKind::Proof)
                .and_then(|declaration| {
                    click::surface::click_declaration_source_position(source, declaration)
                })
                // A failure that names a C statement is located already; one
                // that names nothing else shows the declaration it quotes.
                .or_else(|| {
                    (!report.contains("C statement at"))
                        .then(|| failure_declaration_position(error, &report, source))
                        .flatten()
                })
            && let Some(excerpt) = source_excerpt(sidecar, source, &position, line_offset)
        {
            context.push(excerpt);
        }
    }
    if !context.is_empty() {
        report.push_str("\n\n");
        report.push_str(&context.join("\n"));
    }
    if show_trace {
        let source_locations = ProofSourceLocations::new(project, inputs);
        let target = trace_target.cloned().or_else(|| {
            project
                .entry_source()
                .and_then(|source| proof_source_position(error, project, inputs, source))
        });
        let positions = RefCell::new(HashMap::<
            Vec<usize>,
            Option<(String, click::surface::SourcePosition)>,
        >::new());
        let tactic_location = |path: &[usize]| {
            if let Some(cached) = positions.borrow().get(path) {
                return cached.clone();
            }
            let label = error.proof_claim_label().and_then(|claim| {
                let source = project.entry_source()?;
                let position = source_locations.position(claim, path, source)?;
                let multiple = tactic_line_has_multiple_starts(source, &position).unwrap_or(true);
                let line = position.line + line_offset;
                let label = if multiple {
                    format!("tactic@{line}:{}", position.column)
                } else {
                    format!("tactic@{line}")
                };
                Some((label, position))
            });
            positions.borrow_mut().insert(path.to_vec(), label.clone());
            label
        };
        let branch_arm = |path: &[usize], target: &click::surface::SourcePosition| {
            let source = project.entry_source()?;
            let claim = error.proof_claim_label()?;
            let branch = source_locations.position(claim, path, source)?;
            tactic_arm_containing_position(source, &branch, target)
                .ok()
                .flatten()
        };
        let have_body_contains = |path: &[usize], target: &click::surface::SourcePosition| {
            let Some(source) = project.entry_source() else {
                return false;
            };
            let Some(claim) = error.proof_claim_label() else {
                return false;
            };
            let Some(have) = source_locations.position(claim, path, source) else {
                return false;
            };
            tactic_have_body_contains_position(source, &have, target).unwrap_or(false)
        };
        if let Some(trace) = error.trace_context_report_with_tactic_locations(
            &tactic_location,
            &branch_arm,
            &have_body_contains,
            target.as_ref(),
        ) {
            report.push_str("\n\n");
            report.push_str(&trace);
            if let Some(formatted) = target.as_ref().and_then(|position| {
                project.entry_source().and_then(|source| {
                    format_source_tactic_at_position(source, position, line_offset)
                })
            }) {
                report.push_str("\n\n");
                report.push_str(&formatted);
            }
        } else {
            report.push_str(
                "\n\nproof trace unavailable: no checked path was retained for this failure",
            );
        }
        return report;
    }
    // The hint is printed only for a command that `--trace-proof` accepts:
    // both resolve the name through `trace_unit`.
    if error.kind() == ClickErrorKind::Proof
        && let Some((declaration, _)) = error
            .proof_claim_label()
            .and_then(|claim| claim.split_once('.'))
        && let Ok(unit) = trace_unit(declaration, project, inputs)
    {
        report.push_str(&format!(
            "\n\nTo get a trace:\n  click verify --trace-proof {} {}",
            shell_word(unit.name()),
            shell_word(&sidecar.display().to_string())
        ));
    }
    report
}

/// The one proof unit `--trace-proof` verifies and traces.
enum TraceUnit {
    Function(String),
    Theorem(String),
}

impl TraceUnit {
    fn name(&self) -> &str {
        match self {
            Self::Function(name) | Self::Theorem(name) => name,
        }
    }
}

/// Resolves a `--trace-proof` argument against the proofs the sidecar
/// selects: a C function or an entry-module theorem, by name. Validation
/// refuses a name declared as both, so the name alone identifies the proof.
/// The error says why the name cannot be traced.
fn trace_unit(
    requested: &str,
    project: &ClickProject,
    inputs: &CInput,
) -> Result<TraceUnit, String> {
    let names = match inputs {
        CInput::Bundle(sources) => c0_project_selected_proof_names(project, &source_refs(sources))
            .map_err(click_message)?,
        CInput::Prepared(imports) => {
            c0_prepared_project_selected_proof_names(project, imports).map_err(click_message)?
        }
        CInput::PreparedProgram(_) => {
            return Err(
                "`--trace-proof` currently supports C sidecars, not typed compiler inputs".into(),
            );
        }
    };
    let selects = |kind: &str, name: &str| {
        names.iter().any(|selected| {
            selected
                .strip_prefix(kind)
                .and_then(|rest| rest.strip_prefix(':'))
                == Some(name)
        })
    };
    if selects("function", requested) {
        Ok(TraceUnit::Function(requested.to_owned()))
    } else if selects("theorem", requested) {
        Ok(TraceUnit::Theorem(requested.to_owned()))
    } else {
        Err(format!("`{requested}` is not a selected proof"))
    }
}

fn format_source_tactic(
    tactic: &str,
    source_indent: &str,
    line: usize,
    column: Option<usize>,
) -> String {
    let location = column.map_or_else(
        || format!("tactic@{line}"),
        |column| format!("tactic@{line}:{column}"),
    );
    let mut report = format!("{location}:");
    for (index, line) in tactic.lines().enumerate() {
        report.push_str("\n  ");
        if index == 0 {
            report.push_str(line);
        } else {
            report.push_str(line.strip_prefix(source_indent).unwrap_or(line));
        }
    }
    report
}

fn format_source_tactic_at_position(
    source: &str,
    position: &click::surface::SourcePosition,
    line_offset: usize,
) -> Option<String> {
    let tactic = tactic_source_at_position(source, position).ok()?;
    let source_line = source
        .lines()
        .nth(position.line.checked_sub(1)?)
        .unwrap_or("");
    let indent = source_line
        .chars()
        .take(position.column.saturating_sub(1))
        .collect::<String>();
    let multiple = tactic_line_has_multiple_starts(source, position).unwrap_or(true);
    Some(format_source_tactic(
        &tactic,
        &indent,
        position.line + line_offset,
        multiple.then_some(position.column),
    ))
}

fn proof_source_position(
    error: &ClickError,
    project: &ClickProject,
    inputs: &CInput,
    source: &str,
) -> Option<click::surface::SourcePosition> {
    let (claim, path) = error.proof_source_site()?;
    proof_source_position_for_path(claim, path, project, inputs, source)
}

fn proof_source_position_for_path(
    claim: &str,
    path: &[usize],
    project: &ClickProject,
    inputs: &CInput,
    source: &str,
) -> Option<click::surface::SourcePosition> {
    ProofSourceLocations::new(project, inputs).position(claim, path, source)
}

/// Resolving an enclosing tactic parses and resolves the project. A trace
/// walks many nested tactics under the same enclosing step, so share that
/// resolution across all of its location callbacks.
struct ProofSourceLocations<'a> {
    project: &'a ClickProject,
    inputs: &'a CInput,
    outer: RefCell<HashMap<(String, usize), Option<click::surface::SourcePosition>>>,
}

impl<'a> ProofSourceLocations<'a> {
    fn new(project: &'a ClickProject, inputs: &'a CInput) -> Self {
        Self {
            project,
            inputs,
            outer: RefCell::new(HashMap::new()),
        }
    }

    fn position(
        &self,
        claim: &str,
        path: &[usize],
        source: &str,
    ) -> Option<click::surface::SourcePosition> {
        let source_index = *path.first()?;
        let key = (claim.to_owned(), source_index);
        let cached = self.outer.borrow().get(&key).cloned();
        let outer = if let Some(cached) = cached {
            cached
        } else {
            let outer = match self.inputs {
                CInput::Bundle(sources) => c0_project_tactic_source_position(
                    self.project,
                    &source_refs(sources),
                    claim,
                    source_index,
                ),
                CInput::Prepared(imports) => c0_prepared_project_tactic_source_position(
                    self.project,
                    imports,
                    claim,
                    source_index,
                ),
                CInput::PreparedProgram(import) => program_prepared_project_tactic_source_position(
                    self.project,
                    import,
                    claim,
                    source_index,
                ),
            }
            .ok();
            self.outer.borrow_mut().insert(key, outer.clone());
            outer
        }?;
        if path.len() == 1 {
            Some(outer)
        } else {
            nested_tactic_source_position(source, &outer, &path[1..]).ok()
        }
    }
}

fn source_excerpt(
    sidecar: &Path,
    source: &str,
    position: &click::surface::SourcePosition,
    line_offset: usize,
) -> Option<String> {
    let line = source.lines().nth(position.line.checked_sub(1)?)?;
    let chars = line.chars().collect::<Vec<_>>();
    let column = position.column.checked_sub(1)?;
    if column > chars.len() {
        return None;
    }
    let start = column.saturating_sub(48);
    let end = chars.len().min(start + 160);
    let snippet = chars[start..end].iter().collect::<String>();
    let left = if start == 0 { "" } else { "…" };
    let right = if end == chars.len() { "" } else { "…" };
    let marker = chars[column..]
        .iter()
        .take_while(|character| character.is_alphanumeric() || **character == '_')
        .take(12)
        .count()
        .max(1);
    let caret_offset = chars[start..column]
        .iter()
        .map(|character| if *character == '\t' { 4 } else { 1 })
        .sum::<usize>()
        + usize::from(start > 0);
    // An mdtest reports lines of the markdown file, not of its Click block.
    let file_line = position.line + line_offset;
    let width = file_line.to_string().len();
    Some(format!(
        "  --> {}:{}:{}\n  {:width$} | {}{}{}\n  {:width$} | {}{}",
        sidecar.display(),
        file_line,
        position.column,
        file_line,
        left,
        snippet,
        right,
        "",
        " ".repeat(caret_offset),
        "^".repeat(marker),
        width = width,
    ))
}

fn print_incremental_selection(
    sidecar: &Path,
    revision: &str,
    selected: &[String],
    reused: &[String],
    reasons: &[String],
    full_rebuild: bool,
) {
    println!("INCREMENTAL {} since {revision}", sidecar.display());
    println!(
        "  mode: {}",
        if full_rebuild {
            "full rebuild"
        } else {
            "semantic function selection"
        }
    );
    println!(
        "  selected ({}): {}",
        selected.len(),
        bounded_names(selected)
    );
    println!("  reused ({}): {}", reused.len(), bounded_names(reused));
    for reason in reasons.iter().take(12) {
        println!("  because: {reason}");
    }
    if reasons.len() > 12 {
        println!("  because: ... {} more reasons", reasons.len() - 12);
    }
}

fn bounded_names(names: &[String]) -> String {
    if names.is_empty() {
        return "(none)".to_string();
    }
    let mut shown = names.iter().take(12).cloned().collect::<Vec<_>>();
    if names.len() > shown.len() {
        shown.push(format!("... {} more", names.len() - shown.len()));
    }
    shown.join(", ")
}

fn git_repo_root(path: &Path) -> Result<PathBuf, String> {
    let anchor = if path.is_dir() {
        path
    } else {
        containing_directory(path)
    };
    let output = Command::new("git")
        .args([
            "-C",
            &anchor.display().to_string(),
            "rev-parse",
            "--show-toplevel",
        ])
        .output()
        .map_err(|error| format!("failed to run git: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "`{}` is not inside a readable git worktree",
            path.display()
        ));
    }
    Ok(PathBuf::from(
        String::from_utf8_lossy(&output.stdout).trim(),
    ))
}

fn git_commit_id(repo: &Path, revision: &str) -> Result<String, String> {
    let output = Command::new("git")
        .args([
            "-C",
            &repo.display().to_string(),
            "rev-parse",
            "--verify",
            &format!("{revision}^{{commit}}"),
        ])
        .output()
        .map_err(|error| format!("failed to run git: {error}"))?;
    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
    } else {
        Err(format!("unknown git revision `{revision}`"))
    }
}

fn verification_marker_path(repo: &Path, commit: &str, sidecar: &Path) -> Result<PathBuf, String> {
    let relative = sidecar.strip_prefix(repo).map_err(|_| {
        format!(
            "`{}` is outside git worktree `{}`",
            sidecar.display(),
            repo.display()
        )
    })?;
    let mut hasher = DefaultHasher::new();
    relative.hash(&mut hasher);
    let output = Command::new("git")
        .args([
            "-C",
            &repo.display().to_string(),
            "rev-parse",
            "--git-path",
            INCREMENTAL_CACHE_SCHEMA,
        ])
        .output()
        .map_err(|error| format!("failed to locate git metadata: {error}"))?;
    if !output.status.success() {
        return Err("git did not expose its metadata path".to_string());
    }
    let root = PathBuf::from(String::from_utf8_lossy(&output.stdout).trim());
    let root = if root.is_absolute() {
        root
    } else {
        repo.join(root)
    };
    Ok(root.join(commit).join(format!("{:016x}", hasher.finish())))
}

fn verifier_fingerprint() -> Result<&'static str, String> {
    static FINGERPRINT: OnceLock<Result<String, String>> = OnceLock::new();
    FINGERPRINT
        .get_or_init(|| {
            let executable = env::current_exe()
                .map_err(|error| format!("failed to locate the Click executable: {error}"))?;
            let bytes = fs::read(&executable).map_err(|error| {
                format!(
                    "failed to fingerprint Click executable `{}`: {error}",
                    executable.display()
                )
            })?;
            let mut hasher = DefaultHasher::new();
            bytes.hash(&mut hasher);
            Ok(format!("{:016x}", hasher.finish()))
        })
        .as_deref()
        .map_err(Clone::clone)
}

/// The verifier switches that change a verdict: every `CLICK_*` environment
/// variable, sorted, so a baseline attested with budgets or the memory DAG
/// disabled is never reused by a run with them enabled.
fn environment_switches() -> String {
    environment_switches_from(env::vars())
}

fn environment_switches_from(variables: impl IntoIterator<Item = (String, String)>) -> String {
    let mut switches = variables
        .into_iter()
        .filter(|(name, _)| name.starts_with("CLICK_"))
        .map(|(name, value)| format!("env={name}={value}\n"))
        .collect::<Vec<_>>();
    switches.sort();
    switches.concat()
}

fn marker_contents(
    commit: &str,
    relative: &Path,
    fingerprint: &str,
    switches: &str,
    target: CTarget,
) -> String {
    format!(
        "{INCREMENTAL_CACHE_SCHEMA}\ntarget={}\nverifier={fingerprint}\ncommit={commit}\nsidecar={}\n{switches}",
        target.name(),
        relative.display()
    )
}

fn valid_marker(
    contents: &str,
    commit: &str,
    relative: &Path,
    fingerprint: &str,
    target: CTarget,
) -> bool {
    contents
        == marker_contents(
            commit,
            relative,
            fingerprint,
            &environment_switches(),
            target,
        )
}

/// Compare the commit's complete input bundle with the snapshot that was
/// actually verified, including transitively included headers.
fn baseline_matches_verified(
    baseline: &LoadedSidecar,
    click_source: &str,
    sources: &[(String, String)],
) -> bool {
    baseline.0 == click_source && baseline.1 == sources
}

fn has_full_verification_marker(
    repo: &Path,
    commit: &str,
    sidecar: &Path,
    target: CTarget,
) -> Result<bool, String> {
    let marker = verification_marker_path(repo, commit, sidecar)?;
    let relative = sidecar.strip_prefix(repo).map_err(|_| {
        format!(
            "`{}` is outside git worktree `{}`",
            sidecar.display(),
            repo.display()
        )
    })?;
    let fingerprint = verifier_fingerprint()?;
    match fs::read_to_string(marker) {
        Ok(contents) => Ok(valid_marker(
            &contents,
            commit,
            relative,
            fingerprint,
            target,
        )),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(_) => Ok(false),
    }
}

/// Attest only commits whose complete input bundle equals the verified
/// snapshot. Re-reading the working tree here could certify a different
/// program if a file changed after verification.
fn record_full_verification(
    sidecar: &Path,
    click_source: &str,
    sources: &[(String, String)],
    also_attest: &[String],
) -> Result<(), String> {
    let sidecar = fs::canonicalize(sidecar)
        .map_err(|error| format!("failed to resolve `{}`: {error}", sidecar.display()))?;
    let repo = git_repo_root(&sidecar)?;
    let commit = git_commit_id(&repo, "HEAD")?;
    let relative = sidecar.strip_prefix(&repo).map_err(|_| {
        format!(
            "`{}` is outside git worktree `{}`",
            sidecar.display(),
            repo.display()
        )
    })?;
    for attested in std::iter::once(&commit).chain(also_attest) {
        let Some(baseline) = load_baseline_sidecar(&repo, attested, &sidecar)? else {
            continue;
        };
        if !baseline_matches_verified(&baseline, click_source, sources) {
            continue;
        }
        let marker = verification_marker_path(&repo, attested, &sidecar)?;
        let parent = marker
            .parent()
            .ok_or_else(|| "incremental marker has no parent directory".to_string())?;
        fs::create_dir_all(parent)
            .map_err(|error| format!("failed to create `{}`: {error}", parent.display()))?;
        let temporary = parent.join(format!(".tmp-{}", std::process::id()));
        fs::write(
            &temporary,
            marker_contents(
                attested,
                relative,
                verifier_fingerprint()?,
                &environment_switches(),
                selected_c_target(click_source).map_err(click_message)?,
            ),
        )
        .map_err(|error| format!("failed to write `{}`: {error}", temporary.display()))?;
        fs::rename(&temporary, &marker)
            .map_err(|error| format!("failed to install `{}`: {error}", marker.display()))?;
    }
    Ok(())
}

fn git_show(repo: &Path, revision: &str, path: &Path) -> Result<Option<String>, String> {
    let relative = path.strip_prefix(repo).map_err(|_| {
        format!(
            "`{}` is outside git worktree `{}`",
            path.display(),
            repo.display()
        )
    })?;
    let spec = format!("{revision}:{}", relative.display());
    let output = Command::new("git")
        .args(["-C", &repo.display().to_string(), "show", &spec])
        .output()
        .map_err(|error| format!("failed to run git: {error}"))?;
    if output.status.success() {
        Ok(Some(String::from_utf8_lossy(&output.stdout).into_owned()))
    } else {
        Ok(None)
    }
}

fn load_baseline_sidecar(
    repo: &Path,
    revision: &str,
    click_path: &Path,
) -> Result<Option<LoadedSidecar>, String> {
    let Some(click_source) = git_show(repo, revision, click_path)? else {
        return Ok(None);
    };
    let parent = containing_directory(click_path);
    let Some(sources) = load_baseline_sources(parent, &click_source, |source_path| {
        git_show(repo, revision, source_path)
    })?
    else {
        return Ok(None);
    };
    Ok(Some((click_source, sources)))
}

fn load_baseline_sources(
    parent: &Path,
    click_source: &str,
    mut load: impl FnMut(&Path) -> Result<Option<String>, String>,
) -> Result<Option<Vec<(String, String)>>, String> {
    let mut pending = verifying_source_paths(click_source).map_err(click_message)?;
    let target = selected_c_target(click_source).map_err(click_message)?;
    let mut sources = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    let mut next = 0;
    while next < pending.len() {
        let name = pending[next].clone();
        next += 1;
        if !seen.insert(name.clone()) {
            continue;
        }
        let source_path = parent.join(&name);
        let Some(source) = load(&source_path)? else {
            return Ok(None);
        };
        let includes = c_source::local_include_paths_for_target(&name, &source, target)
            .map_err(|error| format!("failed to process baseline C source includes: {error}"))?;
        pending.extend(includes);
        sources.push((name, source));
    }
    Ok(Some(sources))
}

/// Shows a discovered sidecar relative to the directory the user named, since
/// project discovery canonicalizes to absolute paths.
fn display_path(sidecar: &Path, root: &Path) -> String {
    let Ok(root) = fs::canonicalize(root) else {
        return sidecar.display().to_string();
    };
    let relative = sidecar.strip_prefix(&root).unwrap_or(sidecar);
    let shown: PathBuf = if relative == sidecar {
        sidecar.to_path_buf()
    } else {
        root.file_name().map_or_else(
            || relative.to_path_buf(),
            |name| Path::new(name).join(relative),
        )
    };
    shown.display().to_string()
}

fn plural(count: usize) -> &'static str {
    if count == 1 { "" } else { "s" }
}

fn verify_file(
    click_path: &Path,
    limits: RunLimits,
    project_root: Option<&Path>,
    trace_proof: Option<&str>,
    trace_to: Option<&TraceTo>,
) -> Result<(), String> {
    // A previous failed sidecar may have left admissions behind; each file
    // reports only its own.
    let _ = click::surface::take_sorry_admissions();
    // Every phase of the run, from loading its sources and building the
    // external-dependency summary to counting its selected proofs, runs
    // inside the run's work budget and crash-containment bound.
    with_run_limits("click verify", limits, || {
        verify_file_within_limits(click_path, project_root, trace_proof, trace_to)
    })
}

fn verify_file_within_limits(
    click_path: &Path,
    project_root: Option<&Path>,
    trace_proof: Option<&str>,
    trace_to: Option<&TraceTo>,
) -> Result<(), String> {
    let target = {
        let _phase = VerificationPhase::new("project loading");
        load_target_inputs(click_path, project_root)?
    };
    let line_offset = target.line_offset();
    let LoadedTarget {
        click_source,
        project,
        inputs,
        mdtest,
    } = target;
    let trace_unit = trace_proof
        .map(|requested| {
            trace_unit(requested, &project, &inputs)
                .map_err(|message| {
                    format!(
                        "{message} in `{}`; `--trace-proof` takes the name of a C function or theorem the sidecar proves",
                        click_path.display()
                    )
                })
        })
        .transpose()?;
    let trace_target = trace_to
        .map(|target| resolve_trace_target(&click_source, line_offset, target))
        .transpose()?;
    let summary = {
        let _phase = VerificationPhase::new("external dependency summary");
        match &inputs {
            CInput::Bundle(sources) => c0_project_summary(&project, &source_refs(sources))
                .map_err(|error| located_click_message(error, click_path, &project, line_offset))?,
            CInput::Prepared(imports) => c0_prepared_project_summary(&project, imports)
                .map_err(|error| located_click_message(error, click_path, &project, line_offset))?,
            CInput::PreparedProgram(import) => program_prepared_project_summary(&project, import)
                .map_err(|error| {
                located_click_message(error, click_path, &project, line_offset)
            })?,
        }
    };
    let (verified, successful_trace) = {
        let run_selected = || match (&inputs, &trace_unit) {
            (CInput::Bundle(sources), Some(TraceUnit::Function(function))) => {
                verify_c0_project_functions(&project, &source_refs(sources), [function.clone()])
            }
            (CInput::Prepared(imports), Some(TraceUnit::Function(function))) => {
                verify_c0_prepared_project_functions(&project, imports, [function.clone()])
            }
            (CInput::Bundle(sources), Some(TraceUnit::Theorem(theorem))) => {
                verify_c0_project_theorem(&project, &source_refs(sources), theorem)
            }
            (CInput::Prepared(imports), Some(TraceUnit::Theorem(theorem))) => {
                verify_c0_prepared_project_theorem(&project, imports, theorem)
            }
            (CInput::PreparedProgram(_), Some(_)) => unreachable!(),
            (CInput::Bundle(sources), None) => verify_c0_project(&project, &source_refs(sources)),
            (CInput::Prepared(imports), None) => verify_c0_prepared_project(&project, imports),
            (CInput::PreparedProgram(import), None) => {
                verify_program_prepared_project(&project, import)
            }
        };
        let report = |error: ClickError| {
            proof_error_report(
                &error,
                click_path,
                trace_proof.is_some(),
                &project,
                &inputs,
                line_offset,
                trace_target.as_ref(),
            )
        };
        match &trace_unit {
            Some(unit) => with_proof_trace(unit.name(), || {
                let verified = run_selected().map_err(report)?;
                // The renderer asks for one step's location several times.
                let source_locations = ProofSourceLocations::new(&project, &inputs);
                let located = RefCell::new(HashMap::<
                    (String, Vec<usize>),
                    Option<(String, click::surface::SourcePosition)>,
                >::new());
                let locate = |claim: &str, path: &[usize]| {
                    let key = (claim.to_owned(), path.to_vec());
                    if let Some(cached) = located.borrow().get(&key) {
                        return cached.clone();
                    }
                    let label = (|| {
                        let source = project.entry_source()?;
                        let position = source_locations.position(claim, path, source)?;
                        let multiple = tactic_line_has_multiple_starts(source, &position).ok()?;
                        let line = position.line + line_offset;
                        let label = if multiple {
                            format!("tactic@{line}:{}", position.column)
                        } else {
                            format!("tactic@{line}")
                        };
                        Some((label, position))
                    })();
                    located.borrow_mut().insert(key, label.clone());
                    label
                };
                let arm = |claim: &str, path: &[usize], target: &click::surface::SourcePosition| {
                    let source = project.entry_source()?;
                    let branch = source_locations.position(claim, path, source)?;
                    tactic_arm_containing_position(source, &branch, target)
                        .ok()
                        .flatten()
                };
                let body =
                    |claim: &str, path: &[usize], target: &click::surface::SourcePosition| {
                        let Some(source) = project.entry_source() else {
                            return false;
                        };
                        let Some(have) = source_locations.position(claim, path, source) else {
                            return false;
                        };
                        tactic_have_body_contains_position(source, &have, target).unwrap_or(false)
                    };
                let trace = accepted_proof_trace(&locate, &arm, &body, trace_target.as_ref()).map(
                    |mut trace| {
                        if let Some(formatted) = trace_target.as_ref().and_then(|position| {
                            format_source_tactic_at_position(&click_source, position, line_offset)
                        }) {
                            trace.push_str("\n\n");
                            trace.push_str(&formatted);
                        }
                        trace
                    },
                );
                Ok((verified, trace))
            }),
            None => run_selected()
                .map(|verified| (verified, None))
                .map_err(report),
        }
    }?;
    if trace_proof.is_some() {
        let trace = successful_trace.ok_or_else(|| {
            trace_to.map_or_else(
                || "verified proof has no retained checked path to trace".to_owned(),
                |target| {
                    format!(
                        "tactic@{} has no recorded checked step on an accepted path",
                        target.line
                    )
                },
            )
        })?;
        println!("{trace}\n");
    }
    print_external_dependencies(&summary.external_dependencies, &verified);
    // The count comes from the summary's resolution of the sources, so
    // reporting it does not parse every source again after verification.
    let selected = if trace_proof.is_some() {
        1
    } else {
        summary.selected_proof_count
    };
    println!("{selected} selected proof{} verified", plural(selected));
    let admissions = click::surface::take_sorry_admissions();
    if admissions.is_empty() {
        if let CInput::Bundle(sources) = &inputs
            && trace_proof.is_none()
            && mdtest.is_none()
            && project.modules().len() == 1
            && project.c_profile().is_none()
            && let Err(message) = record_full_verification(click_path, &click_source, sources, &[])
        {
            eprintln!("click-verify: warning: could not record incremental baseline: {message}");
        }
    } else {
        eprintln!(
            "click-verify: WARNING: {} proof unit{} admitted via `sorry` in `{}`: NOTHING HERE IS PROVED. `sorry` is a dev-only hole (enabled by `--allow-sorry`); it never verifies in the gate.",
            admissions.len(),
            plural(admissions.len()),
            click_path.display(),
        );
        for admission in &admissions {
            eprintln!(
                "click-verify: WARNING: sorry admitted `{}`",
                admission.label
            );
        }
        eprintln!("click-verify: WARNING: no incremental baseline recorded for a sorry run.");
    }
    Ok(())
}

fn verify_location(
    click_path: &Path,
    line: usize,
    column: usize,
    limits: RunLimits,
) -> Result<(), String> {
    // As in `verify_file`, loading is inside the run's limits.
    with_run_limits("click verify", limits, || {
        verify_location_within_limits(click_path, line, column)
    })
}

fn verify_location_within_limits(
    click_path: &Path,
    line: usize,
    column: usize,
) -> Result<(), String> {
    let project_root = lone_sidecar_project_root(click_path)?;
    let target = {
        let _phase = VerificationPhase::new("project loading");
        load_target_inputs(click_path, Some(&project_root))?
    };
    let line_offset = target.line_offset();
    // An mdtest location names a line of the markdown file; the verifier
    // selects by lines of the extracted Click block.
    let line = match &target.mdtest {
        Some(mdtest) => mdtest
            .click_line(line)
            .map_err(|error| format!("`{}:{line}:{column}`: {error}", click_path.display()))?,
        None => line,
    };
    let LoadedTarget {
        project, inputs, ..
    } = target;
    let summary = {
        let _phase = VerificationPhase::new("external dependency summary");
        match &inputs {
            CInput::Bundle(sources) => c0_project_summary(&project, &source_refs(sources))
                .map_err(|error| located_click_message(error, click_path, &project, line_offset))?,
            CInput::Prepared(imports) => c0_prepared_project_summary(&project, imports)
                .map_err(|error| located_click_message(error, click_path, &project, line_offset))?,
            CInput::PreparedProgram(import) => program_prepared_project_summary(&project, import)
                .map_err(|error| {
                located_click_message(error, click_path, &project, line_offset)
            })?,
        }
    };
    let verified = {
        let result = match &inputs {
            CInput::Bundle(sources) => {
                verify_c0_project_at(&project, &source_refs(sources), line, column)
            }
            CInput::Prepared(imports) => {
                verify_c0_prepared_project_at(&project, imports, line, column)
            }
            CInput::PreparedProgram(import) => {
                verify_program_prepared_project_at(&project, import, line, column)
            }
        };
        result.map_err(|error| {
            proof_error_report(
                &error,
                click_path,
                false,
                &project,
                &inputs,
                line_offset,
                None,
            )
        })
    }?;
    print_external_dependencies(&summary.external_dependencies, &verified);
    println!("1 selected proof verified");
    Ok(())
}

fn print_external_dependencies(
    dependencies: &BTreeMap<String, Vec<String>>,
    verified: &[VerifiedCTheorem],
) {
    if let Some(selection) = verified
        .first()
        .and_then(|theorem| theorem.selection.as_ref())
    {
        for assumption in &selection.runtime_assumptions {
            println!("runtime assumption: {assumption}");
        }
    }
    let verified_functions = verified
        .iter()
        .map(|theorem| theorem.function_block.signature().name())
        .collect::<std::collections::BTreeSet<_>>();
    for (function, external) in dependencies {
        if verified_functions.contains(function.as_str()) {
            println!(
                "external assumptions: {function} -> {}",
                external.join(", ")
            );
        }
    }
}

#[cfg(test)]
#[path = "click-verify/incremental_tests.rs"]
mod incremental_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    fn assert_source_diagnostic(report: &str) {
        for internal in ["snapshot#", "snapshot<", "load A=", "pointer(pointer "] {
            assert!(!report.contains(internal), "{report}");
        }
        assert!(
            !report
                .split("value ")
                .skip(1)
                .any(|tail| { tail.as_bytes().first().is_some_and(u8::is_ascii_uppercase) }),
            "{report}"
        );
    }

    #[test]
    fn refused_transport_names_the_cell_and_loop_counter_without_kernel_notation() {
        let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests/loop_binder_instance_footprint_includes_its_memory.md");
        let report =
            entry_with([fixture.display().to_string()]).expect_err("the loop may write the cell");
        assert_source_diagnostic(&report);
        assert!(report.contains("store to occupied[start]"), "{report}");
        assert!(report.contains("i >= end"), "{report}");
        assert!(report.contains("at(pre, occupied[start])"), "{report}");
        assert!(!report.contains("lowered target"), "{report}");
        assert_eq!(
            report
                .matches("some effect facts have no exact Click spelling")
                .count(),
            1,
            "{report}"
        );
    }

    #[test]
    fn refused_call_result_fact_uses_the_proof_binding() {
        let (root, path) = temporary_project(
            "call-result-diagnostic",
            r#"
            extern int32 child(int32 x);
            int32 parent(int32 x) { return child(x); }
        "#,
            r#"
            verifying "program.c";
            theorem negative(n: int32) {
                requires n < 0;
                ensures n < 1 by { simp(); }
            }
            extern int32 child(int32 x) {
                requires 0 <= x;
                ensures 0 <= result;
            }
            int32 parent(int32 x) {
                requires 0 <= x;
                ensures 0 <= result;
            } by {
                let r = step(child(x), {});
                have r < 1 by {
                    apply(negative(r)) using { 0 <= r; }
                }
                step();
                simp();
            }
        "#,
        );
        let result = entry_with([path.display().to_string()]);
        fs::remove_dir_all(root).unwrap();
        let report = result.expect_err("a nonnegative call result is not negative");
        assert_source_diagnostic(&report);
        assert!(report.contains("r < 0"), "{report}");
        assert!(
            report.contains("with n = r instantiates to r < 0"),
            "{report}"
        );
    }

    #[test]
    fn refused_match_arm_contradiction_reports_its_own_tactic() {
        for name in [
            "arm_contradiction_reports_its_source",
            "nested_arm_contradiction_reports_its_source",
            "bridged_arm_contradiction_reports_its_source",
            "arm_contradiction_after_loop_reports_its_source",
        ] {
            let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("mdtests/{name}.md"));
            let source = fs::read_to_string(&fixture).unwrap();
            let (line, tactic) = source
                .lines()
                .enumerate()
                .find(|(_, line)| {
                    line.trim()
                        .starts_with("contradiction(x.model == Cell::Present(")
                })
                .map(|(line, tactic)| (line + 1, tactic.trim()))
                .unwrap();
            let report = entry_with([fixture.display().to_string()])
                .expect_err("the constructor is not refuted");
            assert!(
                report.contains(&format!("tactic@{line}:")),
                "{name}: {report}"
            );
            assert!(report.contains(tactic), "{name}: {report}");
            assert!(
                report.contains("requires an exact fact and its negation"),
                "{name}: {report}"
            );
            assert!(
                report.contains("in match arm `Cell::Present`"),
                "{name}: {report}"
            );
        }
    }

    fn loop_frontier_trace_report(target: Option<usize>) -> String {
        let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests/loop_preserve_frontier_report_multi_exit.md");
        let mut arguments = vec!["--trace-proof".to_owned(), "scan".to_owned()];
        if let Some(line) = target {
            arguments.extend(["--trace-to".to_owned(), line.to_string()]);
        }
        arguments.push(fixture.display().to_string());
        entry_with(arguments).expect_err("the loop proof remains unfinished")
    }

    #[test]
    fn loop_frontier_trace_reports_the_unfinished_path() {
        let report = loop_frontier_trace_report(None);
        assert!(report.contains("stopped inside the loop body"), "{report}");
        let (_, trace) = report
            .split_once("proof trace (checked tactics and branch facts):")
            .unwrap_or_else(|| panic!("missing proof trace: {report}"));
        for line in [48, 49, 59] {
            assert!(trace.contains(&format!("tactic@{line}: step\n")), "{trace}");
        }
        assert!(!trace.contains("tactic@57:"), "{trace}");
    }

    #[test]
    fn loop_frontier_trace_to_selects_checked_tactics() {
        for target in [48, 57, 59] {
            let report = loop_frontier_trace_report(Some(target));
            let (_, trace) = report
                .split_once("proof trace (checked tactics and branch facts):")
                .unwrap_or_else(|| panic!("missing proof trace at {target}: {report}"));
            assert!(
                trace.contains(&format!("tactic@{target}: step\n")),
                "{trace}"
            );
            if target == 48 {
                assert!(!trace.contains("tactic@49:"), "{trace}");
            } else if target == 57 {
                assert!(!trace.contains("tactic@59:"), "{trace}");
            } else {
                assert!(!trace.contains("tactic@57:"), "{trace}");
            }
        }
    }

    #[test]
    fn loop_frontier_trace_to_an_unreached_tactic_explains_the_missing_step() {
        let report = loop_frontier_trace_report(Some(63));
        assert!(
            report.contains("target tactic has no recorded checked step on a retained path"),
            "{report}"
        );
        assert!(!report.contains("tactic@63: step\n"), "{report}");
    }

    #[test]
    fn loop_frontier_trace_to_selects_another_unfinished_arm() {
        let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests/loop_preserve_frontier_report_multi_exit.md");
        let mut loaded = load_target_inputs(&fixture, None).unwrap();
        let line_offset = loaded.line_offset();
        // Leave both arms unfinished, preserving physical source line numbers.
        loaded.click_source = loaded.click_source.replace(
            "                step();\n                step();",
            "                step();\n                ",
        );
        loaded.project = loaded
            .project
            .with_entry_source(loaded.click_source.clone());
        let target = resolve_trace_target(
            &loaded.click_source,
            line_offset,
            &TraceTo {
                line: 59,
                column: None,
            },
        )
        .unwrap();
        let CInput::Bundle(sources) = &loaded.inputs else {
            panic!("expected C fixture")
        };
        let report = with_proof_trace("scan", || {
            let error = verify_c0_project_functions(
                &loaded.project,
                &source_refs(sources),
                ["scan".to_owned()],
            )
            .expect_err("both preservation arms remain unfinished");
            proof_error_report(
                &error,
                &fixture,
                true,
                &loaded.project,
                &loaded.inputs,
                line_offset,
                Some(&target),
            )
        });
        assert!(report.contains("tactic@59: step\n"), "{report}");
        assert!(
            !report.contains("target tactic has no recorded checked step"),
            "{report}"
        );
    }

    #[test]
    fn trace_target_uses_a_unique_line_or_an_explicit_column() {
        let source = "by { step(); step(); }\nby {\n  step();\n}\n";
        assert_eq!(
            resolve_trace_target(
                source,
                8,
                &TraceTo {
                    line: 11,
                    column: None
                }
            )
            .unwrap(),
            click::surface::SourcePosition::new(3, 3),
        );
        assert!(
            resolve_trace_target(
                source,
                8,
                &TraceTo {
                    line: 9,
                    column: None
                }
            )
            .unwrap_err()
            .contains("several tactics")
        );
        assert_eq!(
            resolve_trace_target(
                source,
                8,
                &TraceTo {
                    line: 9,
                    column: Some(6)
                }
            )
            .unwrap(),
            click::surface::SourcePosition::new(1, 6),
        );

        // A proof `match` arm's block follows `=>`, which the source scanner
        // reads as two punctuation tokens; its tactics are targets too.
        let arm =
            "by {\n    match m {\n        K::A => {\n            step();\n        },\n    }\n}\n";
        assert_eq!(
            resolve_trace_target(
                arm,
                0,
                &TraceTo {
                    line: 4,
                    column: None
                }
            )
            .unwrap(),
            click::surface::SourcePosition::new(4, 13),
        );

        let nested = "by {\n    have n <= n by { simp(); }\n}\n";
        assert_eq!(
            resolve_trace_target(
                nested,
                8,
                &TraceTo {
                    line: 10,
                    column: None,
                },
            )
            .unwrap(),
            click::surface::SourcePosition::new(2, 5),
        );
    }

    #[test]
    fn location_suffixes_win_over_paths_that_could_be_directories() {
        assert!(looks_like_source_location("examples/tiny/tiny.click:12:5"));
        assert!(!looks_like_source_location("examples/tiny"));
        assert!(!looks_like_source_location("examples"));
    }

    #[test]
    fn parses_allow_sorry_and_rejects_it_with_changed_since() {
        assert_eq!(
            parse_arguments(["--allow-sorry".to_string(), "example.click".to_string()]),
            Ok(Arguments {
                target: "example.click".to_string(),
                limits: RunLimits::verify(),
                changed_since: None,
                explain: false,
                allow_sorry: true,
                trace_proof: None,
                trace_to: None,
            })
        );
        assert_eq!(
            entry_with([
                "--allow-sorry".to_string(),
                "--changed-since".to_string(),
                "HEAD".to_string(),
                "example.click".to_string(),
            ]),
            Err("`--allow-sorry` cannot be combined with `--changed-since`".to_string())
        );
    }

    #[test]
    fn parses_default_and_overridden_run_limits() {
        assert_eq!(
            parse_arguments(["example.click".to_string()]),
            Ok(Arguments {
                target: "example.click".to_string(),
                limits: RunLimits::verify(),
                changed_since: None,
                explain: false,
                allow_sorry: false,
                trace_proof: None,
                trace_to: None,
            })
        );
        assert_eq!(
            parse_arguments([
                "--time-limit".to_string(),
                "250ms".to_string(),
                "example.click".to_string(),
            ]),
            Ok(Arguments {
                target: "example.click".to_string(),
                limits: RunLimits {
                    time: Duration::from_millis(250),
                    ..RunLimits::verify()
                },
                changed_since: None,
                explain: false,
                allow_sorry: false,
                trace_proof: None,
                trace_to: None,
            })
        );
        assert_eq!(
            parse_arguments([
                "--work-limit".to_string(),
                "1_000".to_string(),
                "example.click".to_string(),
            ]),
            Ok(Arguments {
                target: "example.click".to_string(),
                limits: RunLimits {
                    work: 1_000,
                    ..RunLimits::verify()
                },
                changed_since: None,
                explain: false,
                allow_sorry: false,
                trace_proof: None,
                trace_to: None,
            })
        );
        assert!(
            parse_arguments([
                "--work-limit".to_string(),
                "0".to_string(),
                "example.click".to_string(),
            ])
            .is_err()
        );
        assert_eq!(
            parse_arguments([
                "--changed-since".to_string(),
                "HEAD~1".to_string(),
                "--explain".to_string(),
                "examples".to_string(),
            ]),
            Ok(Arguments {
                target: "examples".to_string(),
                limits: RunLimits::verify(),
                changed_since: Some("HEAD~1".to_string()),
                explain: true,
                allow_sorry: false,
                trace_proof: None,
                trace_to: None,
            })
        );
    }

    #[test]
    fn imported_projects_force_the_documented_selected_scope_rebuild() {
        let project = ClickProject::new(
            "entry.click",
            [
                click::surface::ClickModuleSource::new("library.click", "", []),
                click::surface::ClickModuleSource::new(
                    "entry.click",
                    "import \"library.click\";",
                    ["library.click".to_string()],
                ),
            ],
        );
        assert!(
            imported_project_rebuild_reason(&project)
                .unwrap()
                .contains("selected entry scope")
        );
        assert!(
            imported_project_rebuild_reason(&ClickProject::new(
                "entry.click",
                [click::surface::ClickModuleSource::new(
                    "entry.click",
                    "",
                    []
                )]
            ))
            .is_none()
        );
    }

    #[test]
    fn marker_contents_include_environment_switches() {
        let relative = Path::new("examples/tiny/tiny.click");
        let plain = marker_contents("abc", relative, "fp", "", CTarget::SUPPORTED);
        assert!(plain.contains("\ntarget=x86_64-linux-kernel\n"));
        let switches = environment_switches_from([(
            "CLICK_DISABLE_TACTIC_BUDGETS".to_string(),
            "1".to_string(),
        )]);
        let budgets_off = marker_contents("abc", relative, "fp", &switches, CTarget::SUPPORTED);
        assert_ne!(plain, budgets_off);
        assert!(budgets_off.ends_with("env=CLICK_DISABLE_TACTIC_BUDGETS=1\n"));
    }

    #[test]
    fn environment_switches_are_sorted_and_limited_to_click_variables() {
        let switches = environment_switches_from([
            ("PATH".to_string(), "x".to_string()),
            ("CLICK_TIMINGS".to_string(), "1".to_string()),
            ("CLICK_DISABLE_TACTIC_BUDGETS".to_string(), "1".to_string()),
        ]);
        assert_eq!(
            switches,
            "env=CLICK_DISABLE_TACTIC_BUDGETS=1\nenv=CLICK_TIMINGS=1\n"
        );
    }

    #[test]
    fn a_baseline_is_attested_only_when_its_sources_match_the_current_ones() {
        let current: LoadedSidecar = (
            "verifying \"a.c\";".to_string(),
            vec![("a.c".to_string(), "int32 f() { return 0; }".to_string())],
        );
        assert!(baseline_matches_verified(&current, &current.0, &current.1));
        let edited: LoadedSidecar = (
            current.0.clone(),
            vec![("a.c".to_string(), "int32 f() { return 1; }".to_string())],
        );
        assert!(!baseline_matches_verified(&edited, &current.0, &current.1));
    }

    #[test]
    fn baseline_sources_include_transitive_local_headers() {
        let files = BTreeMap::from([
            (
                PathBuf::from("project/m.c"),
                "#include \"cap.h\"\nint32 m() { return 0; }".to_string(),
            ),
            (
                PathBuf::from("project/cap.h"),
                "#include \"limits.h\"\ntypedef int32 cap_t;".to_string(),
            ),
            (
                PathBuf::from("project/limits.h"),
                "#define CAP_LIMIT 4".to_string(),
            ),
        ]);
        let loaded = load_baseline_sources(Path::new("project"), "verifying \"m.c\";", |path| {
            Ok(files.get(path).cloned())
        })
        .expect("baseline sources should load")
        .expect("all baseline sources should be present");
        assert_eq!(
            loaded,
            vec![
                (
                    "m.c".to_string(),
                    "#include \"cap.h\"\nint32 m() { return 0; }".to_string()
                ),
                (
                    "cap.h".to_string(),
                    "#include \"limits.h\"\ntypedef int32 cap_t;".to_string()
                ),
                ("limits.h".to_string(), "#define CAP_LIMIT 4".to_string()),
            ]
        );
    }

    #[test]
    fn discovered_sidecars_display_under_the_named_directory() {
        let root = fs::canonicalize("examples").expect("the examples directory should exist");
        let sidecar = root.join("input-cursor").join("input_cursor.click");
        assert_eq!(
            display_path(&sidecar, Path::new("examples")),
            "examples/input-cursor/input_cursor.click"
        );
    }

    #[test]
    fn directory_mode_finds_every_sidecar_in_a_single_project() {
        let selection = select_sidecars(Path::new("examples/input-cursor"))
            .expect("the project should resolve");
        assert_eq!(selection.projects.len(), 1);
        assert!(!selection.projects[0].sidecars.is_empty());
        assert_eq!(selection.project_root, Path::new("examples"));
    }

    /// Writes one sidecar project into a fresh temporary directory and
    /// returns the directory and the sidecar path.
    fn temporary_project(label: &str, c_source: &str, click_source: &str) -> (PathBuf, PathBuf) {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock should be after the Unix epoch")
            .as_nanos();
        let root = env::temp_dir().join(format!(
            "click-verify-{label}-{}-{unique}",
            std::process::id()
        ));
        fs::create_dir_all(&root).expect("temporary verification directory should be creatable");
        fs::write(root.join("program.c"), c_source).expect("C source should be writable");
        let click_path = root.join("program.click");
        fs::write(&click_path, click_source).expect("Click sidecar should be writable");
        (root, click_path)
    }

    /// Program-entry storage is as large as the program's static objects.
    /// Building it (once for the external-dependency summary, then again for
    /// the frontend) once ran before the run's limits were installed and without
    /// a checkpoint, so a 10,000-element zeroed struct pool ran for over an
    /// hour past both the work budget and the ten-minute crash bound. Zeroed
    /// struct arrays are now strided runs, but an explicit initializer list
    /// still stores and partitions one element at a time. Storage charges
    /// and checks per element and per range, inside the run's limits, so the
    /// work budget stops it in that phase, at the same unit on every run.
    #[test]
    fn a_large_program_entry_stops_at_the_work_budget_in_its_storage_phase() {
        let initializers = (0..5000)
            .map(|index| format!("{{{}, 0}}", index % 97))
            .collect::<Vec<_>>()
            .join(", ");
        let (root, click_path) = temporary_project(
            "large-entry",
            &format!(
                "struct node {{ int32 key; struct node *next; }};\n\
                 struct node pool[5000] = {{{initializers}}};\n\
                 int main(void) {{ return pool[0].key; }}\n"
            ),
            "verifying \"program.c\";\n\
             int main() {\n\
                 ensures result == 0;\n\
             } by {\n\
                 execute();\n\
                 simp();\n\
             }\n",
        );
        let run = || {
            entry_with([
                "--work-limit".to_string(),
                "60000".to_string(),
                click_path.display().to_string(),
            ])
            .expect_err("sixty thousand units cannot build a 5,000-element initialized entry")
        };
        // The first run in a process also fills process-wide caches, so it
        // spends a few more units (a fresh `click verify` process always
        // spends the first run's); later runs in one process agree.
        run();
        let first = run();
        let second = run();
        fs::remove_dir_all(&root).expect("temporary verification directory should be removable");
        assert!(
            first.contains("(60000 limit) while running frontend > program-entry storage phase")
                && !first.contains("crash-containment"),
            "{first}"
        );
        assert_eq!(first, second, "a work-budget verdict is deterministic");
    }

    /// The project summary (external dependencies and the selected proof
    /// count) reads function names, signatures, and call graphs. It once
    /// built `main`'s whole program-entry storage too and dropped it, which
    /// doubled the setup cost of a program with large static objects. It now
    /// enters no program-entry storage phase, and beyond resolving the
    /// sources it spends the same work whatever a static array's
    /// initializer holds, while verification still builds that storage.
    #[test]
    fn the_project_summary_builds_no_program_entry_storage() {
        use click::instrumentation::{VerificationEvent, collect, measure_deterministic_work};
        let costs = [100usize, 2000].map(|elements| {
            let initializers = (0..elements)
                .map(|index| format!("{{{}, 0}}", index % 97))
                .collect::<Vec<_>>()
                .join(", ");
            let (root, click_path) = temporary_project(
                "summary-entry",
                &format!(
                    "struct node {{ int32 key; struct node *next; }};\n\
                     struct node pool[{elements}] = {{{initializers}}};\n\
                     int main(void) {{ return pool[0].key; }}\n"
                ),
                "verifying \"program.c\";\n\
                 int main() {\n\
                     ensures result == 0;\n\
                 } by {\n\
                     execute();\n\
                     simp();\n\
                 }\n",
            );
            let LoadedTarget {
                project, inputs, ..
            } = load_target_inputs(&click_path, Some(&root)).expect("the project loads");
            let CInput::Bundle(sources) = &inputs else {
                panic!("a plain C project is a source bundle");
            };
            let refs = source_refs(sources);
            // Warm the process-wide caches so both sizes are measured alike.
            click::surface::c0_project_function_names(&project, &refs)
                .expect("the sources resolve");
            let ((summary, summary_events), summary_work) =
                measure_deterministic_work(|| collect(|| c0_project_summary(&project, &refs)));
            let (resolution, resolution_work) = measure_deterministic_work(|| {
                click::surface::c0_project_function_names(&project, &refs)
            });
            let (verified, verify_events) = collect(|| verify_c0_project(&project, &refs));
            fs::remove_dir_all(&root)
                .expect("temporary verification directory should be removable");
            let summary = summary.expect("the summary resolves");
            resolution.expect("the sources resolve");
            verified.expect("the program verifies");
            let builds_storage = |events: &[VerificationEvent]| {
                events.iter().any(|event| {
                    matches!(
                        event,
                        VerificationEvent::PhaseStarted("program-entry storage")
                    )
                })
            };
            assert!(
                !builds_storage(&summary_events),
                "the summary built entry storage"
            );
            assert!(
                builds_storage(&verify_events),
                "verification builds entry storage"
            );
            assert_eq!(summary.selected_proof_count, 1);
            assert!(summary.external_dependencies.is_empty());
            summary_work as i64 - resolution_work as i64
        });
        assert_eq!(
            costs[0], costs[1],
            "beyond resolution, the summary's work grew with the initializer: {costs:?}"
        );
    }

    /// The crash-containment bound is installed before the run loads its
    /// sources, so even the first C parse, for the external-dependency
    /// summary, stops at a checkpoint once the bound has expired.
    #[test]
    fn the_crash_bound_covers_source_loading_and_parsing() {
        let functions = (0..4000)
            .map(|index| format!("int32 f{index}(int32 x) {{ return x; }}\n"))
            .collect::<String>();
        let (root, click_path) = temporary_project(
            "slow-frontend",
            &functions,
            "verifying \"program.c\";\n\
             int32 f0(int32 x) {\n\
                 ensures result == x;\n\
             } by {\n\
                 execute();\n\
                 simp();\n\
             }\n",
        );
        let error = entry_with([
            "--time-limit".to_string(),
            "1ms".to_string(),
            click_path.display().to_string(),
        ])
        .expect_err("one millisecond cannot parse four thousand functions");
        fs::remove_dir_all(&root).expect("temporary verification directory should be removable");
        assert!(
            error.starts_with("click verify was stopped after")
                && error.contains("by the 1ms wall-clock crash-containment bound")
                && error.contains("C parsing stopped")
                && error.contains(
                    "external dependency summary > source resolution phase, stopped by the 1ms"
                ),
            "{error}"
        );
    }

    #[test]
    fn verify_accepts_realloc_as_a_builtin() {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock should be after the Unix epoch")
            .as_nanos();
        let root = env::temp_dir().join(format!(
            "click-verify-realloc-{}-{unique}",
            std::process::id()
        ));
        fs::create_dir_all(&root).expect("temporary verification directory should be creatable");
        fs::write(
            root.join("realloc.c"),
            "int32 realloc_preserves_calloc_prefix() {\n\
                int32* p = calloc(2, sizeof(int32));\n\
                if (p == 0) { return -1; }\n\
                int32* q = realloc(p, 3 * sizeof(int32));\n\
                if (q == 0) { free(p); return -1; }\n\
                int32 result = q[1];\n\
                free(q);\n\
                return result;\n\
            }\n",
        )
        .expect("C source should be writable");
        let click_path = root.join("realloc.click");
        fs::write(
            &click_path,
            "verifying \"realloc.c\";\n\
                int32 realloc_preserves_calloc_prefix() {\n\
                    ensures result == 0 or result == -1 by auto;\n\
                }\n",
        )
        .expect("Click sidecar should be writable");

        let result = entry_with([click_path.display().to_string()]);
        fs::remove_dir_all(&root).expect("temporary verification directory should be removable");
        assert!(
            result.is_ok(),
            "click verify should accept realloc: {result:?}"
        );
    }

    #[test]
    fn corrupted_or_mismatched_incremental_markers_are_cache_misses() {
        let path = Path::new("examples/sample.click");
        let valid = marker_contents(
            "abc123",
            path,
            "verifier-a",
            &environment_switches(),
            CTarget::SUPPORTED,
        );
        assert!(valid_marker(
            &valid,
            "abc123",
            path,
            "verifier-a",
            CTarget::SUPPORTED
        ));
        let other_target = valid.replace("target=x86_64-linux-kernel", "target=another-target");
        assert!(!valid_marker(
            &other_target,
            "abc123",
            path,
            "verifier-a",
            CTarget::SUPPORTED
        ));
        // The same sources under another selected target are a cache miss.
        assert!(!valid_marker(
            &valid,
            "abc123",
            path,
            "verifier-a",
            CTarget::X86_64LinuxUserspace
        ));
        assert!(!valid_marker(
            "truncated",
            "abc123",
            path,
            "verifier-a",
            CTarget::SUPPORTED
        ));
        assert!(!valid_marker(
            &valid,
            "different",
            path,
            "verifier-a",
            CTarget::SUPPORTED
        ));
        assert!(!valid_marker(
            &valid,
            "abc123",
            path,
            "verifier-b",
            CTarget::SUPPORTED
        ));
        assert!(!valid_marker(
            &valid,
            "abc123",
            Path::new("examples/other.click"),
            "verifier-a",
            CTarget::SUPPORTED
        ));
        // A marker written under a verifier switch this process does not have
        // set is a cache miss as well.
        let other_switches = format!(
            "{}env=CLICK_DISABLE_TACTIC_BUDGETS=1\n",
            environment_switches()
        );
        let attested_elsewhere = marker_contents(
            "abc123",
            path,
            "verifier-a",
            &other_switches,
            CTarget::SUPPORTED,
        );
        assert!(!valid_marker(
            &attested_elsewhere,
            "abc123",
            path,
            "verifier-a",
            CTarget::SUPPORTED
        ));
    }
}
