//! Structured context retained by proof-step failures.
//!
//! The semantic proof state is kept behind an opaque, shared provider.  This
//! keeps constructing an error cheap while allowing the terminal renderer to
//! inspect only the focused goal and bounded premise view when a human asks
//! for the error message.

use crate::kernel::Proposition;
use std::sync::Arc;

pub(crate) mod render;

/// The history result retained while the failing proof's verification session
/// is active. Formatting must not rerun the walk under a different session or
/// bridging mode, nor recover the write width from a later arena.
#[derive(Clone)]
pub(crate) struct MemoryHistoryDiagnostic {
    pub explanation: crate::kernel::resource_tracker::Explanation,
    pub written_bytes: Option<u32>,
}

impl MemoryHistoryDiagnostic {
    pub(crate) fn capture(explanation: crate::kernel::resource_tracker::Explanation) -> Self {
        let written_bytes = explanation
            .outcome
            .blocking_step()
            .and_then(|(at, _)| at)
            .and_then(|at| at.snapshot().derivation())
            .and_then(|derivation| match derivation.as_ref() {
                crate::kernel::CMemoryDerivation::Store { value, .. } => {
                    Some(value.c_type().byte_width())
                }
                _ => None,
            });
        Self {
            explanation,
            written_bytes,
        }
    }
}

/// A lazily inspectable proof state. Implementations retain a persistent proof
/// handle rather than cloning the goal, environment, or derivation history.
pub(crate) trait ProofDiagnosticState: Send + Sync {
    fn register_names(&self, _labels: &mut render::SnapshotLabels) {}

    fn failed_requirement(&self) -> Option<(&str, &Proposition)> {
        None
    }

    fn rejected_resource_fact(&self) -> Option<&crate::kernel::proof::RejectedResourceRewriteFact> {
        None
    }

    /// The instance a refused `fold` proposed, when its resource declares no
    /// field and keeps its children's fields in a hidden record.
    fn proposed_hidden_record(&self) -> Option<&crate::kernel::ResourceInstance> {
        None
    }

    fn memory_history(&self) -> Option<&MemoryHistoryDiagnostic> {
        None
    }

    fn read_resolutions(&self) -> &[crate::kernel::ReadResolutionDiagnostic] {
        &[]
    }

    fn proof_context_kind(&self) -> Option<&str> {
        None
    }

    fn resources(&self) -> &[crate::kernel::CResourceFact] {
        &[]
    }

    fn kernel_goal(&self) -> Option<&Proposition>;
    fn premises(&self, limit: usize) -> Vec<&Proposition>;
    fn premise_count(&self) -> usize;
    fn proof_trace(
        &self,
        _claim: &str,
        _labels: &mut render::SnapshotLabels,
        _tactic_location: &dyn Fn(&[usize]) -> Option<(String, crate::source::SourcePosition)>,
        _branch_arm: &dyn Fn(&[usize], &crate::source::SourcePosition) -> Option<usize>,
        _have_body_contains: &dyn Fn(&[usize], &crate::source::SourcePosition) -> bool,
        _target: Option<&crate::source::SourcePosition>,
    ) -> Option<String> {
        None
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ProofDiagnosticOrigin {
    pub stage: String,
    pub location: String,
    /// Written outer tactic and each nested `have`/`open` body position.
    pub source_tactic_path: Option<Vec<usize>>,
}

#[derive(Clone)]
pub(crate) struct ProofFailureDiagnostic {
    pub origin: ProofDiagnosticOrigin,
    pub claim_label: String,
    pub reason: String,
    pub checks: Option<Arc<CheckObservations>>,
    pub state: Option<Arc<dyn ProofDiagnosticState>>,
}

/// Bounded observations of queries actually executed by one written check.
/// They are diagnostic records, including speculative search, never premises.
#[derive(Clone)]
pub(crate) struct CheckObservations {
    pub reads: Vec<crate::kernel::ReadResolutionDiagnostic>,
    pub walks: Vec<crate::kernel::TransportCellWalkDiagnostic>,
}

pub(crate) fn capture_check_observations<T>(run: impl FnOnce() -> T) -> (T, CheckObservations) {
    crate::kernel::with_bounded_cell_walk_diagnostics(|| {
        let (result, reads) = crate::kernel::capture_read_resolutions(run);
        let walks = crate::kernel::take_transport_cell_walk_diagnostics();
        (result, CheckObservations { reads, walks })
    })
}

pub(crate) fn render_check_observations(
    checks: &CheckObservations,
    labels: &mut render::SnapshotLabels,
    traced: bool,
) -> String {
    let limit = if traced { 16 } else { 2 };
    let mut result =
        String::from("checks observed during the failed attempt (queries, not established facts):");
    for read in checks.reads.iter().take(limit) {
        result.push_str("\n  ");
        if traced {
            result.push_str(&render::render_read_resolution(read, labels));
        } else {
            result.push_str(&format!(
                "read-value check: {}; recovered value {}; comparison {}",
                read.reason,
                if read.recovered.is_some() {
                    "available"
                } else {
                    "not recovered"
                },
                if read.equal { "proved" } else { "not proved" }
            ));
        }
    }
    for walk in checks.walks.iter().take(limit) {
        result.push_str("\n  cell walk: ");
        if traced {
            result.push_str(&render::render_transport_cell_walk(walk, labels));
        } else {
            result.push_str(&format!(
                "{}-byte read; {}; from {} to {}",
                walk.bytes,
                walk.reason,
                labels.state_phrase(walk.start.memory()),
                labels.state_phrase(walk.stopped_at.memory())
            ));
        }
    }
    if checks.reads.is_empty() && checks.walks.is_empty() {
        result.push_str("\n  no instrumented memory query was recorded; the failure may precede a cell walk or use another rule");
    }
    if checks.reads.len() > limit || checks.walks.len() > limit {
        result.push_str("\n  … additional observations omitted");
    }
    if checks.reads.len() >= 16 || checks.walks.len() >= 16 {
        result.push_str("\n  capture limited to 16 distinct cell walks and 16 read queries");
    }
    result
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ProofSearchFailure {
    pub strategy: String,
    pub reason: String,
    pub kind: String,
    pub diagnostic: Option<Arc<ProofFailureDiagnostic>>,
}

impl ProofFailureDiagnostic {
    pub(crate) fn kernel_goal(&self) -> Option<&Proposition> {
        self.state.as_ref()?.kernel_goal()
    }

    pub(crate) fn premises(&self, limit: usize) -> Vec<&Proposition> {
        self.state
            .as_ref()
            .map_or_else(Vec::new, |state| state.premises(limit))
    }

    pub(crate) fn premise_count(&self) -> usize {
        self.state.as_ref().map_or(0, |state| state.premise_count())
    }
}

impl std::fmt::Debug for ProofFailureDiagnostic {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ProofFailureDiagnostic")
            .field("origin", &self.origin)
            .field("claim_label", &self.claim_label)
            .field("reason", &self.reason)
            .finish_non_exhaustive()
    }
}

impl PartialEq for ProofFailureDiagnostic {
    fn eq(&self, other: &Self) -> bool {
        self.origin == other.origin
            && self.claim_label == other.claim_label
            && self.reason == other.reason
            && match (&self.checks, &other.checks) {
                (None, None) => true,
                (Some(left), Some(right)) => Arc::ptr_eq(left, right),
                _ => false,
            }
            && match (&self.state, &other.state) {
                (None, None) => true,
                (Some(left), Some(right)) => Arc::ptr_eq(left, right),
                _ => false,
            }
    }
}

impl Eq for ProofFailureDiagnostic {}

/// Requirements use exactly the same proposition policy as facts and goals.
pub(crate) fn render_failed_requirement(
    state: &dyn ProofDiagnosticState,
    labels: &mut render::SnapshotLabels,
) -> String {
    state.register_names(labels);
    let mut result = String::new();
    if let Some((label, proposition)) = state.failed_requirement() {
        result = format!(
            "{label}: {}",
            render::render_proposition_labeled(proposition, labels)
        );
        // The body fact of a resource without fields reads its hidden
        // record; show the record the fold proposed, in the same labels.
        if let Some(instance) = state.proposed_hidden_record()
            && let Some(record) = render::render_hidden_record_instance_labeled(
                instance.name(),
                instance.arguments(),
                instance.schema().fields(),
                instance.fields(),
                labels,
            )
        {
            result.push_str("\nproposed fold: ");
            result.push_str(&record);
        }
    }
    if let Some(refusal) = state.rejected_resource_fact() {
        if !result.is_empty() {
            result.push('\n');
        }
        result.push_str("rejected fact: ");
        result.push_str(&render::render_proposition_labeled(
            &refusal.rejected,
            labels,
        ));
        result.push_str("\nallowed facts from the checked resource body:");
        if refusal.allowed.is_empty() {
            result.push_str(" none");
        }
        for fact in refusal.allowed.iter().take(12) {
            result.push_str("\n  ");
            result.push_str(&render::render_proposition_labeled(fact, labels));
        }
        if refusal.allowed.len() > 12 {
            let count = refusal.allowed.len() - 12;
            let noun = if count == 1 { "fact" } else { "facts" };
            result.push_str(&format!("\n  … {count} more allowed {noun}"));
        }
    }
    result
}

pub(crate) fn render_terminal_message(
    summary: &str,
    diagnostic: &ProofFailureDiagnostic,
    search_failures: &[ProofSearchFailure],
) -> String {
    render_terminal_message_labeled(
        summary,
        diagnostic,
        search_failures,
        &mut render::SnapshotLabels::ambient(),
    )
}

pub(crate) fn render_terminal_message_labeled(
    summary: &str,
    diagnostic: &ProofFailureDiagnostic,
    search_failures: &[ProofSearchFailure],
    labels: &mut render::SnapshotLabels,
) -> String {
    render_diagnostic_labeled(Some(summary), diagnostic, search_failures, labels)
}

pub(crate) fn render_trace_context_labeled(
    diagnostic: &ProofFailureDiagnostic,
    search_failures: &[ProofSearchFailure],
    labels: &mut render::SnapshotLabels,
) -> String {
    let _typed = crate::surface::proof_diagnostics::render::TypedNotationScope::enter();
    render_diagnostic_labeled(None, diagnostic, search_failures, labels)
}

fn render_diagnostic_labeled(
    summary: Option<&str>,
    diagnostic: &ProofFailureDiagnostic,
    search_failures: &[ProofSearchFailure],
    labels: &mut render::SnapshotLabels,
) -> String {
    if let Some(state) = &diagnostic.state {
        state.register_names(labels);
    }
    // Keep the established summary as the first line. The richer context is
    // deliberately bounded and rendered only at this terminal boundary.
    let mut rendered = summary.unwrap_or_default().to_owned();
    if summary.is_none() {
        rendered.push_str("failed check:\n  ");
        rendered.push_str(&diagnostic.reason);
        rendered.push_str("\n  stage: ");
        rendered.push_str(&diagnostic.origin.stage);
        rendered.push_str("\n  location: ");
        rendered.push_str(&diagnostic.origin.location);
    }
    if summary.is_none()
        && let Some(kind) = diagnostic
            .state
            .as_ref()
            .and_then(|state| state.proof_context_kind())
    {
        rendered.push_str("\n  proof context: ");
        rendered.push_str(kind);
    }
    if summary.is_none()
        && let Some(state) = &diagnostic.state
    {
        let resources = state.resources();
        rendered.push_str(&format!(
            "\n  resources at the failed check (showing {} of {}):",
            resources.len().min(12),
            resources.len()
        ));
        for fact in resources.iter().take(12) {
            rendered.push_str("\n    ");
            rendered.push_str(&render::render_resource_fact_labeled(fact, labels));
        }
        if resources.len() > 12 {
            rendered.push_str("\n    … additional resources omitted");
        }
    }
    if summary.is_some() {
        rendered.push_str("\n  stage: ");
        rendered.push_str(&diagnostic.origin.stage);
        rendered.push_str("\n  location: ");
        rendered.push_str(&diagnostic.origin.location);
    }
    // One label map for the whole report. Rendering the goal and each premise
    // with a map of its own made `snapshot#1` mean a different memory on every
    // line, so a premise that reads exactly like the goal could be about
    // another state entirely — which is the one thing a reader compares these
    // lines to decide.
    if let Some(state) = &diagnostic.state {
        let requirement = render_failed_requirement(state.as_ref(), labels);
        if !requirement.is_empty() {
            rendered.push_str("\n  ");
            rendered.push_str(&requirement);
        }
    }
    if let Some(goal) = diagnostic.kernel_goal() {
        rendered.push_str("\n  goal: ");
        rendered.push_str(&render::render_proposition_labeled(goal, labels));
        if let Some(history) = diagnostic
            .state
            .as_ref()
            .and_then(|state| state.memory_history())
            && let Some(history) = render::render_memory_history_check(history, labels)
        {
            rendered.push_str("\n  ");
            rendered.push_str(&history);
        }
    }
    if let Some(state) = &diagnostic.state {
        for resolution in state.read_resolutions() {
            rendered.push_str("\n  ");
            rendered.push_str(&render::render_read_resolution(resolution, labels));
        }
    }
    let premises = diagnostic.premises(if summary.is_some() { 8 } else { 16 });
    if !premises.is_empty() {
        let heading = if summary.is_some() {
            "recent premises"
        } else {
            "available premises at the failed check"
        };
        rendered.push_str(&format!(
            "\n  {heading} (showing {} of {}):",
            premises.len(),
            diagnostic.premise_count()
        ));
        for premise in &premises {
            rendered.push_str("\n    ");
            rendered.push_str(&render::render_proposition_labeled(premise, labels));
        }
    }
    if diagnostic.premise_count() > premises.len() {
        rendered.push_str("\n    … <additional premises omitted>");
    }
    if let Some(checks) = &diagnostic.checks
        && (summary.is_none() || !checks.reads.is_empty() || !checks.walks.is_empty())
    {
        rendered.push_str("\n  ");
        rendered.push_str(&render_check_observations(
            checks,
            labels,
            summary.is_none(),
        ));
    }
    if !search_failures.is_empty() {
        rendered.push_str("\n  search candidates:");
        for failure in search_failures.iter().take(8) {
            rendered.push_str("\n    ");
            rendered.push_str(&failure.strategy);
            rendered.push_str(" [");
            rendered.push_str(&failure.kind);
            rendered.push_str("]: ");
            rendered.push_str(&failure.reason);
            if let Some(state) = failure
                .diagnostic
                .as_ref()
                .and_then(|diagnostic| diagnostic.state.as_ref())
            {
                let requirement = render_failed_requirement(state.as_ref(), labels);
                if !requirement.is_empty() {
                    rendered.push_str("; ");
                    rendered.push_str(&requirement);
                }
            }
            if failure.kind == "UnclosedGoal"
                && let Some(goal) = failure
                    .diagnostic
                    .as_ref()
                    .and_then(|diagnostic| diagnostic.kernel_goal())
            {
                rendered.push_str("; goal: ");
                rendered.push_str(&render::render_proposition_labeled(goal, labels));
            }
        }
        if search_failures.len() > 8 {
            rendered.push_str("\n    … <additional search candidates omitted>");
        }
    }
    if summary.is_some() && !crate::surface::proof_trace::enabled_for(&diagnostic.claim_label) {
        rendered.push_str(&labels.trace_legend());
    }
    const MAX_REPORT_BYTES: usize = 64 * 1024;
    if rendered.len() > MAX_REPORT_BYTES {
        let mut end = MAX_REPORT_BYTES.saturating_sub("\n… <proof diagnostic truncated>".len());
        while end > 0 && !rendered.is_char_boundary(end) {
            end -= 1;
        }
        rendered.truncate(end);
        rendered.push_str("\n… <proof diagnostic truncated>");
    }
    if summary.is_none() {
        // The trace is a separate section after the ordinary CLI error. Keep
        // its nested hierarchy, but remove the old report-wide indentation.
        rendered = rendered
            .trim_start_matches('\n')
            .lines()
            .map(|line| line.strip_prefix("  ").unwrap_or(line))
            .collect::<Vec<_>>()
            .join("\n");
    }
    rendered
}

pub(crate) fn render_search_failures(summary: &str, failures: &[ProofSearchFailure]) -> String {
    let mut labels = render::SnapshotLabels::default();
    let mut rendered = summary.to_owned();
    rendered.push_str("\n  search candidates:");
    for failure in failures.iter().take(8) {
        rendered.push_str("\n    ");
        rendered.push_str(&failure.strategy);
        rendered.push_str(" [");
        rendered.push_str(&failure.kind);
        rendered.push_str("]: ");
        rendered.push_str(&failure.reason);
        if let Some(state) = failure
            .diagnostic
            .as_ref()
            .and_then(|diagnostic| diagnostic.state.as_ref())
        {
            let requirement = render_failed_requirement(state.as_ref(), &mut labels);
            if !requirement.is_empty() {
                rendered.push_str("; ");
                rendered.push_str(&requirement);
            }
        }

        if let Some(goal) = failure
            .diagnostic
            .as_ref()
            .and_then(|diagnostic| diagnostic.kernel_goal())
        {
            rendered.push_str("; goal: ");
            rendered.push_str(&render::render_proposition_labeled(goal, &mut labels));
        }
    }
    if failures.len() > 8 {
        rendered.push_str("\n    … <additional search candidates omitted>");
    }
    const MAX_REPORT_BYTES: usize = 64 * 1024;
    if rendered.len() > MAX_REPORT_BYTES {
        let mut end = MAX_REPORT_BYTES.saturating_sub("\n… <proof diagnostic truncated>".len());
        while end > 0 && !rendered.is_char_boundary(end) {
            end -= 1;
        }
        rendered.truncate(end);
        rendered.push_str("\n… <proof diagnostic truncated>");
    }
    rendered
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    struct CountingState {
        goal: Proposition,
        calls: AtomicUsize,
    }

    impl ProofDiagnosticState for CountingState {
        fn kernel_goal(&self) -> Option<&Proposition> {
            self.calls.fetch_add(1, Ordering::Relaxed);
            Some(&self.goal)
        }
        fn premises(&self, limit: usize) -> Vec<&Proposition> {
            self.calls.fetch_add(1, Ordering::Relaxed);
            vec![&self.goal][..limit.min(1)].to_vec()
        }
        fn premise_count(&self) -> usize {
            3
        }
    }

    #[test]
    fn rejected_read_prerequisite_uses_the_shared_snapshot_legend() {
        use crate::kernel::{CMemory, CType, Pointer, Variable};
        struct Rejected(Proposition);
        impl ProofDiagnosticState for Rejected {
            fn failed_requirement(&self) -> Option<(&str, &Proposition)> {
                Some(("unproved prerequisite", &self.0))
            }
            fn kernel_goal(&self) -> Option<&Proposition> {
                None
            }
            fn premises(&self, _: usize) -> Vec<&Proposition> {
                Vec::new()
            }
            fn premise_count(&self) -> usize {
                0
            }
        }
        let state = Rejected(Proposition::CMemoryReadDefined {
            memory: CMemory::new(),
            pointer: Pointer::symbolic(Variable(987_001)),
            value_type: CType::Int32,
        });
        let mut labels = render::SnapshotLabels::default();
        let report = render_failed_requirement(&state, &mut labels);
        assert!(report.contains("unproved prerequisite"), "{report}");
        assert!(
            report.contains("defined(at(<state A>, *<pointer A>))"),
            "{report}"
        );
        let legend = labels.trace_legend();
        assert!(legend.contains("<state A> is "), "{legend}");
        assert!(
            !report.contains("unsupported conditional proof"),
            "{report}"
        );
    }

    #[test]
    fn rejected_resource_fact_uses_one_printer_and_snapshot_legend() {
        let _typed = render::TypedNotationScope::enter();
        use crate::kernel::{CMemory, CType, Pointer, Variable};
        struct Rejected(crate::kernel::proof::RejectedResourceRewriteFact);
        impl ProofDiagnosticState for Rejected {
            fn rejected_resource_fact(
                &self,
            ) -> Option<&crate::kernel::proof::RejectedResourceRewriteFact> {
                Some(&self.0)
            }
            fn kernel_goal(&self) -> Option<&Proposition> {
                None
            }
            fn premises(&self, _: usize) -> Vec<&Proposition> {
                vec![]
            }
            fn premise_count(&self) -> usize {
                0
            }
        }
        let read = |memory| Proposition::CMemoryReadDefined {
            memory,
            pointer: Pointer::symbolic(Variable(987_002)),
            value_type: CType::Int32,
        };
        let rejected = read(CMemory::new());
        let allowed = read(CMemory::new().with_block("changed", 4));
        let state = Rejected(crate::kernel::proof::RejectedResourceRewriteFact {
            rejected: rejected.clone(),
            allowed: vec![allowed.clone(); 13].into(),
        });
        let mut labels = render::SnapshotLabels::default();
        let report = render_failed_requirement(&state, &mut labels);
        assert!(
            report.starts_with(&format!(
                "rejected fact: {}",
                render::render_proposition_labeled(&rejected, &mut labels)
            )),
            "{report}"
        );
        assert!(
            report.contains(&render::render_proposition_labeled(&allowed, &mut labels)),
            "{report}"
        );
        assert!(
            report.contains("snapshot#1") && report.contains("snapshot#2"),
            "{report}"
        );
        assert!(report.contains("1 more allowed fact"), "{report}");
        let legend = labels.trace_legend();
        assert!(
            legend.contains("snapshot#1 =") && legend.contains("snapshot#2 ="),
            "{legend}"
        );
    }

    #[test]
    fn rendering_is_the_boundary_that_visits_retained_context() {
        let state = Arc::new(CountingState {
            goal: Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(true), true),
            calls: AtomicUsize::new(0),
        });
        let diagnostic = ProofFailureDiagnostic {
            checks: None,
            origin: ProofDiagnosticOrigin {
                stage: "proof step".into(),
                location: "source tactic 4".into(),
                source_tactic_path: None,
            },
            claim_label: "claim".into(),
            reason: "reason".into(),
            state: Some(state.clone()),
        };
        assert_eq!(state.calls.load(Ordering::Relaxed), 0);
        let report = render_terminal_message("reason", &diagnostic, &[]);
        assert!(report.contains("stage: proof step"));
        assert!(report.contains("additional premises omitted"));
        assert!(state.calls.load(Ordering::Relaxed) >= 2);
    }

    #[test]
    fn trace_context_retains_a_refined_integer_goal_without_a_source_spelling() {
        use crate::kernel::{
            Bitvector32Term, ConditionTerm, IntegerTerm, MachineIntegerType, Variable,
        };
        let goal = Proposition::ConditionIs(
            ConditionTerm::integer_equal(
                IntegerTerm::from_machine(
                    MachineIntegerType::Int32,
                    Bitvector32Term::Variable(Variable(981_701)),
                )
                .unwrap(),
                IntegerTerm::constant_i64(7),
            ),
            true,
        );
        let state = Arc::new(CountingState {
            goal,
            calls: AtomicUsize::new(0),
        });
        let diagnostic = ProofFailureDiagnostic {
            checks: None,
            origin: ProofDiagnosticOrigin {
                stage: "proof step".into(),
                location: "source tactic 4".into(),
                source_tactic_path: None,
            },
            claim_label: "word.contract".into(),
            reason: "reason".into(),
            state: Some(state),
        };
        crate::surface::with_proof_trace("word", || {
            let report = render_trace_context_labeled(
                &diagnostic,
                &[],
                &mut render::SnapshotLabels::default(),
            );
            assert!(report.contains("machine-integer<Int32>"), "{report}");
            assert_eq!(
                report.matches("machine-integer<Int32>").count(),
                2,
                "{report}"
            );
            assert_eq!(
                report
                    .lines()
                    .filter(|line| line.starts_with("goal:"))
                    .count(),
                1,
                "{report}"
            );
            assert!(
                report.contains("available premises at the failed check"),
                "{report}"
            );
            assert!(report.len() < 2048, "{report}");
        });
    }

    #[test]
    fn click_error_lazily_caches_and_preserves_structured_context() {
        let state = Arc::new(CountingState {
            goal: Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(true), true),
            calls: AtomicUsize::new(0),
        });
        let diagnostic = ProofFailureDiagnostic {
            checks: None,
            origin: ProofDiagnosticOrigin {
                stage: "step".into(),
                location: "source tactic 44".into(),
                source_tactic_path: None,
            },
            claim_label: "claim".into(),
            reason: "failed".into(),
            state: Some(state.clone()),
        };
        let error = crate::surface::ClickError::with_diagnostic("failed", diagnostic);
        assert_eq!(state.calls.load(Ordering::Relaxed), 0);
        let first = error.message().to_owned();
        let after_first = state.calls.load(Ordering::Relaxed);
        assert_eq!(first, error.message());
        assert_eq!(after_first, state.calls.load(Ordering::Relaxed));
        let wrapped = error.clone().with_context("outer");
        assert!(wrapped.diagnostic().is_some());
        assert!(wrapped.message().contains("outer"));
    }

    #[test]
    fn reported_trace_uses_the_goals_snapshot_labels() {
        use crate::kernel::{Bitvector32Term, CMemory, Pointer, PointerBlock, PointerOffsetTerm};

        struct TracedState(Proposition);
        impl ProofDiagnosticState for TracedState {
            fn kernel_goal(&self) -> Option<&Proposition> {
                Some(&self.0)
            }
            fn premises(&self, _limit: usize) -> Vec<&Proposition> {
                Vec::new()
            }
            fn premise_count(&self) -> usize {
                0
            }
            fn proof_trace(
                &self,
                claim: &str,
                labels: &mut render::SnapshotLabels,
                tactic_location: &dyn Fn(
                    &[usize],
                )
                    -> Option<(String, crate::source::SourcePosition)>,
                branch_arm: &dyn Fn(&[usize], &crate::source::SourcePosition) -> Option<usize>,
                have_body_contains: &dyn Fn(&[usize], &crate::source::SourcePosition) -> bool,
                target: Option<&crate::source::SourcePosition>,
            ) -> Option<String> {
                crate::surface::proof_trace::render(
                    claim,
                    &[crate::surface::proof_trace::TracePathNode {
                        node: 1,
                        selected_arm: None,
                    }],
                    labels,
                    tactic_location,
                    branch_arm,
                    have_body_contains,
                    target,
                )
            }
        }
        let at = |memory| Proposition::CMemoryLoadable {
            memory,
            base: Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0),
            },
            bytes: Bitvector32Term::Constant(1),
            wide: false,
        };
        crate::surface::with_proof_trace("f", || {
            let memory = CMemory::new().with_block("shared", 1);
            crate::surface::proof_trace::record(
                1,
                crate::surface::proof_trace::TraceStep {
                    header: "\n    source tactic 0: step".into(),
                    source_tactic_path: None,
                    call_source: None,
                    facts: vec![crate::surface::proof_trace::TraceFact {
                        kernel: at(memory.clone()),
                    }],
                    more_facts: 0,
                    frontier: None,
                    load: None,
                    read_equalities: Vec::new(),
                    read_context_changed: false,
                    transport: None,
                    resources: Vec::new(),
                    more_resources: 0,
                },
            );
            let diagnostic = ProofFailureDiagnostic {
                checks: None,
                origin: ProofDiagnosticOrigin {
                    stage: "proof step".into(),
                    location: "source tactic 1".into(),
                    source_tactic_path: None,
                },
                claim_label: "f.contract".into(),
                reason: "failed".into(),
                state: Some(Arc::new(TracedState(at(memory)))),
            };
            let report = crate::surface::ClickError::with_diagnostic("failed", diagnostic).report();
            assert!(
                report.contains("goal: viewable(memory=snapshot#1"),
                "{report}"
            );
            assert!(
                report.contains("adds: viewable(memory=snapshot#1"),
                "{report}"
            );
        });
    }

    #[test]
    fn search_only_reports_are_utf8_safe_and_bounded() {
        let failures = (0..32)
            .map(|index| ProofSearchFailure {
                strategy: format!("策略 {index}"),
                reason: "失敗🙂".repeat(20_000),
                kind: "rejected".into(),
                diagnostic: None,
            })
            .collect::<Vec<_>>();
        let report = render_search_failures("failed", &failures);
        assert!(report.len() <= 64 * 1024);
        assert!(report.contains("proof diagnostic truncated"));
        assert!(report.is_char_boundary(report.len()));
    }

    #[test]
    fn terminal_search_report_renders_unclosed_goal_lazily() {
        let state = Arc::new(CountingState {
            goal: Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(true), true),
            calls: AtomicUsize::new(0),
        });
        let diagnostic = Arc::new(ProofFailureDiagnostic {
            checks: None,
            origin: ProofDiagnosticOrigin {
                stage: "proof step".into(),
                location: "loop closure".into(),
                source_tactic_path: None,
            },
            claim_label: "claim".into(),
            reason: "leaf remained open".into(),
            state: Some(state),
        });
        let report = render_terminal_message(
            "closure failed",
            &ProofFailureDiagnostic {
                checks: None,
                origin: ProofDiagnosticOrigin {
                    stage: "proof step".into(),
                    location: "loop closure".into(),
                    source_tactic_path: None,
                },
                claim_label: "claim".into(),
                reason: "closure failed".into(),
                state: None,
            },
            &[ProofSearchFailure {
                strategy: "loop invariant bundle leaf".into(),
                reason: "leaf remained open".into(),
                kind: "UnclosedGoal".into(),
                diagnostic: Some(diagnostic),
            }],
        );
        assert!(report.contains("[UnclosedGoal]"));
        assert!(report.contains("goal: true"));
    }
}
