//! Opt-in, bounded observations of checked proof steps for CLI diagnostics.
//! The trace is diagnostic only; no recorded text participates in checking.

use crate::kernel::ContractPathPreparationFailure;
use crate::kernel::proof::BranchId;
use crate::kernel::{Bitvector32Term, ConditionTerm, Pointer, Proposition, SharedCMemory};
use crate::source::SourcePosition;
use crate::surface::proof_diagnostics::ProofDiagnosticState;
use crate::surface::proof_diagnostics::render::{self, SnapshotLabels};
use std::any::Any;
use std::cell::RefCell;
use std::collections::HashMap;

pub(super) const MAX_STEPS: usize = 2048;
const MAX_RENDER_BYTES: usize = 64 * 1024;

struct Capture {
    function: String,
    steps: HashMap<usize, TraceStep>,
    branches: HashMap<usize, TraceBranch>,
    joins: HashMap<usize, TraceJoin>,
    bodies: HashMap<usize, TraceBody>,
    scope_parents: HashMap<usize, TraceScope>,
    retained_paths: Vec<TraceRetainedPath>,
    limit_reached: bool,
}

struct TraceRetainedPath {
    claim: String,
    completed: bool,
    /// A loop phase's path, recorded while the function's own
    /// path is still being driven. It is rendered only for a target that
    /// lies on it; a plain trace shows the function's path.
    nested: bool,
    path_index: usize,
    lineage: Vec<TracePathNode>,
    /// Retain the checked provenance chain until the CLI has rendered it.
    _retained: Box<dyn Any>,
}

#[derive(Clone, Copy)]
pub(super) struct TracePathNode {
    pub node: usize,
    pub selected_arm: Option<BranchId>,
}

pub(super) struct TraceJoin {
    pub marker: usize,
    pub arms: [Vec<TracePathNode>; 2],
    pub facts: Vec<TraceFact>,
    pub more_facts: usize,
    /// One arm ran the source continuation before a terminal join.
    pub continuation_arm: Option<usize>,
    /// Keeps arm provenance alive so later proof attempts cannot recycle its
    /// pointer identities.
    pub _retained: Box<dyn Any>,
}

struct TraceScope {
    lineage: Vec<TracePathNode>,
    _retained: Box<dyn Any>,
}

pub(super) struct TraceBody {
    pub lineage: Vec<TracePathNode>,
    pub _retained: Box<dyn Any>,
}

pub(super) struct TraceBranch {
    pub header: String,
    pub source_tactic_path: Option<Vec<usize>>,
    /// How the source spells the two arms: `then`/`else` for an `if`,
    /// `left`/`right` for `cases` and `both`.
    pub arm_names: [&'static str; 2],
    pub arms: [(BranchId, Vec<TraceFact>); 2],
}

pub(super) struct TraceStep {
    pub header: String,
    pub source_tactic_path: Option<Vec<usize>>,
    pub call_source: Option<TraceCallSource>,
    pub facts: Vec<TraceFact>,
    pub more_facts: usize,
    pub frontier: Option<String>,
    pub resources: Vec<TraceResourceChange>,
    pub more_resources: usize,
}

pub(super) struct TraceResourceChange {
    pub before: usize,
    pub after: usize,
    pub description: String,
}

pub(super) struct TraceCallSource {
    pub call: String,
}

pub(super) struct TraceFact {
    pub kernel: Proposition,
    /// A form re-lowered to this exact fact at the checked step.
    pub source: Option<String>,
    /// A structural, source-facing rendering of the checked kernel fact.
    /// Unlike `source`, this is presentation, not a validated citation.
    pub surface_view: Option<String>,
    pub pointer_view: Option<[PointerTraceView; 2]>,
}

/// Source spelling recovered against the read's own state. The memory is
/// retained until report rendering so unnamed snapshots share report labels.
#[derive(Clone)]
pub(super) struct PointerTraceView {
    pub text: String,
    pub mixed_snapshots: bool,
    pub snapshot: Option<(SharedCMemory, Option<String>)>,
}

impl PointerTraceView {
    fn point(&self, labels: &mut SnapshotLabels) -> Option<String> {
        self.snapshot.as_ref().map(|(memory, name)| {
            name.clone()
                .unwrap_or_else(|| labels.snapshot_name(memory.memory()))
        })
    }

    fn render(&self, labels: &mut SnapshotLabels) -> String {
        let text = trace_text(&self.text, 240);
        match self.point(labels) {
            Some(point) => format!("at({}, {text})", trace_text(&point, 128)),
            None => text,
        }
    }
}

fn render_pointer_pair(
    pair: &[PointerTraceView; 2],
    labels: &mut SnapshotLabels,
) -> (String, String) {
    let points = [pair[0].point(labels), pair[1].point(labels)];
    let uniform = match (&points[0], &points[1]) {
        (Some(a), Some(b))
            if a == b
                && pair[0]
                    .snapshot
                    .as_ref()
                    .zip(pair[1].snapshot.as_ref())
                    .is_some_and(|((left, _), (right, _))| left == right) =>
        {
            Some(a)
        }
        (Some(a), None) | (None, Some(a)) => Some(a),
        _ => None,
    };
    if let Some(point) = uniform
        && !pair.iter().any(|value| value.mixed_snapshots)
    {
        (
            format!(" at {}", trace_text(point, 128)),
            format!(
                "{} == {}",
                trace_text(&pair[0].text, 240),
                trace_text(&pair[1].text, 240)
            ),
        )
    } else {
        (
            String::new(),
            format!("{} == {}", pair[0].render(labels), pair[1].render(labels)),
        )
    }
}

/// Diagnostic-only payload for the exact rejected pair. Related equalities
/// are bounded explicit aliases, not a proof-search result or proposed fix.
pub(super) struct ChildArgumentTrace {
    child: String,
    index: usize,
    actual: Pointer,
    required: Pointer,
    related: Vec<Pointer>,
    views: HashMap<Pointer, PointerTraceView>,
}

impl ChildArgumentTrace {
    pub(super) fn from_refusal(
        refusal: &crate::kernel::ResourceRewriteRefusal,
        assumptions: &crate::kernel::PureFactContext,
    ) -> Option<Self> {
        let crate::kernel::ResourceRewriteRefusal::ChildArgumentNotEstablished {
            child,
            index,
            actual,
            required,
        } = refusal
        else {
            return None;
        };
        let (
            Some(crate::kernel::CValue::Pointer(actual)),
            Some(crate::kernel::CValue::Pointer(required)),
        ) = (actual.as_c_value(), required.as_c_value())
        else {
            return None;
        };
        Some(Self {
            views: HashMap::new(),
            child: child.clone(),
            index: *index,
            actual: actual.pointer().clone(),
            required: required.pointer().clone(),
            related: assumptions
                .exact_pointer_aliases(actual.pointer())
                .take(4)
                .cloned()
                .collect(),
        })
    }

    pub(super) fn name_values(
        &mut self,
        mut name: impl FnMut(&Pointer, &Pointer) -> Option<[PointerTraceView; 2]>,
    ) {
        for other in std::iter::once(&self.required).chain(&self.related) {
            if let Some([actual, required]) = name(&self.actual, other) {
                self.views.insert(self.actual.clone(), actual);
                self.views.insert(other.clone(), required);
            }
        }
    }

    fn value(&self, pointer: &Pointer, labels: &mut SnapshotLabels) -> String {
        if let Some(view) = self.views.get(pointer) {
            view.render(labels)
        } else if pointer == &Pointer::null() {
            "0 (null pointer)".into()
        } else if let Some(Bitvector32Term::MemoryLoad(memory, address, _)) =
            pointer_definition(pointer)
        {
            format!(
                "at({}, pointer_read(address {}))",
                labels.snapshot_name(memory.memory()),
                labels.pointer_value_name(&address)
            )
        } else {
            labels.pointer_value_name(pointer)
        }
    }

    pub(super) fn append_to(&self, trace: &mut String, labels: &mut SnapshotLabels) {
        let comparison = self.render(labels);
        if trace.len() + comparison.len() > MAX_RENDER_BYTES {
            *trace = trace_text(trace, MAX_RENDER_BYTES.saturating_sub(comparison.len()));
        }
        trace.push_str(&comparison);
    }

    pub(super) fn render(&self, labels: &mut SnapshotLabels) -> String {
        let actual = self.value(&self.actual, labels);
        let required = self.value(&self.required, labels);
        let mut output = format!(
            "\n\n  failed child argument comparison (checked):\n    child `{}`, argument {}\n    supplied: {actual}\n    required: {required}\n    equality was not established",
            trace_text(&self.child, 128),
            self.index + 1
        );
        if !self.related.is_empty() {
            output.push_str(
                "\n    potentially relevant known equalities (selected by shared supplied value):",
            );
            for pointer in &self.related {
                let name = self.value(pointer, labels);
                output.push_str(&format!("\n      {actual} == {name}"));
            }
            output.push_str(
                "\n    selection is diagnostic guidance, not an explanation of why equality failed",
            );
        }
        output.push_str("\n    defining snapshots identify original reads; different snapshots alone do not establish unequal values");
        output
    }
}

pub(super) fn pointer_definition(pointer: &Pointer) -> Option<Bitvector32Term> {
    crate::kernel::logical_pointer_read_term(pointer).or_else(|| {
        let read = pointer.as_loaded_value()?;
        (read.displacement == crate::kernel::PointerOffsetTerm::Constant(0)).then(|| {
            Bitvector32Term::MemoryLoad(
                read.defining_memory,
                Box::new(read.defining_address),
                crate::kernel::LoadKind::Bits32,
            )
        })
    })
}

fn append_pointer_definition(output: &mut String, pointer: &Pointer, labels: &mut SnapshotLabels) {
    if pointer == &Pointer::null() {
        output.push_str(&format!(
            "\n      {}: null pointer (0)",
            labels.pointer_value_name(pointer)
        ));
    }
    if let Some(Bitvector32Term::MemoryLoad(memory, address, _)) = pointer_definition(pointer) {
        let name = labels.pointer_value_name(pointer);
        let snapshot = labels.snapshot_name(memory.memory());
        let address = labels.pointer_value_name(&address);
        output.push_str(&format!(
            "\n      {name}: defining pointer read at {snapshot}, address {address}"
        ));
    }
}

/// The generated equation connecting a canonical load value to its raw
/// memory read is checker bookkeeping, not an additional surface premise.
/// The surface condition that caused the read is reported separately.
pub(super) fn visible_checked_fact(fact: &Proposition) -> bool {
    !crate::kernel::is_load_variable_defining_fact(fact)
}

/// The exact check that failed after the written proof completed. A completed
/// script has no failing proof node, so it cannot use a node-lineage trace.
/// These facts come from the certification context at the failed check.
pub(super) struct CertificationTraceState {
    goal: Proposition,
    source_goal: Option<String>,
    available: Vec<Proposition>,
    available_count: usize,
}

impl CertificationTraceState {
    pub(super) fn from_failure(failure: &ContractPathPreparationFailure) -> Option<Self> {
        Some(Self {
            goal: failure.obligation.clone()?,
            source_goal: failure.source_goal.clone(),
            available: failure.available.clone(),
            available_count: failure.available_count,
        })
    }
}

fn traced_read(term: &Bitvector32Term) -> Option<(SharedCMemory, Pointer)> {
    match term {
        Bitvector32Term::MemoryLoad(memory, pointer, _) => {
            Some((memory.clone(), pointer.as_ref().clone()))
        }
        Bitvector32Term::Variable(variable) => {
            crate::kernel::registered_load_for_variable(variable)
        }
        _ => None,
    }
}

impl ProofDiagnosticState for CertificationTraceState {
    fn source_goal(&self) -> Option<String> {
        self.source_goal.clone()
    }

    fn kernel_goal(&self) -> Option<&Proposition> {
        Some(&self.goal)
    }

    fn premises(&self, _limit: usize) -> Vec<&Proposition> {
        Vec::new()
    }

    fn premise_count(&self) -> usize {
        0
    }

    fn proof_trace(
        &self,
        _claim: &str,
        labels: &mut SnapshotLabels,
        _tactic_location: &dyn Fn(&[usize]) -> Option<(String, SourcePosition)>,
        _branch_arm: &dyn Fn(&[usize], &SourcePosition) -> Option<usize>,
        _have_body_contains: &dyn Fn(&[usize], &SourcePosition) -> bool,
        _target: Option<&SourcePosition>,
    ) -> Option<String> {
        let mut output =
            String::from("  certification trace (facts available at the failed check):");
        let mut relevant = Vec::new();
        let mut different_snapshots = false;
        if let Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(needed_left, needed_right),
            true,
        ) = &self.goal
            && let Some((needed_memory, needed_pointer)) = traced_read(needed_left)
        {
            let needed_snapshot = labels.snapshot_name(needed_memory.memory());
            for fact in &self.available {
                let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
                    fact
                else {
                    continue;
                };
                let Some((known_memory, known_pointer)) = traced_read(left) else {
                    continue;
                };
                if known_pointer == needed_pointer && right == needed_right {
                    relevant.push(fact);
                    if known_memory != needed_memory {
                        different_snapshots = true;
                        output.push_str(&format!(
                            "\n    same address and required value: known at {}, needed at {}",
                            labels.snapshot_name(known_memory.memory()),
                            needed_snapshot,
                        ));
                    }
                }
            }
            if different_snapshots {
                output.push_str(
                    "\n    certification did not establish that these snapshot reads agree",
                );
            }
        }
        if relevant.is_empty() {
            relevant.extend(self.available.iter().take(8));
        }
        let shown = relevant.len();
        output.push_str(&format!(
            "\n    checked facts (showing {} of {}):",
            shown, self.available_count,
        ));
        for fact in relevant {
            let source = render::render_simple_click_fact_labeled(fact, labels);
            let description = source.unwrap_or_else(|| {
                format!(
                    "internal fact (no exact Click spelling): {}",
                    render::render_internal_proposition_labeled(fact, labels)
                )
            });
            let description = trace_text(&description, 512);
            if output.len() + description.len() > MAX_RENDER_BYTES {
                output.push_str("\n    … <trace output limit reached>");
                break;
            }
            output.push_str("\n    fact: ");
            output.push_str(&description);
        }
        if shown < self.available_count {
            output.push_str("\n    … <other available facts omitted>");
        }
        append_legend(&mut output, labels);
        Some(output)
    }
}

thread_local! {
    static CAPTURE: RefCell<Option<Capture>> = const { RefCell::new(None) };
}

/// Scope tracing to one named function on the verification thread.
pub fn with_proof_trace<R>(function: &str, verify: impl FnOnce() -> R) -> R {
    struct Restore(Option<Capture>);
    impl Drop for Restore {
        fn drop(&mut self) {
            CAPTURE.with(|slot| *slot.borrow_mut() = self.0.take());
        }
    }
    let prior = CAPTURE.with(|slot| {
        slot.replace(Some(Capture {
            function: function.to_owned(),
            steps: HashMap::new(),
            branches: HashMap::new(),
            joins: HashMap::new(),
            bodies: HashMap::new(),
            scope_parents: HashMap::new(),
            retained_paths: Vec::new(),
            limit_reached: false,
        }))
    });
    let _restore = Restore(prior);
    verify()
}

pub(super) fn enabled_for(claim: &str) -> bool {
    CAPTURE.with(|slot| {
        slot.borrow().as_ref().is_some_and(|capture| {
            claim
                .strip_prefix(&capture.function)
                .is_some_and(|tail| tail.starts_with('.') || tail.is_empty())
        })
    })
}

pub(super) fn record(node: usize, step: TraceStep) {
    CAPTURE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else { return };
        if capture.steps.len() < MAX_STEPS {
            capture.steps.insert(node, step);
        } else {
            capture.limit_reached = true;
        }
    });
}

pub(super) fn record_branch(node: usize, branch: TraceBranch) {
    CAPTURE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else { return };
        if capture.branches.len() < MAX_STEPS {
            capture.branches.insert(node, branch);
        } else {
            capture.limit_reached = true;
        }
    });
}

pub(super) fn record_join(node: usize, join: TraceJoin) {
    CAPTURE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else { return };
        if capture.joins.len() < MAX_STEPS {
            capture.joins.insert(node, join);
        } else {
            capture.limit_reached = true;
        }
    });
}

pub(super) fn set_join_continuation_arm(node: usize, arm: usize) {
    CAPTURE.with(|slot| {
        if let Some(join) = slot
            .borrow_mut()
            .as_mut()
            .and_then(|capture| capture.joins.get_mut(&node))
        {
            join.continuation_arm = Some(arm);
        }
    });
}

pub(super) fn record_body(node: usize, body: TraceBody) {
    CAPTURE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else { return };
        if capture.bodies.len() < MAX_STEPS {
            capture.bodies.insert(node, body);
        } else {
            capture.limit_reached = true;
        }
    });
}

thread_local! {
    static LOOP_PARENT_LINEAGE: RefCell<Option<Vec<TracePathNode>>> = const { RefCell::new(None) };
}

/// Runs `verify` with `lineage`, the traced proof's path up to a `loop`
/// tactic, on record as the parent of any loop phase proof it drives, so
/// the phase's own trace can be rendered with that path above it.
pub(crate) fn with_loop_parent_lineage<R>(
    lineage: Option<Vec<TracePathNode>>,
    verify: impl FnOnce() -> R,
) -> R {
    struct Restore(Option<Vec<TracePathNode>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            LOOP_PARENT_LINEAGE.with(|slot| *slot.borrow_mut() = self.0.take());
        }
    }
    let prior = LOOP_PARENT_LINEAGE.with(|slot| slot.replace(lineage));
    let _restore = Restore(prior);
    verify()
}

/// The traced path up to the `loop` tactic whose phase proof is being
/// driven, if a trace is on and the tactic lies on one.
pub(crate) fn loop_parent_lineage() -> Option<Vec<TracePathNode>> {
    LOOP_PARENT_LINEAGE.with(|slot| slot.borrow().clone())
}

pub(super) fn register_scope(
    root: usize,
    parent_lineage: Vec<TracePathNode>,
    retained: Box<dyn Any>,
) {
    CAPTURE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else { return };
        if capture.scope_parents.len() < MAX_STEPS {
            capture.scope_parents.insert(
                root,
                TraceScope {
                    lineage: parent_lineage,
                    _retained: retained,
                },
            );
        } else {
            capture.limit_reached = true;
        }
    });
}

pub(super) fn record_accepted_path(
    claim: &str,
    path_index: usize,
    nested: bool,
    lineage: Vec<TracePathNode>,
    retained: Box<dyn Any>,
) {
    record_retained_path(claim, path_index, nested, true, lineage, retained);
}

pub(super) fn record_unfinished_path(
    claim: &str,
    path_index: usize,
    lineage: Vec<TracePathNode>,
    retained: Box<dyn Any>,
) {
    record_retained_path(claim, path_index, true, false, lineage, retained);
}

fn record_retained_path(
    claim: &str,
    path_index: usize,
    nested: bool,
    completed: bool,
    lineage: Vec<TracePathNode>,
    retained: Box<dyn Any>,
) {
    CAPTURE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else { return };
        if capture.retained_paths.len() < MAX_STEPS {
            capture.retained_paths.push(TraceRetainedPath {
                claim: claim.to_owned(),
                completed,
                nested,
                path_index,
                lineage,
                _retained: retained,
            });
        } else {
            capture.limit_reached = true;
        }
    });
}

/// Walk the accepted proof lineage. A structural join carries the checked
/// arm lineages it replaced, so an earlier call remains visible without
/// including abandoned smart-search candidates.
pub(super) fn render(
    claim: &str,
    lineage: &[TracePathNode],
    labels: &mut SnapshotLabels,
    tactic_location: &dyn Fn(&[usize]) -> Option<(String, SourcePosition)>,
    branch_arm: &dyn Fn(&[usize], &SourcePosition) -> Option<usize>,
    have_body_contains: &dyn Fn(&[usize], &SourcePosition) -> bool,
    target: Option<&SourcePosition>,
) -> Option<String> {
    CAPTURE.with(|slot| {
        let slot = slot.borrow();
        let capture = slot.as_ref()?;
        if !enabled_for(claim) {
            return None;
        }
        let (mut report, reached) = render_lineage(
            capture,
            lineage,
            labels,
            tactic_location,
            branch_arm,
            have_body_contains,
            target,
        );
        if let Some(target) = target
            && !reached
        {
            // A failing loop phase can have already checked a sibling arm.
            // Only retained checked paths may answer a target outside the
            // failure's own lineage; recorded search candidates cannot.
            for path in capture
                .retained_paths
                .iter()
                .filter(|path| path.claim == claim)
            {
                let mut path_labels = SnapshotLabels::default();
                let (alternative, reached) = render_lineage(
                    capture,
                    &path.lineage,
                    &mut path_labels,
                    tactic_location,
                    branch_arm,
                    have_body_contains,
                    Some(target),
                );
                if reached {
                    *labels = path_labels;
                    return Some(alternative);
                }
            }
            report.push_str("\n    target tactic has no recorded checked step on a retained path");
        }
        Some(report)
    })
}

/// Render a completed proof only from paths retained after checked path
/// certification. A target inside one path selects that path; without a
/// target, the first accepted path is a representative execution route.
pub(crate) fn render_accepted(
    labels: &mut SnapshotLabels,
    tactic_location: &dyn Fn(&str, &[usize]) -> Option<(String, SourcePosition)>,
    branch_arm: &dyn Fn(&str, &[usize], &SourcePosition) -> Option<usize>,
    have_body_contains: &dyn Fn(&str, &[usize], &SourcePosition) -> bool,
    target: Option<&SourcePosition>,
) -> Option<String> {
    CAPTURE.with(|slot| {
        let slot = slot.borrow();
        let capture = slot.as_ref()?;
        // The function's own paths first; a loop phase's path only answers a
        // target that lies inside the phase.
        let paths = capture
            .retained_paths
            .iter()
            .filter(|path| path.completed && !path.nested)
            .chain(
                capture
                    .retained_paths
                    .iter()
                    .filter(|path| path.completed && path.nested && target.is_some()),
            );
        for path in paths {
            let locate = |indices: &[usize]| tactic_location(&path.claim, indices);
            let arm = |indices: &[usize], position: &SourcePosition| {
                branch_arm(&path.claim, indices, position)
            };
            let body = |indices: &[usize], position: &SourcePosition| {
                have_body_contains(&path.claim, indices, position)
            };
            let mut path_labels = SnapshotLabels::default();
            let (mut report, reached) = render_lineage(
                capture,
                &path.lineage,
                &mut path_labels,
                &locate,
                &arm,
                &body,
                target,
            );
            if target.is_none() || reached {
                *labels = path_labels;
                if capture
                    .retained_paths
                    .iter()
                    .filter(|path| path.completed && !path.nested)
                    .count()
                    > 1
                {
                    report = report.replacen(
                        "proof trace (checked tactics and branch facts)",
                        &format!("proof trace (accepted path {})", path.path_index),
                        1,
                    );
                }
                return Some(report);
            }
        }
        None
    })
}

fn render_lineage(
    capture: &Capture,
    lineage: &[TracePathNode],
    labels: &mut SnapshotLabels,
    tactic_location: &dyn Fn(&[usize]) -> Option<(String, SourcePosition)>,
    branch_arm: &dyn Fn(&[usize], &SourcePosition) -> Option<usize>,
    have_body_contains: &dyn Fn(&[usize], &SourcePosition) -> bool,
    target: Option<&SourcePosition>,
) -> (String, bool) {
    let mut output = String::from("  proof trace (checked tactics and branch facts):");
    let mut segments = vec![lineage];
    while segments.len() < MAX_STEPS {
        let Some(root) = segments.last().and_then(|segment| segment.first()) else {
            break;
        };
        let Some(parent) = capture.scope_parents.get(&root.node) else {
            break;
        };
        segments.push(&parent.lineage);
    }
    let mut shown = 0;
    let mut depth = 0;
    let mut done = false;
    let mut reached = false;
    let segment_count = segments.len();
    for (index, segment) in segments.into_iter().rev().enumerate() {
        depth = append_path(
            &mut output,
            capture,
            segment,
            labels,
            tactic_location,
            branch_arm,
            have_body_contains,
            target,
            depth,
            &mut shown,
            &mut done,
            &mut reached,
        );
        // An enclosing segment stops at its first step past the target,
        // which for a loop phase's path is the enclosing proof's step after
        // the loop; the phase's own segment still lies ahead and is where
        // the target is reached.
        if done && !reached && index + 1 < segment_count && output.len() < MAX_RENDER_BYTES {
            done = false;
            depth += 1;
            continue;
        }
        if done {
            break;
        }
    }
    if shown == 0 {
        output.push_str("\n    <no checked simple steps recorded on this path>");
    }
    if capture.limit_reached {
        output.push_str("\n    … <trace step limit reached; later steps omitted>");
    }
    (output, reached)
}

fn append_path(
    output: &mut String,
    capture: &Capture,
    lineage: &[TracePathNode],
    labels: &mut SnapshotLabels,
    tactic_location: &dyn Fn(&[usize]) -> Option<(String, SourcePosition)>,
    branch_arm: &dyn Fn(&[usize], &SourcePosition) -> Option<usize>,
    have_body_contains: &dyn Fn(&[usize], &SourcePosition) -> bool,
    target: Option<&SourcePosition>,
    mut depth: usize,
    shown: &mut usize,
    done: &mut bool,
    reached: &mut bool,
) -> usize {
    if depth > 64 || *shown >= MAX_STEPS || output.len() >= MAX_RENDER_BYTES {
        return depth;
    }
    for path_node in lineage {
        if *done {
            break;
        }
        let indent = " ".repeat(2 + depth * 2);
        let mut detail = String::new();
        if let Some(join) = capture.joins.get(&path_node.node) {
            if let Some(branch) = capture.branches.get(&join.marker) {
                let site = branch
                    .source_tactic_path
                    .as_deref()
                    .and_then(tactic_location);
                if target.is_some_and(|target| {
                    site.as_ref()
                        .is_some_and(|(_, at)| source_after(at, target))
                }) {
                    *done = true;
                    break;
                }
                let header = trace_header(
                    &branch.header,
                    branch.source_tactic_path.as_deref(),
                    tactic_location,
                );
                let selected_arm = target
                    .and_then(|target| {
                        branch
                            .source_tactic_path
                            .as_deref()
                            .and_then(|path| branch_arm(path, target))
                    })
                    .or_else(|| {
                        target.and_then(|target| {
                            site.as_ref()
                                .is_some_and(|(_, at)| source_after(target, at))
                                .then_some(join.continuation_arm)
                                .flatten()
                        })
                    });
                if let Some(arm) = selected_arm {
                    detail.push_str(&format!(
                        "\n{indent}{header} ({} arm)",
                        branch.arm_names[arm]
                    ));
                    append_added_facts(
                        &mut detail,
                        &branch.arms[arm].1,
                        labels,
                        &format!("{indent}  "),
                    );
                    if output.len() + detail.len() > MAX_RENDER_BYTES {
                        output.push_str("\n    … <trace output limit reached>");
                        *done = true;
                        break;
                    }
                    output.push_str(&detail);
                    *shown += 1;
                    append_path(
                        output,
                        capture,
                        &join.arms[arm],
                        labels,
                        tactic_location,
                        branch_arm,
                        have_body_contains,
                        target,
                        depth + 1,
                        shown,
                        done,
                        reached,
                    );
                    *done = true;
                } else {
                    detail.push_str(&format!("\n{indent}{header}"));
                    append_added_facts(&mut detail, &join.facts, labels, &format!("{indent}  "));
                    if join.more_facts > 0 {
                        detail.push_str(&format!(
                            "\n{indent}  … {} more joined facts",
                            join.more_facts
                        ));
                    }
                    if output.len() + detail.len() > MAX_RENDER_BYTES {
                        output.push_str("\n    … <trace output limit reached>");
                        *done = true;
                        break;
                    }
                    output.push_str(&detail);
                    *shown += 1;
                    if target.is_some_and(|target| {
                        site.as_ref().is_some_and(|(_, at)| source_same(at, target))
                    }) {
                        *reached = true;
                    }
                }
            }
            continue;
        }
        if let (Some(branch), Some(selected_arm)) = (
            capture.branches.get(&path_node.node),
            path_node.selected_arm,
        ) {
            let Some((arm, (_, facts))) = branch
                .arms
                .iter()
                .enumerate()
                .find(|(_, (id, _))| *id == selected_arm)
            else {
                continue;
            };
            let site = branch
                .source_tactic_path
                .as_deref()
                .and_then(tactic_location);
            if target.is_some_and(|target| {
                site.as_ref()
                    .is_some_and(|(_, at)| source_after(at, target))
            }) {
                *done = true;
                break;
            }
            detail.push_str(&format!(
                "\n{indent}{} ({} arm)",
                trace_header(
                    &branch.header,
                    branch.source_tactic_path.as_deref(),
                    tactic_location,
                ),
                branch.arm_names[arm],
            ));
            append_added_facts(&mut detail, facts, labels, &format!("{indent}  "));
            depth += 1;
        } else if let Some(step) = capture.steps.get(&path_node.node) {
            if step
                .header
                .trim()
                .rsplit_once(": ")
                .is_some_and(|(_, kind)| kind == "mark")
            {
                continue;
            }
            let site = step.source_tactic_path.as_deref().and_then(tactic_location);
            if target.is_some_and(|target| {
                site.as_ref()
                    .is_some_and(|(_, at)| source_after(at, target))
            }) {
                *done = true;
                break;
            }
            detail.push_str(&format!(
                "\n{indent}{}",
                trace_text(
                    &trace_header(
                        step.header.trim(),
                        step.source_tactic_path.as_deref(),
                        tactic_location,
                    ),
                    240
                )
            ));
            let detail_indent = format!("{indent}  ");
            append_added_facts(&mut detail, &step.facts, labels, &detail_indent);
            if step.more_facts > 0 {
                detail.push_str(&format!(
                    "\n{detail_indent}… {} more added facts",
                    step.more_facts
                ));
            }
            if let Some(frontier) = &step.frontier {
                detail.push_str(&format!("\n{detail_indent}{}", trace_text(frontier, 240)));
            }
            for resource in &step.resources {
                let change = match (resource.before, resource.after) {
                    (0, 1) => format!("resource gained: {}", resource.description),
                    (1, 0) => format!("resource lost: {}", resource.description),
                    _ => format!(
                        "resource count: {} ({} -> {})",
                        resource.description, resource.before, resource.after
                    ),
                };
                detail.push_str(&format!("\n{detail_indent}{}", trace_text(&change, 240)));
            }
            if step.more_resources > 0 {
                detail.push_str(&format!(
                    "\n{detail_indent}… {} more resource changes",
                    step.more_resources
                ));
            }
        } else {
            continue;
        }
        if output.len() + detail.len() > MAX_RENDER_BYTES {
            output.push_str("\n    … <trace output limit reached>");
            break;
        }
        output.push_str(&detail);
        *shown += 1;
        if let Some(target) = target {
            let path = capture
                .steps
                .get(&path_node.node)
                .and_then(|step| step.source_tactic_path.as_deref())
                .or_else(|| {
                    capture
                        .branches
                        .get(&path_node.node)
                        .and_then(|branch| branch.source_tactic_path.as_deref())
                });
            if path
                .and_then(tactic_location)
                .is_some_and(|(_, at)| source_same(&at, target))
            {
                *reached = true;
            }
        }
        if let Some(body) = capture.bodies.get(&path_node.node)
            && target.is_some_and(|target| {
                capture
                    .steps
                    .get(&path_node.node)
                    .and_then(|step| step.source_tactic_path.as_deref())
                    .is_some_and(|path| have_body_contains(path, target))
            })
        {
            if *done {
                break;
            }
            append_path(
                output,
                capture,
                &body.lineage,
                labels,
                tactic_location,
                branch_arm,
                have_body_contains,
                target,
                depth + 1,
                shown,
                done,
                reached,
            );
        }
    }
    depth
}

fn trace_header(
    header: &str,
    path: Option<&[usize]>,
    tactic_location: &dyn Fn(&[usize]) -> Option<(String, SourcePosition)>,
) -> String {
    let Some((location, _)) = path.and_then(tactic_location) else {
        return header.to_owned();
    };
    let Some((_, description)) = header.trim().split_once(": ") else {
        return header.to_owned();
    };
    format!("{location}: {description}")
}

fn source_after(position: &SourcePosition, target: &SourcePosition) -> bool {
    (position.line, position.column) > (target.line, target.column)
}

fn source_same(position: &SourcePosition, target: &SourcePosition) -> bool {
    (position.line, position.column) == (target.line, target.column)
}

fn append_added_facts(
    output: &mut String,
    facts: &[TraceFact],
    labels: &mut SnapshotLabels,
    indent: &str,
) {
    let mut unspelled = 0;
    for fact in facts {
        if !visible_checked_fact(&fact.kernel) {
            continue;
        }
        if let Some(pair) = &fact.pointer_view {
            let (point, expression) = render_pointer_pair(pair, labels);
            output.push_str(&format!("\n{indent}adds{point}: {expression}"));
            continue;
        }
        let source = fact.source.clone().or_else(|| {
            if fact.surface_view.is_some() {
                None
            } else {
                render::render_simple_click_fact_labeled(&fact.kernel, labels)
            }
        });
        if let Some(source) = source {
            output.push_str(&format!("\n{indent}adds: {}", trace_text(&source, 240)));
            if let Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) =
                &fact.kernel
                && (pointer_definition(left).is_some() || pointer_definition(right).is_some())
            {
                let left_name = labels.pointer_value_name(left);
                let right_name = labels.pointer_value_name(right);
                output.push_str(&format!(
                    "\n{indent}  checked values: {left_name} == {right_name}"
                ));
                append_pointer_definition(output, left, labels);
                append_pointer_definition(output, right, labels);
            }
        } else if let Some(surface) = &fact.surface_view {
            output.push_str(&format!(
                "\n{indent}adds (surface view): {}",
                trace_text(surface, 240)
            ));
        } else if matches!(
            &fact.kernel,
            Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(..)
                    | ConditionTerm::IntegerNotEqual(..)
                    | ConditionTerm::IntegerLessThan(..)
                    | ConditionTerm::IntegerLessEqual(..)
                    | ConditionTerm::IntegerGreaterThan(..)
                    | ConditionTerm::IntegerGreaterEqual(..),
                _
            )
        ) {
            // Numeric observations are often captured theorem arguments,
            // rather than source expressions at the current frontier.
            // Show their bounded identity in an explicitly requested trace.
            let internal = render::render_internal_proposition_labeled(&fact.kernel, labels);
            output.push_str(&format!(
                "\n{indent}adds (internal): {}",
                trace_text(&internal, 512)
            ));
        } else {
            unspelled += 1;
        }
    }
    if unspelled > 0 {
        output.push_str(&format!(
            "\n{indent}adds: {unspelled} checked fact(s) with no exact Click spelling"
        ));
    }
}

pub(super) fn append_legend(trace: &mut String, labels: &mut SnapshotLabels) {
    let legend = labels.trace_legend();
    if legend.is_empty() {
        return;
    }
    let prefix = "… earlier trace text omitted to retain label definitions\n";
    if trace.len() + legend.len() > MAX_RENDER_BYTES {
        let keep = MAX_RENDER_BYTES.saturating_sub(legend.len() + prefix.len());
        let mut start = trace.len().saturating_sub(keep);
        while !trace.is_char_boundary(start) {
            start += 1;
        }
        *trace = format!("{prefix}{}", &trace[start..]);
    }
    trace.push_str(&legend);
}

fn trace_text(text: &str, max_bytes: usize) -> String {
    if text.len() <= max_bytes {
        return text.to_owned();
    }
    let mut end = max_bytes.saturating_sub('…'.len_utf8());
    while end > 0 && !text.is_char_boundary(end) {
        end -= 1;
    }
    format!("{}…", &text[..end])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{Bitvector32Term, CMemory, Pointer, PointerBlock, PointerOffsetTerm};

    #[test]
    fn pointer_facts_group_one_snapshot_and_qualify_mixed_reads() {
        let first = crate::kernel::intern_c_memory(CMemory::new());
        let second = crate::kernel::intern_c_memory(CMemory::new().with_block("changed", 1));
        let a = PointerTraceView {
            mixed_snapshots: false,
            text: "p->left".into(),
            snapshot: Some((first.clone(), Some("before_rotation".into()))),
        };
        let b = PointerTraceView {
            mixed_snapshots: false,
            text: "sibling->left".into(),
            snapshot: Some((second, Some("after_rotation".into()))),
        };
        let rid = PointerTraceView {
            mixed_snapshots: false,
            text: "rid".into(),
            snapshot: None,
        };
        let mut labels = SnapshotLabels::default();
        assert_eq!(
            render_pointer_pair(&[a.clone(), rid], &mut labels),
            (" at before_rotation".into(), "p->left == rid".into())
        );
        assert_eq!(
            render_pointer_pair(&[a.clone(), b], &mut labels),
            (
                String::new(),
                "at(before_rotation, p->left) == at(after_rotation, sibling->left)".into()
            )
        );
        let unnamed = PointerTraceView {
            mixed_snapshots: false,
            text: "p->left".into(),
            snapshot: Some((first, None)),
        };
        assert_eq!(unnamed.render(&mut labels), "at(snapshot#1, p->left)");
        assert_eq!(unnamed.render(&mut labels), "at(snapshot#1, p->left)");
        let mixed_base = PointerTraceView {
            text: "at(before_rotation, sibling)->left".into(),
            mixed_snapshots: true,
            snapshot: unnamed.snapshot.clone(),
        };
        assert_eq!(
            render_pointer_pair(&[mixed_base, a.clone()], &mut labels).0,
            ""
        );
        let bounded = PointerTraceView {
            text: "λ".repeat(MAX_RENDER_BYTES),
            mixed_snapshots: false,
            snapshot: Some((
                crate::kernel::intern_c_memory(CMemory::new()),
                Some("λ".repeat(MAX_RENDER_BYTES)),
            )),
        };
        assert!(bounded.render(&mut labels).len() < 400);
        // Exhausting report labels must not turn two different memories into
        // a shared snapshot merely because both print as untracked.
        let mut exhausted = SnapshotLabels::default();
        for index in 0..32 {
            exhausted.snapshot_name(&CMemory::new().with_block(format!("padding{index}"), 1));
        }
        let untracked = |block: &str| PointerTraceView {
            text: "p->left".into(),
            mixed_snapshots: false,
            snapshot: Some((
                crate::kernel::intern_c_memory(CMemory::new().with_block(block, 1)),
                None,
            )),
        };
        let (heading, expression) =
            render_pointer_pair(&[untracked("one"), untracked("two")], &mut exhausted);
        assert!(heading.is_empty());
        assert!(expression.contains("snapshot<untracked>"));
        // Source views take precedence over the unqualified citation.
        let fact = TraceFact {
            kernel: Proposition::ConditionIs(
                ConditionTerm::pointer_equal(Pointer::null(), Pointer::null()),
                true,
            ),
            source: Some("misleading current spelling".into()),
            surface_view: None,
            pointer_view: Some([a.clone(), a]),
        };
        let mut report = String::new();
        append_added_facts(&mut report, &[fact], &mut labels, "  ");
        assert_eq!(report, "\n  adds at before_rotation: p->left == p->left");
    }

    // Identical source spellings must not hide distinct reads, and the
    // refusal must reuse the same value labels as the preceding facts.
    #[test]
    fn child_comparison_keeps_read_values_distinct_from_source_spelling() {
        let address = Pointer::symbolic(crate::kernel::Variable(700_001));
        let first = crate::kernel::intern_c_memory(CMemory::new());
        let second = crate::kernel::intern_c_memory(CMemory::new().store(
            address.clone(),
            crate::kernel::CValue::Int32(Bitvector32Term::Constant(1)),
        ));
        let a = Pointer::loaded_value(&first, &address);
        let b = Pointer::loaded_value(&second, &address);
        let rid = Pointer::symbolic(crate::kernel::Variable(700_002));
        let facts = [a.clone(), b.clone()].map(|value| TraceFact {
            kernel: Proposition::ConditionIs(
                ConditionTerm::pointer_equal(value, rid.clone()),
                true,
            ),
            source: Some("p->left == rid".into()),
            surface_view: None,
            pointer_view: None,
        });
        let mut labels = SnapshotLabels::default();
        let mut report = String::new();
        append_added_facts(&mut report, &facts, &mut labels, "  ");
        assert!(
            report.contains("checked values: value#1 == value#2"),
            "{report}"
        );
        assert!(
            report.contains("checked values: value#4 == value#2"),
            "{report}"
        );
        assert!(report.contains("snapshot#1"), "{report}");
        assert!(report.contains("snapshot#2"), "{report}");
        let comparison = ChildArgumentTrace {
            child: "sibling".into(),
            index: 0,
            actual: rid,
            required: b,
            related: vec![a],
            views: HashMap::new(),
        }
        .render(&mut labels);
        assert!(comparison.contains("supplied: value#2"), "{comparison}");
        assert!(
            comparison.contains("required: at(snapshot#2, pointer_read(address value#3))"),
            "{comparison}"
        );
        assert!(
            comparison.contains("value#2 == at(snapshot#1, pointer_read(address value#3))"),
            "{comparison}"
        );
        assert!(comparison.contains("potentially relevant"));
        assert!(comparison.contains("different snapshots alone do not establish unequal values"));
        assert!(!comparison.contains("Missing:"));
        let comparison = ChildArgumentTrace {
            child: "λ".repeat(MAX_RENDER_BYTES),
            index: 0,
            actual: Pointer::null(),
            required: Pointer::null(),
            related: vec![],
            views: HashMap::new(),
        };
        let mut long = "λ".repeat(MAX_RENDER_BYTES);
        comparison.append_to(&mut long, &mut labels);
        assert!(long.len() <= MAX_RENDER_BYTES);
        assert!(long.contains("failed child argument comparison"));
        assert!(long.contains("0 (null pointer)"));
    }

    #[test]
    fn trace_header_uses_resolved_source_tactic_location() {
        let label = |path: &[usize]| {
            (path == [3, 1]).then(|| ("tactic@475".to_owned(), SourcePosition::new(475, 1)))
        };
        assert_eq!(
            trace_header(
                "tactic 3 > have body tactic 1: assumption()",
                Some(&[3, 1]),
                &label,
            ),
            "tactic@475: assumption()"
        );
    }

    fn loadable_at(memory: CMemory) -> Proposition {
        Proposition::CMemoryLoadable {
            memory,
            base: Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0),
            },
            bytes: Bitvector32Term::Constant(1),
            wide: false,
        }
    }

    #[test]
    fn trace_and_goal_share_snapshot_labels_without_conflating_distinct_memories() {
        with_proof_trace("f", || {
            let first = CMemory::default();
            let second = CMemory::new().with_block("different", 1);
            record(
                1,
                TraceStep {
                    header: "\n    source tactic 0: step".into(),
                    source_tactic_path: None,
                    call_source: None,
                    facts: vec![
                        TraceFact {
                            kernel: loadable_at(first.clone()),
                            source: None,
                            surface_view: None,
                            pointer_view: None,
                        },
                        TraceFact {
                            kernel: loadable_at(second.clone()),
                            source: None,
                            surface_view: None,
                            pointer_view: None,
                        },
                    ],
                    more_facts: 0,
                    frontier: None,
                    resources: Vec::new(),
                    more_resources: 0,
                },
            );
            let mut labels = SnapshotLabels::default();
            let goal =
                render::render_internal_proposition_labeled(&loadable_at(first), &mut labels);
            let trace = render(
                "f",
                &[TracePathNode {
                    node: 1,
                    selected_arm: None,
                }],
                &mut labels,
                &|_| None,
                &|_, _| None,
                &|_, _| false,
                None,
            )
            .unwrap();
            assert!(goal.contains("snapshot#1"), "{goal}");
            assert!(
                trace.contains("adds: 2 checked fact(s) with no exact Click spelling"),
                "{trace}"
            );
            assert!(!trace.contains("snapshot#2"), "{trace}");
        });
    }

    #[test]
    fn trace_integer_observations_do_not_hide_unspelled_theorem_facts() {
        use crate::kernel::{IntegerTerm, MachineIntegerType, Variable};
        let fact = TraceFact {
            kernel: Proposition::ConditionIs(
                ConditionTerm::integer_equal(
                    IntegerTerm::from_machine(
                        MachineIntegerType::UInt32,
                        Bitvector32Term::Variable(Variable(981_702)),
                    )
                    .unwrap(),
                    IntegerTerm::constant_i64(17),
                ),
                true,
            ),
            source: None,
            surface_view: None,
            pointer_view: None,
        };
        let mut output = String::new();
        append_added_facts(&mut output, &[fact], &mut SnapshotLabels::default(), "  ");
        assert!(output.contains("adds (internal):"), "{output}");
        assert!(!output.contains("no exact Click spelling"), "{output}");
        assert!(output.len() < 1024, "{output}");
    }

    #[test]
    fn nested_scope_trace_keeps_the_enclosing_checked_step() {
        with_proof_trace("f", || {
            let step = |header| TraceStep {
                header,
                source_tactic_path: None,
                call_source: None,
                facts: Vec::new(),
                more_facts: 0,
                frontier: None,
                resources: Vec::new(),
                more_resources: 0,
            };
            record(1, step("\n    source tactic 0: step".into()));
            record(3, step("\n    have body tactic 0: normalize".into()));
            register_scope(
                2,
                vec![TracePathNode {
                    node: 1,
                    selected_arm: None,
                }],
                Box::new(()),
            );
            let trace = render(
                "f",
                &[
                    TracePathNode {
                        node: 2,
                        selected_arm: None,
                    },
                    TracePathNode {
                        node: 3,
                        selected_arm: None,
                    },
                ],
                &mut SnapshotLabels::default(),
                &|_| None,
                &|_, _| None,
                &|_, _| false,
                None,
            )
            .unwrap();
            assert!(trace.contains("source tactic 0: step"), "{trace}");
            assert!(trace.contains("have body tactic 0: normalize"), "{trace}");
        });
    }

    #[test]
    fn exact_click_fact_takes_precedence_over_internal_rendering() {
        with_proof_trace("f", || {
            record(
                1,
                TraceStep {
                    header: "\n    source tactic 0: have".into(),
                    source_tactic_path: None,
                    call_source: None,
                    facts: vec![TraceFact {
                        kernel: Proposition::ConditionIs(
                            crate::kernel::ConditionTerm::Constant(true),
                            true,
                        ),
                        source: Some("x == x".into()),
                        surface_view: Some("different rendering".into()),
                        pointer_view: None,
                    }],
                    more_facts: 0,
                    frontier: None,
                    resources: Vec::new(),
                    more_resources: 0,
                },
            );
            let report = render(
                "f",
                &[TracePathNode {
                    node: 1,
                    selected_arm: None,
                }],
                &mut SnapshotLabels::default(),
                &|_| None,
                &|_, _| None,
                &|_, _| false,
                None,
            )
            .unwrap();
            assert!(report.contains("adds: x == x"), "{report}");
            assert!(!report.contains("different rendering"), "{report}");
            assert!(!report.contains("no exact Click spelling"), "{report}");
        });
    }

    #[test]
    fn trace_prints_surface_view_when_exact_citation_is_unavailable() {
        let mut output = String::new();
        append_added_facts(
            &mut output,
            &[TraceFact {
                kernel: Proposition::ConditionIs(ConditionTerm::Constant(true), true),
                source: None,
                surface_view: Some("0 <= unmarked(visited, 0, n)".into()),
                pointer_view: None,
            }],
            &mut SnapshotLabels::default(),
            "  ",
        );
        assert_eq!(
            output,
            "\n  adds (surface view): 0 <= unmarked(visited, 0, n)"
        );
    }

    #[test]
    fn trace_omits_generated_load_binding_beside_surface_branch_fact() {
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let Bitvector32Term::Variable(variable) = crate::kernel::canonical_form_of_load(
            memory.clone(),
            pointer.clone(),
            crate::kernel::LoadKind::Bits32,
        ) else {
            panic!("an unresolved external read has a load variable");
        };
        let defining = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(variable)),
                Box::new(Bitvector32Term::MemoryLoad(
                    memory,
                    Box::new(pointer),
                    crate::kernel::LoadKind::Bits32,
                )),
            ),
            true,
        );
        let mut output = String::new();
        append_added_facts(
            &mut output,
            &[
                TraceFact {
                    kernel: Proposition::ConditionIs(ConditionTerm::Constant(true), true),
                    source: Some("at(statement(0).entry, visited[cur]) == 0".into()),
                    surface_view: None,
                    pointer_view: None,
                },
                TraceFact {
                    kernel: defining,
                    source: None,
                    surface_view: None,
                    pointer_view: None,
                },
            ],
            &mut SnapshotLabels::default(),
            "  ",
        );
        assert_eq!(
            output,
            "\n  adds: at(statement(0).entry, visited[cur]) == 0"
        );
    }

    #[test]
    fn joined_branch_retains_only_accepted_arm_steps() {
        with_proof_trace("f", || {
            let step = |name: &str| TraceStep {
                header: format!("source tactic: {name}"),
                source_tactic_path: None,
                call_source: None,
                facts: Vec::new(),
                more_facts: 0,
                frontier: None,
                resources: Vec::new(),
                more_resources: 0,
            };
            record(2, step("then step"));
            record(3, step("else step"));
            record(4, step("discarded candidate"));
            record_branch(
                1,
                TraceBranch {
                    header: "source tactic 0: branch".into(),
                    source_tactic_path: Some(vec![0]),
                    arm_names: ["then", "else"],
                    arms: [
                        (
                            BranchId::ROOT,
                            vec![TraceFact {
                                kernel: Proposition::ConditionIs(
                                    ConditionTerm::Constant(true),
                                    true,
                                ),
                                source: Some("x != 0".into()),
                                surface_view: None,
                                pointer_view: None,
                            }],
                        ),
                        (
                            BranchId::ROOT,
                            vec![TraceFact {
                                kernel: Proposition::ConditionIs(
                                    ConditionTerm::Constant(false),
                                    false,
                                ),
                                source: Some("x == 0".into()),
                                surface_view: None,
                                pointer_view: None,
                            }],
                        ),
                    ],
                },
            );
            record_join(
                5,
                TraceJoin {
                    marker: 1,
                    arms: [
                        vec![TracePathNode {
                            node: 2,
                            selected_arm: None,
                        }],
                        vec![TracePathNode {
                            node: 3,
                            selected_arm: None,
                        }],
                    ],
                    facts: vec![TraceFact {
                        kernel: Proposition::ConditionIs(ConditionTerm::Constant(true), true),
                        source: Some("stable".into()),
                        surface_view: None,
                        pointer_view: None,
                    }],
                    more_facts: 0,
                    continuation_arm: None,
                    _retained: Box::new(()),
                },
            );
            let trace = render(
                "f",
                &[TracePathNode {
                    node: 5,
                    selected_arm: None,
                }],
                &mut SnapshotLabels::default(),
                &|_| Some(("tactic@1".into(), SourcePosition::new(1, 1))),
                &|_, _| Some(0),
                &|_, _| false,
                Some(&SourcePosition::new(2, 1)),
            )
            .unwrap();
            assert!(trace.contains("tactic@1: branch (then arm)"), "{trace}");
            assert!(trace.contains("adds: x != 0"), "{trace}");
            assert!(trace.contains("then step"), "{trace}");
            assert!(!trace.contains("adds: x == 0"), "{trace}");
            assert!(!trace.contains("else step"), "{trace}");
            assert!(!trace.contains("discarded candidate"), "{trace}");
            let summary = render(
                "f",
                &[TracePathNode {
                    node: 5,
                    selected_arm: None,
                }],
                &mut SnapshotLabels::default(),
                &|_| Some(("tactic@1".into(), SourcePosition::new(1, 1))),
                &|_, _| None,
                &|_, _| false,
                Some(&SourcePosition::new(3, 1)),
            )
            .unwrap();
            assert!(summary.contains("adds: stable"), "{summary}");
            assert!(!summary.contains("then step"), "{summary}");
            assert!(!summary.contains("else step"), "{summary}");
        });
    }

    #[test]
    fn completed_have_shows_only_its_exported_fact_unless_target_is_inside() {
        with_proof_trace("f", || {
            let fact = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
            record(
                1,
                TraceStep {
                    header: "source tactic 2: have x == x".into(),
                    source_tactic_path: Some(vec![2]),
                    call_source: None,
                    facts: vec![TraceFact {
                        kernel: fact,
                        source: Some("x == x".into()),
                        surface_view: None,
                        pointer_view: None,
                    }],
                    more_facts: 0,
                    frontier: None,
                    resources: Vec::new(),
                    more_resources: 0,
                },
            );
            record(
                2,
                TraceStep {
                    header: "have body tactic 1: normalize()".into(),
                    source_tactic_path: Some(vec![2, 1]),
                    call_source: None,
                    facts: Vec::new(),
                    more_facts: 0,
                    frontier: None,
                    resources: Vec::new(),
                    more_resources: 0,
                },
            );
            record_body(
                1,
                TraceBody {
                    lineage: vec![TracePathNode {
                        node: 2,
                        selected_arm: None,
                    }],
                    _retained: Box::new(()),
                },
            );
            let report = render(
                "f",
                &[TracePathNode {
                    node: 1,
                    selected_arm: None,
                }],
                &mut SnapshotLabels::default(),
                &|_| None,
                &|_, _| None,
                &|_, _| false,
                None,
            )
            .unwrap();
            assert!(report.contains("source tactic 2: have x == x"), "{report}");
            assert!(report.contains("adds: x == x"), "{report}");
            assert!(
                !report.contains("have body tactic 1: normalize()"),
                "{report}"
            );
            let inside = render(
                "f",
                &[TracePathNode {
                    node: 1,
                    selected_arm: None,
                }],
                &mut SnapshotLabels::default(),
                &|path| match path {
                    [2] => Some(("tactic@2".into(), SourcePosition::new(2, 1))),
                    [2, 1] => Some(("tactic@3".into(), SourcePosition::new(3, 1))),
                    _ => None,
                },
                &|_, _| None,
                &|path, _| path == [2],
                Some(&SourcePosition::new(3, 1)),
            )
            .unwrap();
            assert!(inside.contains("tactic@3: normalize()"), "{inside}");
        });
    }

    #[test]
    fn successful_trace_uses_only_retained_accepted_lineage() {
        with_proof_trace("f", || {
            let step = |header| TraceStep {
                header,
                source_tactic_path: None,
                call_source: None,
                facts: Vec::new(),
                more_facts: 0,
                frontier: None,
                resources: Vec::new(),
                more_resources: 0,
            };
            record(
                1,
                TraceStep {
                    source_tactic_path: Some(vec![0]),
                    ..step("source tactic 0: accepted".into())
                },
            );
            record(
                2,
                TraceStep {
                    source_tactic_path: Some(vec![0]),
                    ..step("source tactic 0: abandoned candidate".into())
                },
            );
            record(3, step("source tactic 0: mark".into()));
            record_accepted_path(
                "f.contract",
                0,
                false,
                vec![
                    TracePathNode {
                        node: 3,
                        selected_arm: None,
                    },
                    TracePathNode {
                        node: 1,
                        selected_arm: None,
                    },
                ],
                Box::new(()),
            );
            let report = render_accepted(
                &mut SnapshotLabels::default(),
                &|_, _| None,
                &|_, _, _| None,
                &|_, _, _| false,
                None,
            )
            .unwrap();
            assert!(report.contains("accepted"), "{report}");
            assert!(!report.contains("abandoned candidate"), "{report}");
            assert!(!report.contains(": mark"), "{report}");
            let targeted = render(
                "f.contract",
                &[TracePathNode {
                    node: 3,
                    selected_arm: None,
                }],
                &mut SnapshotLabels::default(),
                &|_| Some(("tactic@2".into(), SourcePosition::new(2, 1))),
                &|_, _| None,
                &|_, _| false,
                Some(&SourcePosition::new(2, 1)),
            )
            .unwrap();
            assert!(targeted.contains("accepted"), "{targeted}");
            assert!(!targeted.contains("abandoned candidate"), "{targeted}");
            record(
                4,
                TraceStep {
                    source_tactic_path: Some(vec![1]),
                    ..step("source tactic 1: unfinished arm".into())
                },
            );
            record_unfinished_path(
                "f.contract",
                0,
                vec![TracePathNode {
                    node: 4,
                    selected_arm: None,
                }],
                Box::new(()),
            );
            let locate = |path: &[usize]| {
                let line = path[0] + 2;
                Some((format!("tactic@{line}"), SourcePosition::new(line, 1)))
            };
            let target = SourcePosition::new(3, 1);
            assert!(
                render_accepted(
                    &mut SnapshotLabels::default(),
                    &|_, path| locate(path),
                    &|_, _, _| None,
                    &|_, _, _| false,
                    Some(&target),
                )
                .is_none(),
                "an unfinished arm cannot become an accepted proof trace"
            );
            let unfinished = render(
                "f.contract",
                &[],
                &mut SnapshotLabels::default(),
                &locate,
                &|_, _| None,
                &|_, _| false,
                Some(&target),
            )
            .unwrap();
            assert!(unfinished.contains("unfinished arm"), "{unfinished}");
            assert!(!unfinished.contains("abandoned candidate"), "{unfinished}");
        });
    }
}
