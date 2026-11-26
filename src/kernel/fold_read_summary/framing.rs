//! Test-only fold framing and its definition registry.

use super::super::resource_tracker::{TrackedResource, step_effect};
use super::*;
use crate::kernel::CompareRelation;
use std::collections::BTreeMap;
use std::sync::Arc;

/// What the test registry holds for one declared name.
#[derive(Clone, Debug)]
enum RegisteredFoldRead {
    Checked(Arc<CheckedFoldReadSummary>),
    Declined(FoldReadDecline),
    /// Two different bodies were registered under one name in this test.
    /// Neither may govern framing, because unfolding might use the other.
    Conflicting,
}

thread_local! {
    /// The read summary of each registered `Integer` function, recorded once
    /// per test case from the declared body, keyed by name and
    /// guarded by the body's fingerprint.
    static FOLD_READ_SUMMARIES: std::cell::RefCell<
        BTreeMap<String, (u64, RegisteredFoldRead)>,
    > = const { std::cell::RefCell::new(BTreeMap::new()) };
}

/// Records one declared body and its checked summary (or decline) for this
/// test case. Registering a *different* body under a name already
/// registered makes that name unusable for the rest of the case. Framing
/// needs a summary of the exact body that unfolding states.
pub(crate) fn register_fold_read_definition(definition: FoldReadDefinition) {
    let fingerprint = definition.fingerprint();
    let checked = match CheckedFoldReadSummary::check(&definition) {
        Ok(summary) => RegisteredFoldRead::Checked(Arc::new(summary)),
        Err(decline) => RegisteredFoldRead::Declined(decline),
    };
    FOLD_READ_SUMMARIES.with(|registry| {
        let mut registry = registry.borrow_mut();
        match registry.get_mut(&definition.name) {
            Some((recorded, _)) if *recorded == fingerprint => {}
            Some(entry) => entry.1 = RegisteredFoldRead::Conflicting,
            None => {
                registry.insert(definition.name.clone(), (fingerprint, checked));
            }
        }
    });
}

pub(crate) fn clear_fold_read_summaries() {
    FOLD_READ_SUMMARIES.with(|registry| registry.borrow_mut().clear());
}

/// Why no summary governs a name, for a refusal to print.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum FoldReadUnavailable {
    NotRegistered,
    Declined(FoldReadDecline),
    Conflicting,
}

pub(crate) fn registered_fold_read_summary(
    name: &str,
) -> Result<Arc<CheckedFoldReadSummary>, FoldReadUnavailable> {
    crate::instrumentation::record_deterministic_work(1);
    FOLD_READ_SUMMARIES.with(|registry| match registry.borrow().get(name) {
        None => Err(FoldReadUnavailable::NotRegistered),
        Some((_, RegisteredFoldRead::Checked(summary))) => Ok(summary.clone()),
        Some((_, RegisteredFoldRead::Declined(decline))) => {
            Err(FoldReadUnavailable::Declined(decline.clone()))
        }
        Some((_, RegisteredFoldRead::Conflicting)) => Err(FoldReadUnavailable::Conflicting),
    })
}

// ---------------------------------------------------------------------------
// Framing
// ---------------------------------------------------------------------------

/// A checked explicit transport of one proposition across the steps between
/// the states its fold applications name.
#[derive(Clone, Debug)]
pub(crate) struct CheckedFoldFrameTransport {
    /// How many application pairs were framed.
    pub(crate) framed_applications: usize,
    /// How many recorded steps the framing crossed in all.
    pub(crate) crossed_steps: usize,
}

/// Why a transport could not be framed, bounded for a refusal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum FoldFrameRefusal {
    /// The two propositions differ somewhere other than in the array
    /// states of fold applications.
    ShapeMismatch,
    /// No two applications differ, so this rule has nothing to frame.
    NothingToFrame,
    /// The function has no checked read summary.
    NoSummary {
        name: String,
        reason: FoldReadUnavailable,
    },
    /// The two applications differ in a name, a scalar argument, the array
    /// pointer, or an argument sort.
    ApplicationsDiffer { name: String },
    /// Neither array state is recorded as derived from the other.
    UnrelatedStates { name: String },
    /// A step between the states could not be shown to miss the interval.
    StepNotShownOutside {
        name: String,
        step: &'static str,
        detail: &'static str,
    },
}

impl std::fmt::Display for FoldFrameRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ShapeMismatch => formatter.write_str(
                "source and target differ outside the array states of fold applications",
            ),
            Self::NothingToFrame => {
                formatter.write_str("no fold application differs between source and target")
            }
            Self::NoSummary { name, reason } => match reason {
                FoldReadUnavailable::NotRegistered => {
                    write!(formatter, "`{name}` has no checked read summary")
                }
                FoldReadUnavailable::Declined(decline) => {
                    write!(formatter, "`{name}` has no checked read summary: {decline}")
                }
                FoldReadUnavailable::Conflicting => write!(
                    formatter,
                    "`{name}` has no checked read summary: two different bodies were declared under that name"
                ),
            },
            Self::ApplicationsDiffer { name } => write!(
                formatter,
                "the two `{name}` applications differ in an endpoint, a scalar argument or the array pointer, not only in the array state"
            ),
            Self::UnrelatedStates { name } => write!(
                formatter,
                "the two `{name}` array states are not on one recorded history"
            ),
            Self::StepNotShownOutside { name, step, detail } => write!(
                formatter,
                "a `{step}` step between the two `{name}` states was not shown to miss the cells the fold reads: {detail}"
            ),
        }
    }
}

/// The explicit transport rule: `target` follows from `source` when the two
/// propositions are the same up to the array states of summarized fold
/// applications, and every such pair is framed.
///
/// The walk is shallow and parallel: propositional connectives, the Integer
/// comparisons, and the Integer arithmetic spine. Anything else must be equal
/// on both sides. Work is linear in the two propositions plus, per framed
/// application pair, one unit per recorded step crossed.
pub(crate) fn frame_fold_application_transport(
    source: &Proposition,
    target: &Proposition,
    assumptions: &PureFactContext,
) -> Result<CheckedFoldFrameTransport, FoldFrameRefusal> {
    let mut checked = CheckedFoldFrameTransport {
        framed_applications: 0,
        crossed_steps: 0,
    };
    zip_proposition(source, target, assumptions, &mut checked)?;
    if checked.framed_applications == 0 {
        return Err(FoldFrameRefusal::NothingToFrame);
    }
    Ok(checked)
}

fn zip_proposition(
    source: &Proposition,
    target: &Proposition,
    assumptions: &PureFactContext,
    checked: &mut CheckedFoldFrameTransport,
) -> Result<(), FoldFrameRefusal> {
    crate::instrumentation::record_deterministic_work(1);
    match (source, target) {
        (
            Proposition::ConditionIs(left, left_value),
            Proposition::ConditionIs(right, right_value),
        ) if left_value == right_value => {
            zip_condition(left.old_form(), right.old_form(), assumptions, checked)
        }
        (Proposition::And(a, b), Proposition::And(c, d))
        | (Proposition::Or(a, b), Proposition::Or(c, d))
        | (Proposition::Implies(a, b), Proposition::Implies(c, d)) => {
            zip_proposition(a, c, assumptions, checked)?;
            zip_proposition(b, d, assumptions, checked)
        }
        (Proposition::Not(a), Proposition::Not(b)) => zip_proposition(a, b, assumptions, checked),
        (left, right) if left == right => Ok(()),
        _ => Err(FoldFrameRefusal::ShapeMismatch),
    }
}

fn zip_condition(
    source: &OldConditionTerm,
    target: &OldConditionTerm,
    assumptions: &PureFactContext,
    checked: &mut CheckedFoldFrameTransport,
) -> Result<(), FoldFrameRefusal> {
    use OldConditionTerm as C;
    crate::instrumentation::record_deterministic_work(1);
    match (source, target) {
        (C::IntegerLessThan(a, b), C::IntegerLessThan(c, d))
        | (C::IntegerLessEqual(a, b), C::IntegerLessEqual(c, d))
        | (C::IntegerGreaterThan(a, b), C::IntegerGreaterThan(c, d))
        | (C::IntegerGreaterEqual(a, b), C::IntegerGreaterEqual(c, d))
        | (C::IntegerEqual(a, b), C::IntegerEqual(c, d))
        | (C::IntegerNotEqual(a, b), C::IntegerNotEqual(c, d)) => {
            zip_integer(a, c, assumptions, checked)?;
            zip_integer(b, d, assumptions, checked)
        }
        (left, right) if left == right => Ok(()),
        _ => Err(FoldFrameRefusal::ShapeMismatch),
    }
}

fn zip_integer(
    source: &SharedIntegerTerm,
    target: &SharedIntegerTerm,
    assumptions: &PureFactContext,
    checked: &mut CheckedFoldFrameTransport,
) -> Result<(), FoldFrameRefusal> {
    crate::instrumentation::record_deterministic_work(1);
    if source == target {
        return Ok(());
    }
    match (source.as_ref(), target.as_ref()) {
        (IntegerTerm::Negate(a), IntegerTerm::Negate(b)) => zip_integer(a, b, assumptions, checked),
        (IntegerTerm::Add(a, b), IntegerTerm::Add(c, d))
        | (IntegerTerm::Subtract(a, b), IntegerTerm::Subtract(c, d))
        | (IntegerTerm::Multiply(a, b), IntegerTerm::Multiply(c, d))
        | (IntegerTerm::TruncatingQuotient(a, b), IntegerTerm::TruncatingQuotient(c, d))
        | (IntegerTerm::TruncatingRemainder(a, b), IntegerTerm::TruncatingRemainder(c, d)) => {
            zip_integer(a, c, assumptions, checked)?;
            zip_integer(b, d, assumptions, checked)
        }
        (
            IntegerTerm::PureFunctionApplication(left),
            IntegerTerm::PureFunctionApplication(right),
        ) => {
            let crossed = frame_fold_applications(left, right, assumptions)?;
            checked.framed_applications += 1;
            checked.crossed_steps += crossed;
            Ok(())
        }
        _ => Err(FoldFrameRefusal::ShapeMismatch),
    }
}

/// Proves `left == right` for two applications of one summarized function
/// that differ only in the array argument's state, returning how many
/// recorded steps were crossed.
pub(crate) fn frame_fold_applications(
    left: &SharedPureApplication,
    right: &SharedPureApplication,
    assumptions: &PureFactContext,
) -> Result<usize, FoldFrameRefusal> {
    let name = left.name().to_string();
    if left.name() != right.name() {
        return Err(FoldFrameRefusal::ApplicationsDiffer { name });
    }
    let summary = registered_fold_read_summary(left.name()).map_err(|reason| {
        FoldFrameRefusal::NoSummary {
            name: name.clone(),
            reason,
        }
    })?;
    let differ = || FoldFrameRefusal::ApplicationsDiffer { name: name.clone() };
    let left_interval = summary.instantiate(left).ok_or_else(differ)?;
    // Every argument but the array's state must be the same term: the
    // same scalar values (so the same endpoints), the same pointer, the same
    // element type. Nothing here is proved equal; it is compared.
    for (position, (a, b)) in left.arguments().iter().zip(right.arguments()).enumerate() {
        crate::instrumentation::record_deterministic_work(1);
        let same = if position == summary.array_parameter {
            match (a, b) {
                (
                    PureFunctionArgument::ArrayRef {
                        pointer: left_pointer,
                        element_type: left_type,
                        ..
                    },
                    PureFunctionArgument::ArrayRef {
                        pointer: right_pointer,
                        element_type: right_type,
                        ..
                    },
                ) => left_pointer == right_pointer && left_type == right_type,
                _ => false,
            }
        } else {
            a == b
        };
        if !same {
            return Err(differ());
        }
    }
    if left.arguments().len() != right.arguments().len() {
        return Err(differ());
    }
    let PureFunctionArgument::ArrayRef {
        point: right_memory,
        ..
    } = &right.arguments()[summary.array_parameter]
    else {
        return Err(differ());
    };
    let left_state = intern_memory_ref(&left_interval.memory);
    let right_state = right_memory.shared_memory().clone();
    if left_state == right_state {
        return Ok(0);
    }
    // SymbolicMemory states are content-addressed and each records its first derivation,
    // so the later state's recorded history need not pass through the
    // earlier one: a second store to one cell re-derives from the state
    // before the first. Walk both back to a common state, always stepping
    // the newer one, and check every step crossed on either side. Each step
    // relates two contents, so agreement on the interval along both walks is
    // agreement between the two ends. Arena ids strictly decrease along a
    // derivation, so the walk terminates, and it costs one unit per step.
    let empty = interval_proven_empty(&left_interval, assumptions);
    let (mut left_current, mut right_current) = (left_state, right_state);
    let mut crossed = 0;
    while left_current != right_current {
        crate::instrumentation::record_deterministic_work(1);
        let newer = if later_than(&left_current, &right_current) {
            &mut left_current
        } else if later_than(&right_current, &left_current) {
            &mut right_current
        } else {
            return Err(FoldFrameRefusal::UnrelatedStates { name });
        };
        let Some(step) = newer.derivation() else {
            return Err(FoldFrameRefusal::UnrelatedStates { name });
        };
        step_misses_interval(&step, newer, &left_interval, empty, assumptions).map_err(
            |(kind, detail)| FoldFrameRefusal::StepNotShownOutside {
                name: name.clone(),
                step: kind,
                detail,
            },
        )?;
        crossed += 1;
        *newer = step.base().clone();
    }
    Ok(crossed)
}

fn later_than(left: &SharedMemory, right: &SharedMemory) -> bool {
    let (left_arena, left_id) = left.arena_id();
    let (right_arena, right_id) = right.arena_id();
    left_arena == right_arena && left_id > right_id
}

/// Whether one recorded step leaves every cell of the interval unchanged.
fn step_misses_interval(
    step: &MemoryDerivation,
    produced: &SharedMemory,
    interval: &FoldReadInterval,
    empty: bool,
    assumptions: &PureFactContext,
) -> Result<(), (&'static str, &'static str)> {
    // A step the assumption-free whole-block rule separates from the array's
    // block leaves every byte of it alone, cells included. That rule reads no
    // fact, so this reuses its answer without widening it.
    let block_separate = matches!(
        step_effect::affects(
            step,
            produced,
            TrackedResource::Block(&interval.base.base),
            &step_effect::Evidence {
                assumptions: &PureFactContext::new(),
                cross_loop_havoc: false,
            },
        ),
        step_effect::StepEffect::Separate(_)
    );
    if block_separate {
        return Ok(());
    }
    match step {
        // This edge changes only cached knowledge, not any byte or lifetime.
        // Its producer records it only for unconditional forgetting, never
        // for havoc or assumption-dependent pruning.
        MemoryDerivation::CellsForgotten { .. } => Ok(()),
        MemoryDerivation::Store { pointer, value, .. } => {
            if empty || access_misses_interval(pointer, value.byte_width(), interval, assumptions) {
                Ok(())
            } else {
                Err((
                    "store",
                    "no exact fact places the written bytes at or above the fold's end or below its start, and no stated separation holds them apart",
                ))
            }
        }
        // A seeded run is the stores it stands for, each framed as one.
        MemoryDerivation::CellsSeeded { .. } => {
            let stores = step.seeded_stores().expect("a CellsSeeded edge");
            if empty
                || stores.iter().all(|(pointer, value)| {
                    access_misses_interval(pointer, value.byte_width(), interval, assumptions)
                })
            {
                Ok(())
            } else {
                Err((
                    "store",
                    "no exact fact places the written bytes at or above the fold's end or below its start, and no stated separation holds them apart",
                ))
            }
        }
        MemoryDerivation::CallHavoc { mutable_ranges, .. } => {
            if empty
                || mutable_ranges
                    .iter()
                    .all(|written| range_misses_interval(written, interval, assumptions))
            {
                Ok(())
            } else {
                Err((
                    "call",
                    "a range the callee may write is not shown outside the fold's cells",
                ))
            }
        }
        other => Err((
            other.kind_name(),
            "only stores and calls with a checked write set are framed; allocation, free, lifetime and loop steps keep the conservative whole-block rule",
        )),
    }
}

/// One exact linear form of a pointer offset: a constant plus integer
/// coefficients of opaque atoms. Every atom is a term whose value the offset
/// reads exactly (a sign-extended `int32`, a 64-bit index, or an offset
/// variable), so the form is the offset's `i64` value with no wraparound.
#[derive(Clone, Debug, Default)]
struct LinearOffset {
    constant: i128,
    atoms: BTreeMap<OffsetAtom, i128>,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum OffsetAtom {
    Variable(Variable),
    Int32(SharedMachineIntegerTerm),
    Int64 {
        value: SharedMachineIntegerTerm,
        unsigned: bool,
    },
}

impl LinearOffset {
    fn of(offset: &OldAddressOffset) -> Self {
        let mut linear = Self::default();
        let mut pending = vec![(offset, 1i128)];
        while let Some((offset, sign)) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match offset {
                OldAddressOffset::Constant(value) => linear.constant += sign * i128::from(*value),
                OldAddressOffset::Variable(variable) => {
                    linear.add_atom(OffsetAtom::Variable(*variable), sign)
                }
                OldAddressOffset::Add(left, right) => {
                    pending.push((left, sign));
                    pending.push((right, sign));
                }
                OldAddressOffset::Int32Scaled { value, byte_width } => {
                    match value.operand_view().word32_constant() {
                        Some(value) => {
                            linear.constant +=
                                sign * i128::from(value as i32) * i128::from(*byte_width)
                        }
                        None => linear.add_atom(
                            OffsetAtom::Int32(value.clone()),
                            sign * i128::from(*byte_width),
                        ),
                    }
                }
                OldAddressOffset::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => linear.add_atom(
                    OffsetAtom::Int64 {
                        value: value.clone(),
                        unsigned: *unsigned,
                    },
                    sign * i128::from(*byte_width),
                ),
            }
        }
        linear
    }

    fn add_atom(&mut self, atom: OffsetAtom, coefficient: i128) {
        let entry = self.atoms.entry(atom).or_insert(0);
        *entry += coefficient;
    }

    fn minus(mut self, other: &Self) -> Self {
        self.constant -= other.constant;
        for (atom, coefficient) in &other.atoms {
            crate::instrumentation::record_deterministic_work(1);
            self.add_atom(atom.clone(), -coefficient);
        }
        self.atoms.retain(|_, coefficient| *coefficient != 0);
        self
    }

    /// The form `element_width * sext(index) + constant`, when this is one:
    /// no atom at all (index `0`), or exactly one `int32` atom whose
    /// coefficient is the element width.
    fn as_scaled_index(&self, element_width: u32) -> Option<(SharedMachineIntegerTerm, i128)> {
        match self.atoms.len() {
            // A constant delta names a constant index: the whole elements it
            // spans, when that is an `int32`, and the bytes left over.
            0 => {
                let width = i128::from(element_width);
                let index = self.constant.div_euclid(width);
                let index = i32::try_from(index).ok()?;
                Some((
                    SharedMachineIntegerTerm::intern(
                        MachineIntegerType::Int32,
                        OldMachineTerm::constant(index as u32),
                    ),
                    self.constant - i128::from(index) * width,
                ))
            }
            1 => {
                let (atom, coefficient) = self.atoms.iter().next()?;
                match atom {
                    OffsetAtom::Int32(index) if *coefficient == i128::from(element_width) => {
                        Some((index.clone(), self.constant))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

/// `element_width * sext(index) + constant` for `pointer` relative to `base`,
/// when both are in one block and the delta has that exact form.
fn scaled_index_from(
    pointer: &OldAddress,
    base: &OldAddress,
    element_width: u32,
) -> Option<(SharedMachineIntegerTerm, i128)> {
    if pointer.base != base.base {
        return None;
    }
    LinearOffset::of(&pointer.offset)
        .minus(&LinearOffset::of(&base.offset))
        .as_scaled_index(element_width)
}

/// `left <= right` as signed `int32`, from syntax, constants, or one exact
/// fact. Only indexed lookups: nothing scans the context.
fn proven_signed_le(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    proven_signed_le_views(
        MachineOperandView::Old(left),
        MachineOperandView::Old(right),
        assumptions,
    )
}

fn proven_signed_le_views(
    left: MachineOperandView<'_>,
    right: MachineOperandView<'_>,
    assumptions: &PureFactContext,
) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    if left.retain(MachineIntegerType::Int32) == right.retain(MachineIntegerType::Int32) {
        return true;
    }
    if let (Some(left), Some(right)) = (left.word32_constant(), right.word32_constant()) {
        return (left as i32) <= (right as i32);
    }
    [CompareRelation::LessEqual, CompareRelation::LessThan]
        .into_iter()
        .any(|relation| {
            assumptions.selected_comparison_value(&crate::kernel::assumptions::index_comparison(
                relation, left, right,
            )) == Some(true)
        })
}

/// `left < right` from constants or one exact selected fact.
fn proven_signed_lt_views(
    left: MachineOperandView<'_>,
    right: MachineOperandView<'_>,
    assumptions: &PureFactContext,
) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    if let (Some(left), Some(right)) = (left.word32_constant(), right.word32_constant()) {
        return (left as i32) < (right as i32);
    }
    left.retain(MachineIntegerType::Int32) != right.retain(MachineIntegerType::Int32)
        && (assumptions.selected_comparison_value(&crate::kernel::assumptions::index_comparison(
            CompareRelation::LessThan,
            left,
            right,
        )) == Some(true)
            || assumptions.selected_comparison_value(
                &crate::kernel::assumptions::index_comparison(
                    CompareRelation::LessEqual,
                    right,
                    left,
                ),
            ) == Some(false))
}

/// The interval reads no cell because its end is proven at or below its
/// start. Unknown order is not emptiness.
fn interval_proven_empty(interval: &FoldReadInterval, assumptions: &PureFactContext) -> bool {
    proven_signed_le_views(
        interval.end.operand_view(),
        interval.start.operand_view(),
        assumptions,
    )
}

/// Whether the `bytes` bytes at `pointer` miss every cell of the interval.
fn access_misses_interval(
    pointer: &OldAddress,
    bytes: u32,
    interval: &FoldReadInterval,
    assumptions: &PureFactContext,
) -> bool {
    if bytes == 0 || pointer.blocks_proven_distinct(&interval.base) {
        return true;
    }
    if let Some((index, constant)) =
        scaled_index_from(pointer, &interval.base, interval.element_width)
    {
        let width = i128::from(interval.element_width);
        // The write starts at `width*index + constant`. At or above the end
        // cell's first byte when `index >= end` and `constant >= 0`; ending at
        // or below the start cell's first byte when `index < start` and the
        // write fits in the cell it starts in (`constant + bytes <= width`).
        let above = constant >= 0
            && proven_signed_le_views(
                interval.end.operand_view(),
                index.operand_view(),
                assumptions,
            );
        let below = constant + i128::from(bytes) <= width
            && proven_signed_lt_views(
                index.operand_view(),
                interval.start.operand_view(),
                assumptions,
            );
        if above || below {
            return true;
        }
    }
    separated_by_stated_fact(
        |range| range_contains_interval(range, interval, assumptions),
        |range| range_contains_access(range, pointer, bytes, assumptions),
        &interval.base.base,
        &pointer.base,
        assumptions,
    )
}

/// Whether one range a callee may write misses every cell of the interval.
fn range_misses_interval(
    written: &MemoryRange,
    interval: &FoldReadInterval,
    assumptions: &PureFactContext,
) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    if written.base().blocks_proven_distinct(&interval.base) {
        return true;
    }
    // Same-block arithmetic uses signed indices; native spans are undecided.
    if written.wide_bounds().is_some() {
        return false;
    }
    if written.element_width() == interval.element_width
        && scaled_index_from(written.base(), &interval.base, interval.element_width).is_some_and(
            |(index, rest)| rest == 0 && index.operand_view().word32_constant() == Some(0),
        )
    {
        // Same base and element width: the written cells are
        // `[written.start, written.end)` of the same array. The range must be
        // proven well formed first; a reversed range is never read as empty,
        // because nothing here decides what bytes such a write set covers.
        if proven_signed_le(written.start(), written.end(), assumptions)
            && (proven_signed_le_views(
                MachineOperandView::Old(written.end()),
                interval.start.operand_view(),
                assumptions,
            ) || proven_signed_le_views(
                interval.end.operand_view(),
                MachineOperandView::Old(written.start()),
                assumptions,
            ))
        {
            return true;
        }
    }
    separated_by_stated_fact(
        |range| range_contains_interval(range, interval, assumptions),
        |range| range_contains_range(range, written, assumptions),
        &interval.base.base,
        &written.base().base,
        assumptions,
    )
}

/// A stated `separate(memory(L), memory(R))` with the interval inside one side
/// and the write inside the other, both decided by exact order facts.
fn separated_by_stated_fact(
    holds_interval: impl Fn(&MemoryRange) -> bool,
    holds_write: impl Fn(&MemoryRange) -> bool,
    interval_block: &AddressBase,
    write_block: &AddressBase,
    assumptions: &PureFactContext,
) -> bool {
    assumptions
        .memory_separation_candidates(interval_block, write_block)
        .any(|(proposition, left, right)| {
            crate::instrumentation::record_deterministic_work(1);
            let oriented = holds_interval(left) && holds_write(right)
                || holds_interval(right) && holds_write(left);
            let holds =
                oriented && !assumptions.memory_ranges_overlap_after_base_equality(left, right);
            if holds {
                crate::kernel::record_implicit_consulted_premises(assumptions, proposition);
            }
            holds
        })
}

/// The interval's cells lie inside `range`: the same base and element width,
/// `range.start <= start` and `end <= range.end`.
fn range_contains_interval(
    range: &MemoryRange,
    interval: &FoldReadInterval,
    assumptions: &PureFactContext,
) -> bool {
    // This arithmetic rule uses signed 32-bit indices; wide ranges are undecided.
    if range.wide_bounds().is_some() {
        return false;
    }
    range.element_width() == interval.element_width
        && scaled_index_from(&interval.base, range.base(), interval.element_width).is_some_and(
            |(index, rest)| rest == 0 && index.operand_view().word32_constant() == Some(0),
        )
        && proven_signed_le_views(
            MachineOperandView::Old(range.start()),
            interval.start.operand_view(),
            assumptions,
        )
        && proven_signed_le_views(
            interval.end.operand_view(),
            MachineOperandView::Old(range.end()),
            assumptions,
        )
}

/// The `bytes` bytes at `pointer` lie inside one cell of `range`.
fn range_contains_access(
    range: &MemoryRange,
    pointer: &OldAddress,
    bytes: u32,
    assumptions: &PureFactContext,
) -> bool {
    // This arithmetic rule uses signed 32-bit indices; wide ranges are undecided.
    if range.wide_bounds().is_some() {
        return false;
    }
    let width = range.element_width();
    let Some((index, constant)) = scaled_index_from(pointer, range.base(), width) else {
        return false;
    };
    constant >= 0
        && constant + i128::from(bytes) <= i128::from(width)
        && proven_signed_le_views(
            MachineOperandView::Old(range.start()),
            index.operand_view(),
            assumptions,
        )
        && proven_signed_lt_views(
            index.operand_view(),
            MachineOperandView::Old(range.end()),
            assumptions,
        )
}

/// `inner` lies inside `outer`: the same base and element width and nested
/// endpoints.
fn range_contains_range(
    outer: &MemoryRange,
    inner: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    // This arithmetic rule uses signed 32-bit indices; wide ranges are undecided.
    if outer.wide_bounds().is_some() || inner.wide_bounds().is_some() {
        return false;
    }
    outer.element_width() == inner.element_width()
        && scaled_index_from(inner.base(), outer.base(), inner.element_width()).is_some_and(
            |(index, rest)| rest == 0 && index.operand_view().word32_constant() == Some(0),
        )
        && proven_signed_le(inner.start(), inner.end(), assumptions)
        && proven_signed_le(outer.start(), inner.start(), assumptions)
        && proven_signed_le(inner.end(), outer.end(), assumptions)
}

#[path = "tests.rs"]
mod tests;
