//! Checked operations on iterated guarded ownership (`Resource::Iterated`).
//!
//! The fact itself is defined in `primitives/iterated.rs`. Everything here
//! answers a question about one index or one C store, so each operation reads
//! the one fact it names, the index's range membership, the guard cell at that
//! index, and the fact's holes. Nothing enumerates the index range.
//!
//! The invariant every operation preserves: the fact holds, for each index
//! `k` of its range that is not a hole, the element at `k` exactly when the
//! guard at `k` holds in the *current* memory. The guard cells are owned
//! beside the fact (validation requires the body to own them), so only this
//! context can change them, and every change goes through
//! [`plan_iterated_guard_store`] or drops the fact.

use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

/// The element-level proof steps and the whole-range conversions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum IteratedStep {
    /// The named clause supplies the range at the written index.
    UnfoldSlot {
        template: IteratedMemory,
        index: MachineTerm,
    },
    FoldSlot {
        template: IteratedMemory,
        index: MachineTerm,
    },
    /// `fold(resource[..])`: form `template` (a hole-free fact) from the
    /// covering owned range when every guard is known true, or from nothing
    /// when every guard is known false.
    FoldClause { template: IteratedMemory },
    /// `unfold(resource[..])`: the converse of `fold(resource[..])`.
    UnfoldClause { template: IteratedMemory },
}

/// Decides one condition from the fact context: `Some(true)`, `Some(false)`,
/// or `None` when neither is established.
fn decide(assumptions: &PureFactContext, condition: ConditionTerm) -> Option<bool> {
    crate::instrumentation::record_deterministic_work(1);
    assumptions.decide(&condition)
}

fn proves(assumptions: &PureFactContext, condition: ConditionTerm) -> bool {
    decide(assumptions, condition) == Some(true)
}

fn terms_equal(assumptions: &PureFactContext, left: &MachineTerm, right: &MachineTerm) -> bool {
    left == right
        // `2 * index` and `index * 2` are one element offset: their affine
        // forms agree, with no fact consulted.
        || crate::kernel::assumptions::affine_bitvector_difference_constant(left, right) == Some(0)
        || proves(
            assumptions,
            ConditionTerm::Compare { format: MachineIntegerType::Int32, relation: CompareRelation::Equal, left: crate::kernel::ConditionOperand::new(left.clone()), right: crate::kernel::ConditionOperand::new(right.clone()) },
        )
}

fn terms_distinct(assumptions: &PureFactContext, left: &MachineTerm, right: &MachineTerm) -> bool {
    left != right
        && decide(
            assumptions,
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: crate::kernel::ConditionOperand::new(left.clone()),
                right: crate::kernel::ConditionOperand::new(right.clone()),
            },
        ) == Some(false)
}

/// Whether `index` lies in the fact's range, by the fact context.
fn index_in_range(
    assumptions: &PureFactContext,
    iterated: &IteratedMemory,
    index: &MachineTerm,
) -> bool {
    proves(
        assumptions,
        ConditionTerm::signed_less_equal(iterated.lower().clone(), index.clone()),
    ) && proves(
        assumptions,
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: crate::kernel::ConditionOperand::new(index.clone()),
            right: crate::kernel::ConditionOperand::new(iterated.upper().clone()),
        },
    )
}

/// Whether `index` lies outside the fact's range, by the fact context.
fn index_out_of_range(
    assumptions: &PureFactContext,
    iterated: &IteratedMemory,
    index: &MachineTerm,
) -> bool {
    proves(
        assumptions,
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: crate::kernel::ConditionOperand::new(index.clone()),
            right: crate::kernel::ConditionOperand::new(iterated.lower().clone()),
        },
    ) || proves(
        assumptions,
        ConditionTerm::signed_less_equal(iterated.upper().clone(), index.clone()),
    )
}

/// The guard's truth for a guard cell holding `cell`.
fn guard_holds_for(
    assumptions: &PureFactContext,
    iterated: &IteratedMemory,
    cell: &MachineTerm,
) -> Option<bool> {
    let equal = decide(
        assumptions,
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: crate::kernel::ConditionOperand::new(cell.clone()),
            right: crate::kernel::ConditionOperand::new(iterated.guard().value().clone()),
        },
    )?;
    Some(equal == iterated.guard().holds_when_equal())
}

/// The logical guard value in this state. Folding the clause does not
/// execute a C read: it needs the guard's truth, while the surrounding rule
/// separately requires ownership of the guard range. A logical value fact
/// never establishes that a subsequent C load is initialized.
fn guard_cell_value(
    state: &ExecutionState,
    iterated: &IteratedMemory,
    index: &MachineTerm,
    assumptions: &PureFactContext,
) -> Result<MachineTerm, String> {
    // A guard cell holding a value is that value (the read-over-write
    // authority); only an unknown cell is read as a named load.
    let cell = iterated.guard_cell(index);
    if let Some(ProgramValue::Int32(value)) = state
        .memory()
        .known_value(&cell)
        .and_then(|stored| iterated.guard().cell_type.read_cell(&stored))
    {
        return Ok(value);
    }
    if let Some(kind) = LoadKind::of_type(iterated.guard().cell_type)
        && let Some(entry) = state.program_point().entry_integer_version(&cell, kind)
    {
        return Ok(MachineTerm::MemoryLoad(entry, Box::new(cell), kind));
    }
    let paths = crate::kernel::eval::evaluate_logical_memory_load_paths(
        state.memory(),
        cell,
        iterated.guard().cell_type,
        Vec::new().into(),
        Vec::new(),
        assumptions,
    );
    match paths.as_slice() {
        [
            ExpressionPath {
                outcome: ExpressionOutcome::Value(ProgramValue::Int32(value)),
                facts,
                obligations,
            },
        ] if facts
            .iter()
            .all(|fact| assumptions.proves_exact(fact.proposition()))
            && obligations.is_empty() =>
        {
            Ok(value.clone())
        }
        _ => Err("the iterated guard does not denote one logical int32 value".into()),
    }
}

/// The guard's truth at `index` in `state`: `Some(true)` when the fact
/// context proves it holds, `Some(false)` when it proves it fails, and
/// `None` when neither is established.
pub(crate) fn iterated_guard_at(
    state: &ExecutionState,
    iterated: &IteratedMemory,
    index: &MachineTerm,
    assumptions: &PureFactContext,
) -> Result<Option<bool>, String> {
    let cell = guard_cell_value(state, iterated, index, assumptions)?;
    Ok(guard_holds_for(assumptions, iterated, &cell))
}

/// Whether the fact holds the element at `index`: `Some(true)` when the index
/// is in range, not a hole, and its guard is known true; `Some(false)` when
/// the index is out of range, a hole, or its guard is known false; `None`
/// ("may hold") otherwise. This is the containment and separation question
/// for one element, answered from one guard cell and the holes.
pub(crate) fn iterated_holds_element(
    state: &ExecutionState,
    iterated: &IteratedMemory,
    index: &MachineTerm,
    assumptions: &PureFactContext,
) -> Option<bool> {
    if index_out_of_range(assumptions, iterated, index)
        || iterated
            .holes()
            .iter()
            .any(|hole| terms_equal(assumptions, hole.native_compat(), index))
    {
        return Some(false);
    }
    let guard = iterated_guard_at(state, iterated, index, assumptions).ok()?;
    match guard {
        Some(false) => Some(false),
        Some(true)
            if index_in_range(assumptions, iterated, index)
                && iterated
                    .holes()
                    .iter()
                    .all(|hole| terms_distinct(assumptions, hole.native_compat(), index)) =>
        {
            Some(true)
        }
        _ => None,
    }
}

/// Whether the fact is proved to hold nothing in `range`: the range is in
/// another block, or the element block's elements of the fact lie entirely
/// outside it by constant bounds. Constant in the fact's range size.
pub(crate) fn iterated_separate_from_range(
    iterated: &IteratedMemory,
    range: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    if range.base().blocks_proven_distinct(iterated.element_base()) {
        return true;
    }
    let Some(covering) = iterated.covering_range().or_else(|| {
        // Gapped elements are covered by the range from the first element's
        // start to the last element's end.
        // IteratedMemory::element_range always constructs signed int32 bounds.
        let first = iterated.element_range(iterated.lower());
        let last = iterated.element_range(&MachineTerm::subtract(
            iterated.upper().clone(),
            MachineTerm::constant(1),
        ));
        Some(MemoryRange::new_with_element_width(
            iterated.element_base().clone(),
            first.start().clone(),
            last.end().clone(),
            iterated.element_width(),
        ))
    }) else {
        return false;
    };
    assumptions.proves_resource_separate(
        &Resource::Memory(covering),
        &Resource::Memory(range.clone()),
    )
}

fn replace_iterated(
    resources: ResourceContext,
    current: &ResourceFact,
    next: IteratedMemory,
) -> Result<ResourceContext, String> {
    resources
        .without_exact_representation(current)
        .map(|resources| resources.unchecked_with_fact(ResourceFact::own(Resource::iterated(next))))
        .ok_or_else(|| "the iterated ownership fact is not held".to_string())
}

fn unfold_slot(
    state: &ExecutionState,
    current: &ResourceFact,
    iterated: &IteratedMemory,
    index: &MachineTerm,
    assumptions: &PureFactContext,
) -> Result<ExecutionState, String> {
    if !index_in_range(assumptions, iterated, index) {
        return Err(
            "the index is not known to lie in the iterated range; establish `lo <= index` and `index < hi` first"
                .to_string(),
        );
    }
    if let Some(hole) = iterated
        .holes()
        .iter()
        .find(|hole| !terms_distinct(assumptions, hole.native_compat(), index))
    {
        let _ = hole;
        return Err(
            "this element may already be taken out: the index is not known to differ from an element taken out earlier"
                .to_string(),
        );
    }
    match iterated_guard_at(state, iterated, index, assumptions)? {
        Some(true) => {}
        Some(false) => {
            return Err(
                "the guard is false at this index, so the iterated ownership fact holds no element there"
                    .to_string(),
            );
        }
        None => {
            return Err(
                "the guard at this index is not known to hold; state the guard cell's value as a fact first"
                    .to_string(),
            );
        }
    }
    let next = iterated.with_hole(index.clone());
    let resources = replace_iterated(state.resources().clone(), current, next)?;
    // The checked owner lost exactly this element to its new hole.
    // Guard stores preserve that partition; exposing the element is
    // construction in this same frame, not new ownership admission.
    // Keep unrelated occurrences and support metadata untouched.
    let resources =
        resources.unchecked_with_fact(ResourceFact::own_memory(iterated.element_range(index)));
    Ok(state.clone().with_resource_context(resources))
}

fn fold_slot(
    state: &ExecutionState,
    current: &ResourceFact,
    iterated: &IteratedMemory,
    index: &MachineTerm,
    assumptions: &PureFactContext,
) -> Result<ExecutionState, String> {
    match iterated_guard_at(state, iterated, index, assumptions)? {
        Some(true) => {}
        Some(false) => {
            return Err(
                "the guard is false at this index, so the iterated ownership fact cannot hold the element; set the guard cell first"
                    .to_string(),
            );
        }
        None => {
            return Err(
                "the guard at this index is not known to hold; state the guard cell's value as a fact first"
                    .to_string(),
            );
        }
    }
    let Some(position) = iterated
        .holes()
        .iter()
        .position(|hole| terms_equal(assumptions, hole.native_compat(), index))
    else {
        return Err(
            "this element was not taken out of the iterated ownership fact; only an element taken out, or whose guard a store just made true, can be given back"
                .to_string(),
        );
    };
    let next = iterated.without_hole_at(position);
    // Selection checked the base and exact element shape. Consume in
    // that clause's coordinates instead of rediscovering its held
    // supplier through a later pointer-read spelling.
    let owned_element = iterated.element_range(index);
    let resources = state
        .resources()
        .clone()
        .without_fact_incrementally(&ResourceFact::own_memory(owned_element), assumptions)
        .ok_or_else(|| "the element is not owned here".to_string())?;
    let resources = replace_iterated(resources, current, next)?;
    Ok(state.clone().with_resource_context(resources))
}

/// Applies one checked iterated-ownership step to `state`. Each step reads
/// the one fact it names, one guard cell, the fact's holes, and the element
/// it moves; the index range is never enumerated.
pub(crate) fn apply_iterated_step(
    state: &ExecutionState,
    step: &IteratedStep,
    assumptions: &PureFactContext,
) -> Result<ExecutionState, String> {
    match step {
        IteratedStep::UnfoldSlot { template, index }
        | IteratedStep::FoldSlot { template, index } => {
            let current = state.resources().owned_iterated_clause(template)?;
            let Resource::Iterated(iterated) = current.resource() else {
                unreachable!("the iterated clause index holds only iterated facts");
            };
            match step {
                IteratedStep::UnfoldSlot { .. } => {
                    unfold_slot(state, current, iterated, index, assumptions)
                }
                _ => fold_slot(state, current, iterated, index, assumptions),
            }
        }
        IteratedStep::FoldClause { template } => {
            if !template.holes().is_empty() {
                return Err(
                    "folding the whole clause requires a template with no open slots".to_string(),
                );
            }
            // The guard is read against cells this context owns, exactly as
            // a declaration's guard reads cells its own body owns; otherwise
            // someone else could change which elements the fact claims.
            if !state.resources().satisfies_fact(
                &ResourceFact::own_memory(template.guard_range()),
                assumptions,
            ) {
                return Err(
                    "folding the whole clause needs ownership of every guard cell of the range"
                        .to_string(),
                );
            }
            match every_guard(state, template, assumptions)? {
                Some(true) => {
                    let covering = template.covering_range().ok_or_else(|| {
                        "the elements do not tile one range"
                            .to_string()
                    })?;
                    let resources = state
                        .resources()
                        .clone()
                        .without_fact_incrementally(&ResourceFact::own_memory(covering), assumptions)
                        .ok_or_else(|| {
                            "folding the whole clause needs ownership of every element's cells".to_string()
                        })?;
                    Ok(state.clone().with_resource_context(resources.unchecked_with_fact(
                        ResourceFact::own(Resource::iterated(template.clone())),
                    )))
                }
                Some(false) => Ok(state.clone().with_resource_context(
                    state.resources().clone().unchecked_with_fact(ResourceFact::own(
                        Resource::iterated(template.clone()),
                    )),
                )),
                None => Err(
                    "folding the whole clause needs every guard known: a fact `forall (k: int32) { lo <= k and k < hi implies guard }` or its negation"
                        .to_string(),
                ),
            }
        }
        IteratedStep::UnfoldClause { template } => Ok(state.clone().with_resource_context(
            prepare_iterated_clause_unfold(state, template, assumptions)?.install(),
        )),
    }
}

/// The checked whole-clause unfold retains the exact residual frame. Installation
/// consumes that construction; it neither repeats guard reasoning nor admits a
/// newly described range beside an independently supplied frame.
struct ConstructedIteratedExposure {
    frame: ResourceContext,
    range: Option<MemoryRange>,
}

impl ConstructedIteratedExposure {
    fn install(self) -> ResourceContext {
        match self.range {
            Some(range) => self
                .frame
                .unchecked_with_fact(ResourceFact::own_memory(range)),
            None => self.frame,
        }
    }
}

fn prepare_iterated_clause_unfold(
    state: &ExecutionState,
    template: &IteratedMemory,
    assumptions: &PureFactContext,
) -> Result<ConstructedIteratedExposure, String> {
    let required = ResourceFact::own(Resource::iterated(template.clone()));
    let frame = state
        .resources()
        .clone()
        .without_fact_incrementally(&required, assumptions)
        .ok_or_else(|| {
            "unfolding the whole clause needs the iterated ownership fact with no element taken out"
                .to_string()
        })?;
    let range = match every_guard(state, template, assumptions)? {
        Some(true) => Some(template.covering_range().ok_or_else(||
            "the elements do not tile one range".to_string())?),
        Some(false) => None,
        None => return Err("unfolding the whole clause needs every guard known: a fact `forall (k: int32) { lo <= k and k < hi implies guard }` or its negation".to_string()),
    };
    Ok(ConstructedIteratedExposure { frame, range })
}

/// The reserved identity of the arbitrary index whole-clause folding and unfolding
/// instantiate the range's guard at. It is bound only inside the one
/// hypothetical fact context those checks build.
const ITERATED_GUARD_INDEX: Variable = Variable(u64::MAX - 0x6974_6572);

/// Whether every guard of the range is known true (`Some(true)`) or known
/// false (`Some(false)`): the universally quantified guard at a fresh index is
/// instantiated once and decided under the range hypotheses. One decision,
/// independent of the range's size.
fn every_guard(
    state: &ExecutionState,
    iterated: &IteratedMemory,
    assumptions: &PureFactContext,
) -> Result<Option<bool>, String> {
    let index = MachineTerm::Variable(ITERATED_GUARD_INDEX);
    let hypotheses = assumptions
        .clone()
        .assume_proposition(Proposition::condition_is(
            ConditionTerm::signed_less_equal(iterated.lower().clone(), index.clone()),
            true,
        ))
        .assume_proposition(Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: crate::kernel::ConditionOperand::new(index.clone()),
                right: crate::kernel::ConditionOperand::new(iterated.upper().clone()),
            },
            true,
        ));
    let cell = guard_cell_value(state, iterated, &index, &hypotheses)?;
    if let Some(value) = guard_holds_for(&hypotheses, iterated, &cell) {
        return Ok(Some(value));
    }
    let antecedent = Proposition::And(
        Box::new(Proposition::condition_is(
            ConditionTerm::signed_less_equal(iterated.lower().clone(), index.clone()),
            true,
        )),
        Box::new(Proposition::condition_is(
            ConditionTerm::signed_less_than(index, iterated.upper().clone()),
            true,
        )),
    );
    let Some((value, equal)) = hypotheses.selected_universal_equality_value(
        ITERATED_GUARD_INDEX,
        antecedent,
        &cell,
        iterated.guard().value(),
    ) else {
        return Ok(None);
    };
    if equal {
        Ok(guard_holds_for(&hypotheses, iterated, &value))
    } else {
        Ok((hypotheses.decide(&ConditionTerm::equal(
            value,
            iterated.guard().value().clone(),
        )) == Some(true))
        .then_some(!iterated.guard().holds_when_equal()))
    }
}

/// The frame of a loop that declares its own resources, without the iterated
/// facts whose guard cells the loop may write. The body executes without
/// those facts (a declaring loop's body holds only what it declares), so no
/// store in it passes the store rule for them; after the loop the guard
/// cells may hold anything, and a fact read against them would claim cells
/// nobody checked. Dropping the fact is the sound answer: the elements are
/// lost to this frame, never claimed twice.
pub(crate) fn frame_out_iterated_facts_written_by_loop(
    state: ExecutionState,
    written: Option<&[MemoryRange]>,
) -> ExecutionState {
    if !state.resources().has_iterated_facts() {
        return state;
    }
    let mut resources = state.resources().clone();
    for fact in state.resources().iterated_facts() {
        let Resource::Iterated(iterated) = fact.resource() else {
            continue;
        };
        let guard_block = &iterated.guard().base().base;
        let written_here = written.is_none_or(|ranges| {
            ranges.iter().any(|range| {
                &range.base().base == guard_block
                    || !range.base().base.proven_distinct(guard_block)
                        && (range.base().has_symbolic_block()
                            || iterated.guard().base().has_symbolic_block())
            })
        });
        if written_here && let Some(next) = resources.clone().without_exact_representation(&fact) {
            resources = next;
        }
    }
    state.with_resource_context(resources)
}

/// What a C store to `pointer` does to the iterated facts whose guard cells
/// share its block: for each fact, the representation to hold while the store
/// writes and the one to hold after it.
pub(crate) struct IteratedStorePlan {
    replacements: Vec<(ResourceFact, IteratedMemory, IteratedMemory)>,
}

impl IteratedStorePlan {
    /// The resource context with every affected fact in its during-store
    /// form: the stored index is a hole, so the store changes nothing the
    /// fact claims.
    pub(crate) fn before_store(
        &self,
        resources: ResourceContext,
    ) -> Result<ResourceContext, String> {
        self.replacements
            .iter()
            .try_fold(resources, |resources, (current, during, _)| {
                replace_iterated(resources, current, during.clone())
            })
    }

    /// The resource context with every affected fact in its after-store form.
    pub(crate) fn after_store(
        &self,
        resources: ResourceContext,
    ) -> Result<ResourceContext, String> {
        self.replacements
            .iter()
            .try_fold(resources, |resources, (_, during, after)| {
                if during == after {
                    return Ok(resources);
                }
                replace_iterated(
                    resources,
                    &ResourceFact::own(Resource::iterated(during.clone())),
                    after.clone(),
                )
            })
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.replacements.is_empty()
    }
}

/// The store rule. A store of `value` to `pointer` may change a guard cell,
/// and so change which elements an iterated fact claims. It is permitted at
/// index `j` exactly when
///
/// - `j` is outside the fact's range, or
/// - `j` is a hole (its element was taken out), or
/// - the guard at `j` is known false before the store, or the element at `j`
///   is owned outright beside the fact (either way the fact holds nothing at
///   `j`).
///
/// In every permitted case the fact makes no claim at `j` while the store
/// writes, so the store cannot change what it holds. After the store `j`
/// stays a hole unless it is out of range or the stored value makes the guard
/// known false; a store that makes the guard true therefore leaves `j` a hole
/// until indexed `fold` restores the element. A store at an index whose element the
/// fact may still hold is refused: it would silently change the fact.
pub(crate) fn plan_iterated_guard_store(
    state: &ExecutionState,
    pointer: &Address,
    value: &ProgramValue,
    assumptions: &PureFactContext,
) -> Result<IteratedStorePlan, String> {
    let resources = state.resources();
    let mut replacements = Vec::new();
    if !resources.has_iterated_facts() {
        return Ok(IteratedStorePlan { replacements });
    }
    for fact in resources.iterated_facts_in_block(&pointer.base) {
        let ResourceFact::Own(Resource::Iterated(iterated), _) = fact else {
            continue;
        };
        if iterated.guard().base().base != pointer.base {
            continue;
        }
        // Owned memory is a partition: a cell one owned range authorizes
        // cannot be a guard cell another owned range holds.
        let written = Resource::Memory(MemoryRange::new_with_element_width(
            pointer.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(1),
            value.byte_width().max(1),
        ));
        if resources.proves_owned_resources_separate(
            &written,
            &Resource::Memory(iterated.guard_range()),
            assumptions,
        ) {
            continue;
        }
        let refusal = |reason: &str| {
            format!(
                "this store may change a guard cell of the iterated ownership of `{}`, which would change the elements it holds: {reason}; unfold the iterated slot at this index first, or establish that its guard is false",
                iterated.owner()
            )
        };
        let Some(index) = pointer.element_index_from_base_with_width(
            iterated.guard().base(),
            iterated.guard().cell_width,
        ) else {
            return Err(refusal(
                "the stored address is not a guard cell Click can index",
            ));
        };
        if value.byte_width() != iterated.guard().cell_width {
            return Err(refusal("the store does not write one whole guard cell"));
        }
        let ProgramValue::Int32(stored) = value else {
            return Err(refusal("the stored value is not an `int32`"));
        };
        let out_of_range = index_out_of_range(assumptions, iterated, &index);
        let hole = iterated
            .holes()
            .iter()
            .position(|hole| terms_equal(assumptions, hole.native_compat(), &index));
        let during = match hole {
            // Respell the hole as the stored index so the write's own
            // derivation names it structurally.
            Some(position) => iterated.without_hole_at(position).with_hole(index.clone()),
            None if out_of_range => iterated.with_hole(index.clone()),
            // The element is owned outright beside the fact. Owned memory is
            // a partition, so the fact cannot hold it: at this index it
            // claims nothing, whatever the guard cell says.
            None if resources.satisfies_fact(
                &ResourceFact::own_memory(iterated.element_range(&index)),
                assumptions,
            ) =>
            {
                iterated.with_hole(index.clone())
            }
            None => match iterated_holds_element(state, iterated, &index, assumptions) {
                Some(false) => iterated.with_hole(index.clone()),
                Some(true) => {
                    return Err(refusal(
                        "the guard holds at this index, so the fact still holds its element",
                    ));
                }
                None => {
                    return Err(refusal(
                        "the guard at this index is not known, so the fact may hold its element",
                    ));
                }
            },
        };
        let stored_guard = guard_holds_for(assumptions, iterated, stored);
        let after = if out_of_range || stored_guard == Some(false) {
            let position = during.holes().len() - 1;
            during.without_hole_at(position)
        } else {
            during.clone()
        };
        replacements.push((fact.clone(), during, after));
    }
    Ok(IteratedStorePlan { replacements })
}

#[cfg(test)]
mod scaling_tests {
    include!("../scaling_tests/kernel/iterated.rs");
}
