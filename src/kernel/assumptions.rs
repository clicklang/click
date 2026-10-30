use super::execution_facts::ContextFactKey;
use super::prelude::*;
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::{CompareRelation, OverflowOperation};

#[cfg(test)]
thread_local! {
    /// Facts whose whole execution-variable ceiling was taken.
    static WHOLE_CEILING_FACTS: Cell<usize> = const { Cell::new(0) };
    static CONDITION_IMPLICATION_ANTECEDENT_CHECKS: Cell<usize> = const { Cell::new(0) };
    static MEMORY_SEPARATION_CANDIDATE_CHECKS: Cell<usize> = const { Cell::new(0) };
    static MEMORY_SEPARATION_RECURSIVE_CANDIDATE_CHECKS: Cell<usize> = const { Cell::new(0) };
    static BITVECTOR_EQUALITY_INDEX_FACT_VISITS: Cell<usize> = const { Cell::new(0) };
    static EXACT_CONSTANT_FACT_VISITS: Cell<usize> = const { Cell::new(0) };
    static CONDITION_FACT_VISITS: Cell<usize> = const { Cell::new(0) };
}

/// Counts one condition fact examined by a condition-fact query
/// (`has_condition_fact`, `exact_ordering_modulo_canonical_atoms`, the
/// symbolic pointer-equality hop), for the scaling regressions.
#[inline]
pub(in crate::kernel) fn count_condition_fact_visit() {
    #[cfg(test)]
    CONDITION_FACT_VISITS.with(|visits| visits.set(visits.get() + 1));
}
use std::cell::{Cell, RefCell};

pub(in crate::kernel) mod checked_order_bounds;
pub(in crate::kernel) mod checked_scalar_facts;
mod condition_reasoning;
pub(super) mod contradictions;
pub(in crate::kernel) mod variable_chains;
use super::equality_graph::EqualityGraph;
use super::machine_integer::comparison::{
    native_comparison_of_integer_observation, native_comparison_through_integer_operations,
};
use super::machine_integer::definedness::{
    definedness_of_integer_bound, integer_bounds_of_definedness,
};
use super::machine_integer::modular::wrapped_equality_of_integer_equality;
pub(in crate::kernel) use condition_reasoning::cancel_common_offset_addends;
pub(in crate::kernel) use condition_reasoning::held_order_at;
pub(in crate::kernel) use condition_reasoning::narrowed_cast_identity;

#[cfg(test)]
#[derive(Clone, Debug)]
pub(super) struct PointerValueUndo {
    source: std::sync::Arc<ConditionTerm>,
    conditions: crate::kernel::fact_collections::FactMap<ConditionTerm, bool>,
    propositions: crate::kernel::fact_collections::FactSet<Proposition>,
    graph: std::sync::Arc<EqualityGraph>,
}

mod separation_classes;
pub(in crate::kernel) use separation_classes::SeparatedAddressIndex;

mod memory_reasoning;
pub(in crate::kernel) use memory_reasoning::additive_base_spellings;
pub(crate) use memory_reasoning::arm_frame_composite_definitions;
pub(in crate::kernel) use memory_reasoning::parameter_alias_bucket;
pub(in crate::kernel) use memory_reasoning::parameter_partition_root;
pub(in crate::kernel) use memory_reasoning::parameter_partition_variable;
pub(in crate::kernel) use memory_reasoning::read_candidate_byte_width;
pub(in crate::kernel) use memory_reasoning::signed_byte_sum_is_nonwrapping;
pub(in crate::kernel) use memory_reasoning::{
    frame_composite_definitions, owned_instances_naming_access_base,
};
pub(crate) mod proposition_reasoning;

pub(crate) use proposition_reasoning::finite_forall_goal_instances;

/// How a structural walk compares two load atoms. The walk itself is exact —
/// it only ever descends through matching constructors — so the whole
/// relation is only as strong as the load-atom rule plugged in here.
pub(in crate::kernel) type LoadAtomsMatch<'a> =
    &'a dyn Fn(&Bitvector32Term, &Bitvector32Term) -> bool;

pub(in crate::kernel) fn pointers_equal_with_load_atoms(
    left: &Pointer,
    right: &Pointer,
    loads_match: LoadAtomsMatch<'_>,
) -> bool {
    (left.block == right.block
        || match (&left.block, &right.block) {
            (PointerBlock::LoadedPointer(_), PointerBlock::LoadedPointer(_)) => {
                let (Some(a), Some(b)) = (left.as_loaded_value(), right.as_loaded_value()) else {
                    return false;
                };
                loads_match(
                    &Bitvector32Term::MemoryLoad(
                        a.defining_memory,
                        Box::new(a.defining_address),
                        LoadKind::Bits64,
                    ),
                    &Bitvector32Term::MemoryLoad(
                        b.defining_memory,
                        Box::new(b.defining_address),
                        LoadKind::Bits64,
                    ),
                )
            }
            (PointerBlock::Symbolic(_), PointerBlock::Symbolic(_)) => {
                let base = |pointer: &Pointer| Pointer {
                    block: pointer.block.clone(),
                    offset: PointerOffsetTerm::Constant(0),
                };
                let (Some(first), Some(second)) = (
                    super::equality_graph::logical_pointer_read_term(&base(left)),
                    super::equality_graph::logical_pointer_read_term(&base(right)),
                ) else {
                    return false;
                };
                terms_equal_with_load_atoms(&first, &second, loads_match)
            }
            _ => false,
        })
        && offsets_equal_with_load_atoms(&left.offset, &right.offset, loads_match)
}

fn offsets_equal_with_load_atoms(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    loads_match: LoadAtomsMatch<'_>,
) -> bool {
    match (left, right) {
        (PointerOffsetTerm::Add(ll, lr), PointerOffsetTerm::Add(rl, rr)) => {
            offsets_equal_with_load_atoms(ll, rl, loads_match)
                && offsets_equal_with_load_atoms(lr, rr, loads_match)
        }
        (
            PointerOffsetTerm::Int32Scaled {
                value: left_value,
                byte_width: left_width,
            },
            PointerOffsetTerm::Int32Scaled {
                value: right_value,
                byte_width: right_width,
            },
        ) => {
            left_width == right_width
                && terms_equal_with_load_atoms(left_value, right_value, loads_match)
        }
        _ => left == right,
    }
}

fn terms_equal_with_load_atoms(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    loads_match: LoadAtomsMatch<'_>,
) -> bool {
    // Original object classes guide decoding, not numeric address equality.
    // Compare the addresses through the same pointer/load-atom rule.
    if let (Some(left), Some(right)) = (left.address_pointer(), right.address_pointer()) {
        return pointers_equal_with_load_atoms(left, right, loads_match);
    }
    match (left, right) {
        (Bitvector32Term::MemoryLoad(_, _, _), Bitvector32Term::MemoryLoad(_, _, _)) => {
            loads_match(left, right)
        }
        // A registered load variable is a load atom too: the same cell named
        // at two snapshots has two variables when the edge between them is
        // crossed only in context. Compare through the first-seen origin
        // snapshots, which are DAG-connected; the canonical placeholder form
        // is unsuited to frame checks.
        (Bitvector32Term::Variable(a), Bitvector32Term::Variable(b))
            if a != b
                && crate::kernel::is_load_variable(a)
                && crate::kernel::is_load_variable(b) =>
        {
            match (
                crate::kernel::registered_load_origin_term_for_variable(a),
                crate::kernel::registered_load_origin_term_for_variable(b),
            ) {
                (Some(left), Some(right)) => loads_match(&left, &right),
                _ => false,
            }
        }
        (
            Bitvector32Term::If {
                condition: left_condition,
                then_term: left_then,
                else_term: left_else,
            },
            Bitvector32Term::If {
                condition: right_condition,
                then_term: right_then,
                else_term: right_else,
            },
        ) => {
            conditions_equal_with_load_atoms(left_condition, right_condition, loads_match)
                && terms_equal_with_load_atoms(left_then, right_then, loads_match)
                && terms_equal_with_load_atoms(left_else, right_else, loads_match)
        }
        _ => {
            if let (Some((left_operator, ll, lr)), Some((right_operator, rl, rr))) =
                (left.as_binary(), right.as_binary())
            {
                left_operator == right_operator
                    && terms_equal_with_load_atoms(ll, rl, loads_match)
                    && terms_equal_with_load_atoms(lr, rr, loads_match)
            } else if let (Some((left_operator, left_value)), Some((right_operator, right_value))) =
                (left.as_unary(), right.as_unary())
            {
                left_operator == right_operator
                    && terms_equal_with_load_atoms(left_value, right_value, loads_match)
            } else {
                left == right
            }
        }
    }
}

/// Exact structural condition equality with load atoms compared by
/// `loads_match`. Only matching constructors recurse and everything else
/// falls back to `==`, so two structurally different conditions never match
/// however permissive `loads_match` is.
pub(in crate::kernel) fn conditions_equal_with_load_atoms(
    left: &ConditionTerm,
    right: &ConditionTerm,
    loads_match: LoadAtomsMatch<'_>,
) -> bool {
    if left == right {
        return true;
    }
    let terms = |ll, rl, lr, rr| {
        terms_equal_with_load_atoms(ll, rl, loads_match)
            && terms_equal_with_load_atoms(lr, rr, loads_match)
    };
    if let (Some((left_operator, ll, lr)), Some((right_operator, rl, rr))) = (
        left.as_bitvector_comparison(),
        right.as_bitvector_comparison(),
    ) {
        return left_operator == right_operator && terms(ll, rl, lr, rr);
    }
    match (left, right) {
        (ConditionTerm::PointerOffsetEqual(ll, lr), ConditionTerm::PointerOffsetEqual(rl, rr)) => {
            offsets_equal_with_load_atoms(ll, rl, loads_match)
                && offsets_equal_with_load_atoms(lr, rr, loads_match)
        }
        (ConditionTerm::PointerEqual(ll, lr), ConditionTerm::PointerEqual(rl, rr)) => {
            pointers_equal_with_load_atoms(ll, rl, loads_match)
                && pointers_equal_with_load_atoms(lr, rr, loads_match)
        }
        (ConditionTerm::AlgebraicEqual(ll, lr), ConditionTerm::AlgebraicEqual(rl, rr)) => {
            algebraic_terms_equal_with_load_atoms(ll, rl, loads_match)
                && algebraic_terms_equal_with_load_atoms(lr, rr, loads_match)
        }
        _ => false,
    }
}

/// Exact structural algebraic equality with each load of an abstract value
/// compared by `loads_match` on its scalar carrier: the value an address
/// holds is the same in two snapshots when its bytes are.
fn algebraic_terms_equal_with_load_atoms(
    left: &AlgebraicTerm,
    right: &AlgebraicTerm,
    loads_match: LoadAtomsMatch<'_>,
) -> bool {
    if left == right {
        return true;
    }
    if left.algebraic_type != right.algebraic_type {
        return false;
    }
    let values = |left: &AlgebraicValue, right: &AlgebraicValue| match (left, right) {
        (
            AlgebraicValue::C(CValue::Parameter(left)),
            AlgebraicValue::C(CValue::Parameter(right)),
        ) => algebraic_terms_equal_with_load_atoms(left, right, loads_match),
        (AlgebraicValue::Algebraic(left), AlgebraicValue::Algebraic(right)) => {
            algebraic_terms_equal_with_load_atoms(left, right, loads_match)
        }
        _ => left == right,
    };
    match (&left.node, &right.node) {
        (
            AlgebraicTermNode::MemoryLoad {
                memory: left_memory,
                pointer: left_pointer,
            },
            AlgebraicTermNode::MemoryLoad {
                memory: right_memory,
                pointer: right_pointer,
            },
        ) => loads_match(
            &AlgebraicTermNode::memory_load_carrier(left_memory, left_pointer),
            &AlgebraicTermNode::memory_load_carrier(right_memory, right_pointer),
        ),
        (
            AlgebraicTermNode::Constructor {
                variant: left_variant,
                fields: left_fields,
            },
            AlgebraicTermNode::Constructor {
                variant: right_variant,
                fields: right_fields,
            },
        ) => {
            left_variant == right_variant
                && left_fields.len() == right_fields.len()
                && left_fields
                    .iter()
                    .zip(right_fields)
                    .all(|(left, right)| values(left, right))
        }
        _ => false,
    }
}

/// Compares two load atoms by their pointers alone, ignoring which memory
/// snapshot each carries.
///
/// NOT sound as an equality on its own: two loads of one pointer in
/// different snapshots hold different values whenever a write between the
/// snapshots reached that pointer. It exists only as a cheap prefilter that
/// discards hopeless candidates before a proving comparison runs, and every
/// caller must decide the surviving pairs with a real check.
fn load_atoms_equal_ignoring_memories(left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
    match (left, right) {
        (
            Bitvector32Term::MemoryLoad(_, left_pointer, left_kind),
            Bitvector32Term::MemoryLoad(_, right_pointer, right_kind),
        ) => {
            left_kind == right_kind && pointers_equal_ignoring_memories(left_pointer, right_pointer)
        }
        _ => left == right,
    }
}

/// Structural pointer equality that treats two loads of one location as
/// equal regardless of which memory snapshot each form carries. Cheap:
/// no proving, no canonicalization.
pub(crate) fn pointers_equal_ignoring_memories(left: &Pointer, right: &Pointer) -> bool {
    pointers_equal_with_load_atoms(left, right, &load_atoms_equal_ignoring_memories)
}

/// Cheap, assumption-free necessary condition for
/// [`PureFactContext::conditions_equal_modulo_proven_snapshots`]: same structure,
/// with load atoms compared by pointer only.
///
/// Snapshot-blind, so it is NOT an equivalence and must never decide fact
/// availability on its own — it only narrows the candidate set before the
/// proving comparison runs.
pub fn conditions_equal_ignoring_memories(left: &ConditionTerm, right: &ConditionTerm) -> bool {
    if let (ConditionTerm::PointerValueEqual(a, b), ConditionTerm::PointerValueEqual(c, d)) =
        (left, right)
    {
        // Candidate selection only. The context's snapshot bridge separately
        // compares both complete designations before accepting this candidate.
        return a.c_type() == c.c_type()
            && b.c_type() == d.c_type()
            && pointers_equal_with_load_atoms(
                a.pointer(),
                c.pointer(),
                &load_atoms_equal_ignoring_memories,
            )
            && pointers_equal_with_load_atoms(
                b.pointer(),
                d.pointer(),
                &load_atoms_equal_ignoring_memories,
            );
    }
    conditions_equal_with_load_atoms(left, right, &load_atoms_equal_ignoring_memories)
}

/// The address of a memory range's first element, when the range provably
/// has one.
///
/// This anchor is what makes a separation say something about two pointers:
/// each range holds the element at its own anchor, so two separated ranges
/// cannot have the same anchor. A range that may be empty holds nothing and
/// states nothing about its anchor, so both endpoints must be constants that
/// settle that here, with no reasoning and no wrap-around question.
///
/// The anchor is computed the way any element address is, which also
/// normalizes a range that a composition re-expressed against another
/// object's base back to the address the pointer itself carries.
/// The kind and canonical sides a condition fact is filed under in
/// `condition_facts_by_sides`, or `None` for a kind
/// `PureFactContext::condition_matches` relates only to itself.
pub(in crate::kernel) fn condition_match_key(
    condition: &ConditionTerm,
) -> Option<crate::kernel::primitives::ConditionMatchKey> {
    use crate::kernel::primitives::ConditionMatchKey;
    let canonical = crate::kernel::eval::canonical_term;
    let ordered = |left: Bitvector32Term, right: Bitvector32Term| {
        if left <= right {
            (left, right)
        } else {
            (right, left)
        }
    };
    Some(match condition {
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        } => {
            let (left, right) = ordered(canonical(left), canonical(right));
            ConditionMatchKey::Equal(left, right)
        }
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Add,
            left,
            right,
        } => {
            let (left, right) = ordered(canonical(left), canonical(right));
            ConditionMatchKey::OverflowAdd(left, right)
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            let left = crate::kernel::eval::canonical_offset_term(left);
            let right = crate::kernel::eval::canonical_offset_term(right);
            if left <= right {
                ConditionMatchKey::OffsetEqual(left, right)
            } else {
                ConditionMatchKey::OffsetEqual(right, left)
            }
        }
        ConditionTerm::Compare {
            format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
            relation: CompareRelation::LessThan,
            left: lower,
            right: upper,
        }
        | ConditionTerm::Compare {
            format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
            relation: CompareRelation::GreaterThan,
            left: upper,
            right: lower,
        } => {
            if *format == MachineIntegerType::UInt32 {
                ConditionMatchKey::UnsignedOrder(true, canonical(lower), canonical(upper))
            } else {
                ConditionMatchKey::Order(true, canonical(lower), canonical(upper))
            }
        }
        ConditionTerm::Compare {
            format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
            relation: CompareRelation::LessEqual,
            left: lower,
            right: upper,
        }
        | ConditionTerm::Compare {
            format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
            relation: CompareRelation::GreaterEqual,
            left: upper,
            right: lower,
        } => {
            if *format == MachineIntegerType::UInt32 {
                ConditionMatchKey::UnsignedOrder(false, canonical(lower), canonical(upper))
            } else {
                ConditionMatchKey::Order(false, canonical(lower), canonical(upper))
            }
        }
        _ => return None,
    })
}

/// The key a `CResourceContains` fact is filed under: a memory range's base
/// block, or any other resource itself. `resource_contains_builtin` relates a
/// memory parent only to ranges over related addresses, and any other parent
/// only to itself.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(in crate::kernel) enum ResourceContainsKey {
    Block(PointerBlock),
    Resource(CResource),
}

impl ResourceContainsKey {
    fn of(resource: &CResource) -> Self {
        match resource {
            CResource::Memory(range) => Self::Block(range.base().block.clone()),
            other => Self::Resource(other.clone()),
        }
    }
}

/// Whether a side of this condition is not an atom: see
/// `PureFactContext::open_condition_facts`.
fn condition_has_an_open_side(condition: &ConditionTerm) -> bool {
    let open = |term: &Bitvector32Term| match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::UInt32Constant(_) => false,
        Bitvector32Term::Variable(variable) => {
            crate::kernel::eval::registered_load_for_variable(variable).is_some()
        }
        _ => true,
    };
    let open_offset = |offset: &PointerOffsetTerm| match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => false,
        PointerOffsetTerm::Int32Scaled { value, .. } => open(value),
        _ => true,
    };
    match condition {
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            left,
            right,
            ..
        }
        | ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Add,
            left,
            right,
        } => open(left) || open(right),
        ConditionTerm::PointerOffsetEqual(left, right) => open_offset(left) || open_offset(right),
        _ => false,
    }
}

pub(in crate::kernel) fn memory_range_anchor(range: &CMemoryRange) -> Option<PointerOffsetTerm> {
    let (Some(start), Some(end)) = (range.constant_start(), range.constant_end()) else {
        return None;
    };
    (range.element_width() > 0 && (start as i32) < (end as i32))
        .then(|| range.start_pointer().offset)
}

pub(super) fn resources_equal_ignoring_memories(left: &CResource, right: &CResource) -> bool {
    let values_match = |left: &CValue, right: &CValue| match (left, right) {
        (CValue::Int32(left), CValue::Int32(right))
        | (CValue::UInt8(left), CValue::UInt8(right)) => {
            terms_equal_with_load_atoms(left, right, &load_atoms_equal_ignoring_memories)
        }
        (CValue::Int8(left), CValue::Int8(right)) => {
            terms_equal_with_load_atoms(left, right, &load_atoms_equal_ignoring_memories)
        }
        (CValue::Int16(left), CValue::Int16(right))
        | (CValue::UInt16(left), CValue::UInt16(right)) => {
            terms_equal_with_load_atoms(left, right, &load_atoms_equal_ignoring_memories)
        }
        (CValue::Pointer(left), CValue::Pointer(right)) => {
            pointers_equal_ignoring_memories(left.pointer(), right.pointer())
        }
        _ => false,
    };
    match (left, right) {
        (CResource::Memory(left), CResource::Memory(right)) => {
            // The bounds are compared as terms, so ranges of one kind are
            // read alike; a wide range and an `Int32` one are not equal.
            let (left_start, left_end) = left.bound_terms();
            let (right_start, right_end) = right.bound_terms();
            left.element_width() == right.element_width()
                && left.wide_bounds().is_some() == right.wide_bounds().is_some()
                && terms_equal_with_load_atoms(
                    left_start,
                    right_start,
                    &load_atoms_equal_ignoring_memories,
                )
                && terms_equal_with_load_atoms(
                    left_end,
                    right_end,
                    &load_atoms_equal_ignoring_memories,
                )
                && pointers_equal_ignoring_memories(left.base(), right.base())
        }
        (
            CResource::Composite {
                name: left_name,
                arguments: left_arguments,
            },
            CResource::Composite {
                name: right_name,
                arguments: right_arguments,
            },
        )
        | (
            CResource::Token {
                name: left_name,
                arguments: left_arguments,
            },
            CResource::Token {
                name: right_name,
                arguments: right_arguments,
            },
        ) => {
            left_name == right_name
                && left_arguments.len() == right_arguments.len()
                && left_arguments
                    .iter()
                    .zip(right_arguments.iter())
                    .all(|(left, right)| match (left, right) {
                        (AlgebraicValue::C(left), AlgebraicValue::C(right)) => {
                            values_match(left, right)
                        }
                        _ => left == right,
                    })
        }
        _ => false,
    }
}

/// The equality-graph vertex key for a term is its canonical form, so a raw
/// load term and the load variable for it share one vertex: the graph
/// joins equal terms by construction rather than by per-query bridging.
/// The memory snapshot and cell a load term reads, for a raw load or a
/// registered load variable.
pub(in crate::kernel) fn load_snapshot_and_pointer(
    term: &Bitvector32Term,
) -> Option<(CMemory, Pointer, LoadKind)> {
    match term {
        Bitvector32Term::MemoryLoad(memory, pointer, kind) => {
            Some(((**memory).clone(), pointer.as_ref().clone(), *kind))
        }
        // A load variable's canonical registration carries a placeholder
        // snapshot; its origin registration is the live snapshot it was
        // first minted from, which frame evidence can relate to later
        // snapshots.
        Bitvector32Term::Variable(variable) if crate::kernel::is_load_variable(variable) => {
            let kind = crate::kernel::registered_load_kind_for_variable(variable)?;
            crate::kernel::eval::registered_load_origin_for_variable(variable)
                .or_else(|| crate::kernel::registered_load_for_variable(variable))
                .map(|(memory, pointer)| ((*memory).clone(), pointer, kind))
        }
        _ => None,
    }
}

pub(in crate::kernel) fn equality_graph_term_key(term: &Bitvector32Term) -> Bitvector32Term {
    crate::kernel::eval::canonical_term(term)
}

thread_local! {
    static SOLVE_FACT_CONDITIONS_IN_PROGRESS: RefCell<BTreeSet<(ConditionTerm, bool)>> =
        const { RefCell::new(BTreeSet::new()) };
    static CONDITION_DECISIONS_IN_PROGRESS: RefCell<BTreeSet<ConditionTerm>> =
        const { RefCell::new(BTreeSet::new()) };
    static REASONING_PROVENANCE_STACK: RefCell<Vec<ReasoningProvenanceFrame>> =
        const { RefCell::new(Vec::new()) };
    static RECORDING_REASONING_PROVENANCE: Cell<bool> = const { Cell::new(false) };
    static CAPTURING_IMPLICIT_REASONING_PROVENANCE: Cell<usize> = const { Cell::new(0) };
}

#[derive(Default)]
struct ReasoningProvenanceFrame {
    premises: BTreeSet<Proposition>,
    queries: BTreeSet<Proposition>,
}

struct ReasoningProvenanceCollectionGuard {
    active: bool,
}

impl ReasoningProvenanceCollectionGuard {
    fn start() -> Self {
        REASONING_PROVENANCE_STACK.with(|stack| {
            stack.borrow_mut().push(ReasoningProvenanceFrame::default());
        });
        Self { active: true }
    }

    fn finish(mut self) -> BTreeSet<Proposition> {
        let frame = REASONING_PROVENANCE_STACK.with(|stack| {
            stack
                .borrow_mut()
                .pop()
                .expect("reasoning provenance collection stack")
        });
        self.active = false;
        frame.premises
    }
}

impl Drop for ReasoningProvenanceCollectionGuard {
    fn drop(&mut self) {
        if self.active {
            REASONING_PROVENANCE_STACK.with(|stack| {
                stack.borrow_mut().pop();
            });
        }
    }
}

struct ReasoningProvenanceRecordingGuard;

impl ReasoningProvenanceRecordingGuard {
    fn start() -> Self {
        RECORDING_REASONING_PROVENANCE.with(|recording| recording.set(true));
        Self
    }
}

impl Drop for ReasoningProvenanceRecordingGuard {
    fn drop(&mut self) {
        RECORDING_REASONING_PROVENANCE.with(|recording| recording.set(false));
    }
}

/// Collects the exact premises consumed by successful reasoning
/// during `body`. This is certificate-planning metadata only: it does not
/// enter execution paths, theorems, obligations, or fresh-name budgets.
pub(crate) fn collect_reasoning_provenance<T>(body: impl FnOnce() -> T) -> (T, Vec<Proposition>) {
    let guard = ReasoningProvenanceCollectionGuard::start();
    let result = body();
    let premises = guard.finish();
    (result, premises.into_iter().collect())
}

pub(crate) fn record_reasoning_provenance(
    assumptions: &PureFactContext,
    proposition: &Proposition,
) {
    if RECORDING_REASONING_PROVENANCE.with(Cell::get) {
        return;
    }
    let should_derive = REASONING_PROVENANCE_STACK.with(|stack| {
        let mut stack = stack.borrow_mut();
        let Some(active) = stack.last_mut() else {
            return false;
        };
        active.queries.insert(proposition.clone())
    });
    if !should_derive {
        return;
    }
    let _recording = ReasoningProvenanceRecordingGuard::start();
    // Exact facts already identify their own certificate premise. The
    // general derivation builder used to fill in the rest, but it left the
    // kernel with the rest of the proposition search, and asking it for a
    // premise set would have conservatively attached its complete ambient
    // context anyway. A proposition the exact index does not name
    // contributes no premise here; certificate planning that needs one
    // spells the step instead.
    let premises = if assumptions.proves_exact(proposition) {
        vec![proposition.clone()]
    } else {
        Vec::new()
    };
    REASONING_PROVENANCE_STACK.with(|stack| {
        let mut stack = stack.borrow_mut();
        let Some(active) = stack.last_mut() else {
            return;
        };
        active.premises.extend(premises);
    });
}

pub(crate) fn capture_implicit_reasoning_provenance<T>(body: impl FnOnce() -> T) -> T {
    struct Guard;
    impl Drop for Guard {
        fn drop(&mut self) {
            CAPTURING_IMPLICIT_REASONING_PROVENANCE.with(|depth| depth.set(depth.get() - 1));
        }
    }

    CAPTURING_IMPLICIT_REASONING_PROVENANCE.with(|depth| depth.set(depth.get() + 1));
    let _guard = Guard;
    body()
}

pub(crate) fn record_implicit_reasoning_provenance(
    assumptions: &PureFactContext,
    proposition: &Proposition,
) {
    if CAPTURING_IMPLICIT_REASONING_PROVENANCE.with(|depth| depth.get() != 0) {
        record_reasoning_provenance(assumptions, proposition);
    }
}

/// Whether implicit reasoning provenance is being captured on this thread:
/// a rule that would skip a question whose answer records provenance must
/// ask it while this holds.
pub(crate) fn implicit_reasoning_provenance_capturing() -> bool {
    CAPTURING_IMPLICIT_REASONING_PROVENANCE.with(|depth| depth.get() != 0)
}

/// True while any condition decision is in progress on this thread. Deep
/// reasoning helpers use this to avoid re-entering `decide` from inside a
/// decision, which would cycle through order-fact matching and memory-load
/// resolution.
pub(super) fn inside_condition_decision() -> bool {
    CONDITION_DECISIONS_IN_PROGRESS.with(|in_progress| !in_progress.borrow().is_empty())
}

type StatedIndexMap = crate::persistent::PersistentMap<
    crate::kernel::proof::PropositionIdentityKey,
    crate::persistent::PersistentSet<Proposition>,
>;

fn adjust_stated_index(
    index: &StatedIndexMap,
    key: crate::kernel::proof::PropositionIdentityKey,
    proposition: &Proposition,
    insert: bool,
) -> StatedIndexMap {
    let bucket = index.get(&key).cloned().unwrap_or_default();
    let bucket = if insert {
        bucket.with_value(proposition.clone())
    } else {
        bucket.without_value(proposition)
    };
    if bucket.is_empty() {
        index.without_key(&key)
    } else {
        index.with_inserted(key, bucket)
    }
}

/// A context's index of stated propositions by alpha/load identity key.
///
/// A context starts `Deferred`: each fact change appends one node to a
/// persistent chain without computing a key. A query builds every unbuilt
/// node from the nearest built ancestor down and records each node's index
/// on it, so a sibling sharing the chain later builds only its own suffix:
/// every fact change is keyed at most once however many contexts derive from
/// it, and never when no context asks. Contexts rebuilt from scratch
/// (`retain`/`clear`) are `Built` and maintained eagerly, as before.
#[derive(Clone)]
pub(crate) enum StatedPropositionIndex {
    Built(StatedIndexMap),
    Deferred(std::sync::Arc<DeferredStatedIndexNode>),
}

impl Default for StatedPropositionIndex {
    fn default() -> Self {
        Self::deferred_empty()
    }
}

impl std::fmt::Debug for StatedPropositionIndex {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Built(index) => formatter.debug_tuple("Built").field(&index.len()).finish(),
            Self::Deferred(_) => formatter.write_str("Deferred"),
        }
    }
}

impl StatedPropositionIndex {
    fn deferred_empty() -> Self {
        Self::Deferred(std::sync::Arc::new(DeferredStatedIndexNode {
            parent: std::sync::Mutex::new(None),
            adjustment: None,
            built: std::sync::OnceLock::from(StatedIndexMap::default()),
        }))
    }

    #[cfg(test)]
    fn shares_storage_with(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Built(left), Self::Built(right)) => left.shares_root_with(right),
            (Self::Deferred(left), Self::Deferred(right)) => std::sync::Arc::ptr_eq(left, right),
            _ => false,
        }
    }
}

pub(crate) struct DeferredStatedIndexNode {
    /// The index this node's adjustment applies to, released once this node
    /// is built. The root has none and is built empty.
    parent: std::sync::Mutex<Option<std::sync::Arc<DeferredStatedIndexNode>>>,
    adjustment: Option<(Proposition, bool)>,
    built: std::sync::OnceLock<StatedIndexMap>,
}

impl DeferredStatedIndexNode {
    fn parent(&self) -> Option<std::sync::Arc<DeferredStatedIndexNode>> {
        self.parent
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone()
    }

    /// Builds this node's index, and every unbuilt ancestor's, iteratively.
    /// `None` when a key walk stops at an exhausted budget: nothing partial is
    /// recorded, since an entry a later removal could not retract would make
    /// a removed fact look stated.
    fn force(self: &std::sync::Arc<Self>) -> Option<&StatedIndexMap> {
        if let Some(index) = self.built.get() {
            return Some(index);
        }
        let mut unbuilt = vec![self.clone()];
        let mut index = loop {
            let parent = unbuilt
                .last()
                .and_then(|node| node.parent())
                .expect("an unbuilt node keeps its parent");
            match parent.built.get() {
                Some(index) => break index.clone(),
                None => unbuilt.push(parent),
            }
        };
        for node in unbuilt.iter().rev() {
            if let Some((proposition, insert)) = &node.adjustment {
                match crate::kernel::proof::proposition_identity_key(proposition) {
                    Some(key) => {
                        index = adjust_stated_index(&index, key, proposition, *insert);
                    }
                    None if crate::instrumentation::deadline_exceeded_with_work(0) => {
                        return None;
                    }
                    None => {}
                }
            }
            let _ = node.built.set(index.clone());
            // Built nodes answer from their own index; the history above them
            // is no longer needed by anything that holds this node.
            node.parent
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .take();
        }
        self.built.get()
    }
}

impl Drop for DeferredStatedIndexNode {
    /// Unlinks the chain iteratively, so dropping a context built from a
    /// long fact list cannot overflow the stack.
    fn drop(&mut self) {
        let mut parent = self
            .parent
            .get_mut()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .take();
        while let Some(node) = parent {
            match std::sync::Arc::try_unwrap(node) {
                Ok(mut node) => {
                    parent = node
                        .parent
                        .get_mut()
                        .unwrap_or_else(std::sync::PoisonError::into_inner)
                        .take();
                }
                Err(_) => break,
            }
        }
    }
}

thread_local! {
    static INCOMPLETE_REASONING_EPOCH: Cell<u64> = const { Cell::new(0) };
    static DECIDE_MEMO: RefCell<std::collections::HashMap<(u64, ConditionTerm), Option<bool>>> =
        RefCell::new(std::collections::HashMap::new());
    static ASSUMPTIONS_MEMO_IDS: RefCell<std::collections::HashMap<PureFactContext, u64>> =
        RefCell::new(std::collections::HashMap::new());
    static NEXT_ASSUMPTIONS_MEMO_ID: Cell<u64> = const { Cell::new(0) };
    static LOGICAL_READ_MEMO_IDS: RefCell<std::collections::HashMap<(u64, u64), u64>> =
        RefCell::new(std::collections::HashMap::new());
    static TRANSPORT_EQUAL_MEMO: RefCell<
        std::collections::HashMap<(u64, Bitvector32Term, Bitvector32Term), bool>,
    > = RefCell::new(std::collections::HashMap::new());
    static CONSTANT_NORMALIZATION_MEMO: RefCell<
        std::collections::HashMap<(u64, Bitvector32Term), Option<i64>>,
    > = RefCell::new(std::collections::HashMap::new());
    static SIGNED_INTERVAL_MEMO: RefCell<
        std::collections::HashMap<(u64, Bitvector32Term), (i64, i64)>,
    > = RefCell::new(std::collections::HashMap::new());
    /// Keyed by `atomic_derivation_memo_key`: the premises, whether the
    /// query is for `solve`, and the DAG modes the derivation reads.
    static ATOMIC_DERIVATION_MEMO: RefCell<
        std::collections::HashMap<
            (u64, bool, bool, bool),
            std::collections::HashMap<Proposition, Option<AtomicPropositionDerivationEvidence>>,
        >,
    > = RefCell::new(std::collections::HashMap::new());
}

/// Empties this module's memo tables at a verification boundary (ids keep
/// counting, so a later entry cannot alias an old id).
pub(crate) fn clear_assumption_memos() {
    DECIDE_MEMO.with(|memo| memo.borrow_mut().clear());
    ASSUMPTIONS_MEMO_IDS.with(|ids| ids.borrow_mut().clear());
    LOGICAL_READ_MEMO_IDS.with(|ids| ids.borrow_mut().clear());
    TRANSPORT_EQUAL_MEMO.with(|memo| memo.borrow_mut().clear());
    CONSTANT_NORMALIZATION_MEMO.with(|memo| memo.borrow_mut().clear());
    SIGNED_INTERVAL_MEMO.with(|memo| memo.borrow_mut().clear());
    ATOMIC_DERIVATION_MEMO.with(|memo| memo.borrow_mut().clear());
}

// The memo tables are bounded so a long verification cannot grow them without
// limit. Ids are drawn from a never-reset counter, so clearing the intern
// table cannot alias an old id to different contents.
const ASSUMPTIONS_MEMO_ID_LIMIT: usize = 20_000;
const DECIDE_MEMO_LIMIT: usize = 500_000;
const SIGNED_INTERVAL_MEMO_LIMIT: usize = 100_000;

/// Content-derived memo identity: equal fact sets share an id, and any
/// in-place mutation changes the contents and therefore the id, so a decision
/// memoized under an id can never be checked against different facts.
fn assumptions_memo_id(assumptions: &PureFactContext) -> u64 {
    ASSUMPTIONS_MEMO_IDS.with(|ids| {
        let mut ids = ids.borrow_mut();
        if let Some(id) = ids.get(assumptions) {
            return *id;
        }
        if ids.len() >= ASSUMPTIONS_MEMO_ID_LIMIT {
            ids.clear();
        }
        let id = NEXT_ASSUMPTIONS_MEMO_ID.with(|next| {
            let id = next.get();
            next.set(id + 1);
            id
        });
        // This table owns identity keys, never contexts used for planning.
        // Do not keep dependency indexes from every transient restricted
        // context alive until the next verification boundary. They are
        // excluded from PureFactContext equality and hashing.
        let mut key = assumptions.clone();
        key.equality_graph = assumptions.equality_graph.identity_only();
        key.atomic_connection_facts = crate::persistent::PersistentMap::default();
        key.atomic_ground_facts = crate::kernel::fact_collections::ScanSet::default();
        key.atomic_quantified_facts = crate::kernel::fact_collections::ScanSet::default();
        key.universals_by_conclusion = crate::persistent::PersistentMap::default();
        key.condition_facts_by_variable = crate::persistent::PersistentMap::default();
        key.snapshot_condition_variable_base = crate::persistent::PersistentMap::default();
        key.snapshot_condition_variable_changes = crate::persistent::PersistentMap::default();
        key.snapshot_condition_variables = std::sync::Arc::new(std::sync::OnceLock::new());
        key.memory_load_condition_facts = crate::persistent::PersistentMap::default();
        // Lazy query caches may be populated *after* this clone is interned.
        // The identity table must not own their shared OnceLocks either.
        key.memory_loadable_shape_facts = crate::persistent::PersistentMap::default();
        ids.insert(key, id);
        id
    })
}

#[cfg(test)]
mod planning_index_memo_lifetime_tests {
    use super::*;

    #[test]
    fn memo_identity_does_not_retain_transient_indexes() {
        clear_assumption_memos();
        for size in [8u64, 16, 32, 64] {
            let mut context = PureFactContext::new();
            for index in 0..size {
                context = context.assume_proposition(Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(Bitvector32Term::Variable(Variable(size * 1000 + index))),
                        right: Box::new(Bitvector32Term::Constant(7)),
                    },
                    true,
                ));
            }
            let cache = std::sync::Arc::downgrade(&context.snapshot_condition_variables);
            let id = assumptions_memo_id(&context);
            // The identity key exists before the live context populates a
            // shared cache; dropping only already-built data is insufficient.
            assert_eq!(assumptions_memo_id(&context), id);
            let copy = context.clone();
            assert_eq!(assumptions_memo_id(&copy), id);
            drop(copy);
            drop(context);
            assert!(
                cache.upgrade().is_none(),
                "size {size}: memo identity retained planning state"
            );
        }
        clear_assumption_memos();
    }
}

/// The content-derived memo id of a fact set, never salted by a search
/// attempt: the identity [`crate::kernel::reasoning::with_closure_failure_memo`]
/// keys its negative answers by, so one closure's candidates share them.
pub(crate) fn unsalted_assumptions_memo_id(assumptions: &PureFactContext) -> u64 {
    memo_id_with_logical_reads(assumptions_memo_id(assumptions), assumptions)
}

/// Term registration or a checked read equality can turn an earlier miss into
/// a hit without adding a proposition. Namespace reasoning memos by their
/// generation; never scan or flush the ambient fact set.
fn memo_id_with_logical_reads(base: u64, assumptions: &PureFactContext) -> u64 {
    let generation = assumptions.equality_graph.logical_read_generation();
    if generation == 0 {
        return base;
    }
    LOGICAL_READ_MEMO_IDS.with(|ids| {
        let mut ids = ids.borrow_mut();
        if let Some(id) = ids.get(&(base, generation)) {
            return *id;
        }
        if ids.len() >= ASSUMPTIONS_MEMO_ID_LIMIT {
            ids.clear();
        }
        let id = NEXT_ASSUMPTIONS_MEMO_ID.with(|next| {
            let id = next.get();
            next.set(id + 1);
            id
        });
        ids.insert((base, generation), id);
        id
    })
}

/// Memo identity for the DAG-walk memo tables in api.rs: the ambient scope's
/// id when one is live (no hashing), the content-derived id otherwise.
pub(super) fn dag_memo_assumptions_id(assumptions: &PureFactContext) -> u64 {
    ambient_assumptions_memo_id(assumptions)
        .unwrap_or_else(|| apply_attempt_salt(unsalted_assumptions_memo_id(assumptions)))
}

thread_local! {
    static ASSUMPTIONS_ID_SCOPES: RefCell<Vec<(usize, u64)>> = const { RefCell::new(Vec::new()) };
}

/// Resolves the memo id for a fact set that is borrowed for the duration of
/// the returned guard, skipping the content hash when an enclosing scope
/// already resolved the same object.
///
/// The address comparison is sound because every recorded scope belongs to a
/// live borrow further up the stack: while such a borrow is alive its object
/// cannot be dropped, so an equal address is the same object with the same
/// contents.
pub(crate) struct PureFactContextIdScope {
    id: u64,
    pushed: bool,
}

impl PureFactContextIdScope {
    pub(crate) fn enter(assumptions: &PureFactContext) -> Self {
        if let Some(id) = ambient_assumptions_memo_id(assumptions) {
            return Self { id, pushed: false };
        }
        let address = assumptions as *const PureFactContext as usize;
        let id = assumptions_memo_id(assumptions);
        ASSUMPTIONS_ID_SCOPES.with(|scopes| scopes.borrow_mut().push((address, id)));
        Self {
            id: apply_attempt_salt(memo_id_with_logical_reads(id, assumptions)),
            pushed: true,
        }
    }
}

/// The memo id for this fact set if an enclosing [`PureFactContextIdScope`]
/// already resolved this same object, with no content hashing. Interior
/// reasoning helpers use this so only designated entry points ever pay the
/// hash; outside any scope they simply run unmemoized, as before memoization
/// existed.
pub(super) fn ambient_assumptions_memo_id(assumptions: &PureFactContext) -> Option<u64> {
    let address = assumptions as *const PureFactContext as usize;
    ASSUMPTIONS_ID_SCOPES.with(|scopes| {
        scopes
            .borrow()
            .iter()
            .rev()
            .find(|(scope_address, _)| *scope_address == address)
            .map(|(_, id)| apply_attempt_salt(memo_id_with_logical_reads(*id, assumptions)))
    })
}

impl Drop for PureFactContextIdScope {
    fn drop(&mut self) {
        if self.pushed {
            ASSUMPTIONS_ID_SCOPES.with(|scopes| {
                scopes.borrow_mut().pop();
            });
        }
    }
}

thread_local! {
    static ATTEMPT_SALT_STACK: RefCell<Vec<u64>> = const { RefCell::new(Vec::new()) };
    static NEXT_ATTEMPT_SALT: Cell<u64> = const { Cell::new(1) };
}

/// Runs one candidate search attempt whose memo footprint must not outlive a
/// discarded result. Every reasoning memo keys by an assumptions memo id;
/// inside an attempt those ids are salted with a fresh per-attempt value, so
/// entries the attempt writes land in a namespace no later lookup consults.
/// A discarded attempt therefore cannot perturb a later search's
/// order-sensitive selection by transporting answers computed under its own
/// budget. The trade is that attempts run memo-cold (they see none of the
/// ambient warmth and leave none behind, kept or discarded); `keep` exists
/// so callers state intent, and a kept attempt's semantic products are its
/// returned certificates, never its cache side effects.
pub(crate) fn with_search_attempt_rollback<T>(body: impl FnOnce() -> (T, bool)) -> T {
    let salt = NEXT_ATTEMPT_SALT.with(|next| {
        let salt = next.get();
        next.set(salt + 1);
        salt
    });
    ATTEMPT_SALT_STACK.with(|stack| stack.borrow_mut().push(salt));
    let (value, _keep) = body();
    ATTEMPT_SALT_STACK.with(|stack| {
        stack
            .borrow_mut()
            .pop()
            .expect("attempt salt frames are push/pop balanced");
    });
    value
}

/// The active attempt's memo-id salt, mixed into every assumptions memo id
/// so attempt-scoped entries stay invisible outside the attempt. Zero when
/// no attempt is active, preserving all ids exactly as before.
fn attempt_memo_salt() -> u64 {
    ATTEMPT_SALT_STACK.with(|stack| stack.borrow().last().copied().unwrap_or(0))
}

fn apply_attempt_salt(id: u64) -> u64 {
    let salt = attempt_memo_salt();
    if salt == 0 {
        id
    } else {
        // Multiply-xor folds the salt into the id without colliding with
        // unsalted ids drawn from the small dense counter space.
        id ^ salt.wrapping_mul(0x9E37_79B9_7F4A_7C15)
    }
}

/// Records an exact-query cycle cut or an observed verification limit.
/// Enclosing memo layers compare epochs to avoid retaining negative answers
/// produced by incomplete reasoning. Positive evidence remains valid.
pub(super) fn note_incomplete_reasoning() {
    INCOMPLETE_REASONING_EPOCH.with(|count| count.set(count.get() + 1));
}

/// Monotonic, thread-local epoch shared by all incomplete reasoning paths.
/// This is not a work budget and never limits a query.
pub(super) fn incomplete_reasoning_epoch() -> u64 {
    INCOMPLETE_REASONING_EPOCH.with(Cell::get)
}

/// Kernel checkpoint: retain the limit signal for enclosing negative memos.
/// The instrumentation checkpoint also checks deterministic tactic work and
/// retains diagnostics for the outer verification error boundary. Call it
/// exactly once so this wrapper does not change checkpoint work accounting.
pub(crate) fn reasoning_interrupted() -> bool {
    let interrupted = crate::instrumentation::deadline_exceeded();
    if interrupted {
        note_incomplete_reasoning();
    }
    interrupted
}

/// Whether the verification deadline has passed, noted as a truncation so
/// the memo layers do not cache an answer the deadline cut short. A solve
/// derivation has no step budget of its own: its decisions are memoized
/// per condition and cycle-cut, its recursion follows the proposition, and
/// its premise selection is bounded by the candidate facts, so its work is
/// bounded by the goal and the facts the goal names.
pub(crate) fn solve_reasoning_interrupted() -> bool {
    reasoning_interrupted()
}

/// Marks a condition whose fact-based solve proof is in progress. Proving a
/// condition from the proposition facts can decide other conditions, which
/// consult the facts again; a condition met again while its own proof is
/// in progress is a cycle through the facts and proves nothing on that
/// path. Distinct conditions nest freely, bounded by the conditions the
/// facts connect to the query.
struct SelectedFactReasoningGuard {
    key: (ConditionTerm, bool),
}

impl SelectedFactReasoningGuard {
    fn enter(condition: &ConditionTerm, value: bool) -> Option<Self> {
        let key = (condition.clone(), value);
        let entered = SOLVE_FACT_CONDITIONS_IN_PROGRESS
            .with(|conditions| conditions.borrow_mut().insert(key.clone()));
        if !entered {
            // Refusing the repeated query makes any enclosing negative
            // answer path-dependent, so it must not populate a memo.
            note_incomplete_reasoning();
            return None;
        }
        Some(Self { key })
    }
}

impl Drop for SelectedFactReasoningGuard {
    fn drop(&mut self) {
        SOLVE_FACT_CONDITIONS_IN_PROGRESS.with(|conditions| {
            conditions.borrow_mut().remove(&self.key);
        });
    }
}

/// A condition already being proved from the facts refuses re-entry, records
/// incomplete reasoning without unregistering the outer proof, and distinct
/// conditions nest.
#[cfg(test)]
#[test]
fn solve_fact_reasoning_guard_refuses_reentry_and_keeps_the_outer_proof() {
    let first = ConditionTerm::equal(
        Bitvector32Term::Variable(Variable(7_400_000)),
        Bitvector32Term::Constant(1),
    );
    let second = ConditionTerm::equal(
        Bitvector32Term::Variable(Variable(7_400_001)),
        Bitvector32Term::Constant(2),
    );
    let epoch_before = incomplete_reasoning_epoch();
    let outer = SelectedFactReasoningGuard::enter(&first, true).expect("the first proof registers");
    assert!(
        SelectedFactReasoningGuard::enter(&first, true).is_none(),
        "re-entering the condition is a cycle"
    );
    assert_eq!(
        incomplete_reasoning_epoch(),
        epoch_before + 1,
        "the cycle makes an enclosing negative answer unsafe to memoize"
    );
    let nested = SelectedFactReasoningGuard::enter(&second, true);
    assert!(nested.is_some(), "a distinct condition nests");
    assert!(
        SelectedFactReasoningGuard::enter(&first, false).is_some(),
        "the other polarity is a distinct proof"
    );
    drop(nested);
    assert!(
        SelectedFactReasoningGuard::enter(&first, true).is_none(),
        "the refused re-entry left the outer proof registered"
    );
    assert_eq!(
        incomplete_reasoning_epoch(),
        epoch_before + 2,
        "each refused query advances the incompleteness epoch"
    );
    drop(outer);
    assert!(SelectedFactReasoningGuard::enter(&first, true).is_some());
}

struct ConditionDecisionGuard {
    condition: ConditionTerm,
}

impl ConditionDecisionGuard {
    // Order matching can compare memory loads, which can ask alias questions
    // whose pointer arithmetic re-enters the original order query. Repeating
    // an in-progress query cannot add evidence, so stop that branch
    // conservatively instead of recursing through the Rust stack.
    fn enter(condition: &ConditionTerm) -> Option<Self> {
        CONDITION_DECISIONS_IN_PROGRESS.with(|in_progress| {
            let mut in_progress = in_progress.borrow_mut();
            if !in_progress.insert(condition.clone()) {
                note_incomplete_reasoning();
                return None;
            }
            Some(Self {
                condition: condition.clone(),
            })
        })
    }
}

impl Drop for ConditionDecisionGuard {
    fn drop(&mut self) {
        CONDITION_DECISIONS_IN_PROGRESS.with(|in_progress| {
            in_progress.borrow_mut().remove(&self.condition);
        });
    }
}

/// Pointer-offset equality up to exact materialization: two forms of one
/// offset whose embedded loads resolve, cell by known cell, to the same
/// innermost term. Deterministic and assumption-free; never equates loads
/// across an unresolved havoc.
pub(in crate::kernel) fn pointer_offsets_equal_after_exact_materialization(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (
            PointerOffsetTerm::Int32Scaled {
                value: left_value,
                byte_width: left_width,
            },
            PointerOffsetTerm::Int32Scaled {
                value: right_value,
                byte_width: right_width,
            },
        ) => {
            left_width == right_width
                && (bitvector_terms_equal_after_exact_materialization(left_value, right_value)
                    || loads_equal_by_bounded_snapshot_match(left_value, right_value))
        }
        (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) => {
            (pointer_offsets_equal_after_exact_materialization(left_a, right_a)
                && pointer_offsets_equal_after_exact_materialization(left_b, right_b))
                || (pointer_offsets_equal_after_exact_materialization(left_a, right_b)
                    && pointer_offsets_equal_after_exact_materialization(left_b, right_a))
        }
        _ => false,
    }
}

/// Two irreducible loads of the same cell whose memory forms differ only
/// by materialization drift: chase each load to its fixed point, then let the
/// bounded snapshot matcher decide the memory pair at that one cell. Havoc
/// markers must match on both sides, so this never equates loads across an
/// unresolved havoc. Assumption-free.
fn loads_equal_by_bounded_snapshot_match(left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
    let (Some(left_load), Some(right_load)) = (
        crate::kernel::eval::viewed_as_memory_load(&exact_materialized_load_fixed_point(left)),
        crate::kernel::eval::viewed_as_memory_load(&exact_materialized_load_fixed_point(right)),
    ) else {
        return false;
    };
    let (
        Bitvector32Term::MemoryLoad(left_memory, left_pointer, left_kind),
        Bitvector32Term::MemoryLoad(right_memory, right_pointer, right_kind),
    ) = (&left_load, &right_load)
    else {
        return false;
    };
    left_pointer == right_pointer
        && left_kind == right_kind
        && !crate::kernel::reasoning::loads_separated_by_recorded_history(
            left_memory,
            right_memory,
            left_pointer,
            *left_kind,
            &PureFactContext::new(),
        )
        && crate::kernel::reasoning::memories_match_for_pointer_load_under_assumptions(
            left_memory,
            right_memory,
            left_pointer,
            &PureFactContext::new(),
        )
}

fn bitvector_terms_equal_after_exact_materialization(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> bool {
    exact_materialized_load_fixed_point(left) == exact_materialized_load_fixed_point(right)
}

fn exact_materialized_load_fixed_point(term: &Bitvector32Term) -> Bitvector32Term {
    let mut current = term.clone();
    let mut visited = std::collections::HashSet::new();
    while visited.insert(current.clone()) {
        crate::instrumentation::record_deterministic_work(1);
        let Bitvector32Term::MemoryLoad(memory, pointer, LoadKind::Int32) = &current else {
            break;
        };
        let Some(CValue::Int32(value)) = memory.known_value(pointer) else {
            break;
        };
        current = value;
    }
    current
}

#[cfg(test)]
mod exact_materialization_tests {
    use super::*;

    fn load_chain(length: usize, tail: u32) -> Bitvector32Term {
        let pointer = Pointer {
            block: "exact-load-chain".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        (0..length).fold(Bitvector32Term::Constant(tail), |value, _| {
            let memory = CMemory::new().store(pointer.clone(), CValue::Int32(value));
            Bitvector32Term::MemoryLoad(
                intern_c_memory(memory),
                Box::new(pointer.clone()),
                crate::kernel::LoadKind::Int32,
            )
        })
    }

    #[test]
    fn exact_materialization_follows_an_acyclic_chain_past_the_old_hop_limit() {
        let chain = load_chain(80, 17);
        assert_eq!(
            exact_materialized_load_fixed_point(&chain),
            Bitvector32Term::Constant(17)
        );
        assert!(bitvector_terms_equal_after_exact_materialization(
            &chain,
            &Bitvector32Term::Constant(17)
        ));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/assumptions/exact_materialization_tests.rs");
    }
}

pub(crate) fn proposition_has_free_bitvector_variable(
    proposition: &Proposition,
    variable: Variable,
) -> bool {
    match proposition {
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            proposition_has_free_bitvector_variable(left, variable)
                || proposition_has_free_bitvector_variable(right, variable)
        }
        Proposition::Not(body) => proposition_has_free_bitvector_variable(body, variable),
        Proposition::ForAll { var, body, .. } | Proposition::Exists { var, body, .. } => {
            *var != variable && proposition_has_free_bitvector_variable(body, variable)
        }
        proposition => {
            let mut variables = BTreeSet::new();
            collect_proposition_bitvector_variables(proposition, &mut variables);
            variables.contains(&variable)
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum SignedConstantResolution {
    Unknown,
    Known(i64),
    Ambiguous,
}

impl SignedConstantResolution {
    pub(in crate::kernel) fn merge(self, other: Self) -> Self {
        match (self, other) {
            (Self::Ambiguous, _) | (_, Self::Ambiguous) => Self::Ambiguous,
            (Self::Unknown, resolution) | (resolution, Self::Unknown) => resolution,
            (Self::Known(left), Self::Known(right)) if left == right => Self::Known(left),
            (Self::Known(_), Self::Known(_)) => Self::Ambiguous,
        }
    }

    pub(in crate::kernel) fn from_term(term: Bitvector32Term) -> Self {
        signed_bitvector_constant(&term).map_or(Self::Unknown, Self::Known)
    }

    pub(in crate::kernel) fn map(self, operation: impl FnOnce(i64) -> Bitvector32Term) -> Self {
        match self {
            Self::Known(value) => Self::from_term(operation(value)),
            Self::Unknown => Self::Unknown,
            Self::Ambiguous => Self::Ambiguous,
        }
    }
}

pub(in crate::kernel) fn memory_blind_pointer_fingerprint(pointer: &Pointer) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    hash_memory_blind_pointer(pointer, &mut hasher);
    std::hash::Hasher::finish(&hasher)
}

fn hash_memory_blind_pointer<H: std::hash::Hasher>(pointer: &Pointer, hasher: &mut H) {
    std::hash::Hash::hash(&pointer.block, hasher);
    hash_memory_blind_pointer_offset(&pointer.offset, hasher);
}

fn hash_memory_blind_pointer_offset<H: std::hash::Hasher>(
    offset: &PointerOffsetTerm,
    hasher: &mut H,
) {
    std::hash::Hash::hash(&std::mem::discriminant(offset), hasher);
    match offset {
        PointerOffsetTerm::Constant(value) => std::hash::Hash::hash(value, hasher),
        PointerOffsetTerm::Variable(variable) => std::hash::Hash::hash(variable, hasher),
        PointerOffsetTerm::Add(left, right) => {
            hash_memory_blind_pointer_offset(left, hasher);
            hash_memory_blind_pointer_offset(right, hasher);
        }
        PointerOffsetTerm::Int32Scaled { value, byte_width }
        | PointerOffsetTerm::Int64Scaled {
            value, byte_width, ..
        } => {
            hash_memory_blind_bitvector(value, hasher);
            std::hash::Hash::hash(byte_width, hasher);
        }
    }
}

fn hash_memory_blind_condition<H: std::hash::Hasher>(condition: &ConditionTerm, hasher: &mut H) {
    std::hash::Hash::hash(&std::mem::discriminant(condition), hasher);
    match condition {
        ConditionTerm::PointerValueEqual(left, right) => {
            std::hash::Hash::hash(left, hasher);
            std::hash::Hash::hash(right, hasher);
        }

        ConditionTerm::Constant(value) => std::hash::Hash::hash(value, hasher),
        ConditionTerm::AlgebraicEqual(left, right) => {
            std::hash::Hash::hash(left, hasher);
            std::hash::Hash::hash(right, hasher);
        }
        ConditionTerm::Variable(variable) => std::hash::Hash::hash(variable, hasher),
        crate::kernel::binary_bitvector_condition!(left, right) => {
            hash_memory_blind_bitvector(left, hasher);
            hash_memory_blind_bitvector(right, hasher);
        }
        ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
            std::hash::Hash::hash(float_condition, hasher);
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            hash_memory_blind_pointer_offset(left, hasher);
            hash_memory_blind_pointer_offset(right, hasher);
        }
        ConditionTerm::PointerEqual(left, right) => {
            hash_memory_blind_pointer(left, hasher);
            hash_memory_blind_pointer(right, hasher);
        }
        crate::kernel::integer_comparison_condition!(left, right) => {
            std::hash::Hash::hash(left, hasher);
            std::hash::Hash::hash(right, hasher);
        }
        // An application's arguments are hashed whole, as a word-valued
        // Click application's are.
        ConditionTerm::BoolApplication(application) => {
            std::hash::Hash::hash(application, hasher);
        }
        ConditionTerm::BoolIf {
            condition,
            then_condition,
            else_condition,
        } => {
            hash_memory_blind_condition(condition, hasher);
            hash_memory_blind_condition(then_condition, hasher);
            hash_memory_blind_condition(else_condition, hasher);
        }
        ConditionTerm::BoolEqual(left, right) => {
            hash_memory_blind_condition(left, hasher);
            hash_memory_blind_condition(right, hasher);
        }
        ConditionTerm::BoolLoad(_, pointer) => hash_memory_blind_pointer(pointer, hasher),
    }
}

fn hash_memory_blind_bitvector<H: std::hash::Hasher>(term: &Bitvector32Term, hasher: &mut H) {
    std::hash::Hash::hash(&std::mem::discriminant(term), hasher);
    match term {
        Bitvector32Term::MachineIntegerCast {
            value,
            source,
            destination,
        } => {
            std::hash::Hash::hash(source, hasher);
            std::hash::Hash::hash(destination, hasher);
            hash_memory_blind_bitvector(value, hasher);
        }
        Bitvector32Term::BoolCast { to, value } => {
            std::hash::Hash::hash(to, hasher);
            hash_memory_blind_condition(value, hasher);
        }

        Bitvector32Term::Constant(value) => std::hash::Hash::hash(value, hasher),
        Bitvector32Term::UInt32Constant(value) => {
            std::hash::Hash::hash("uint32", hasher);
            std::hash::Hash::hash(value, hasher)
        }
        Bitvector32Term::Int64Constant(value) => std::hash::Hash::hash(value, hasher),
        Bitvector32Term::UInt64Constant(value) => std::hash::Hash::hash(value, hasher),
        Bitvector32Term::MachineIntegerConstant(value) => std::hash::Hash::hash(value, hasher),
        Bitvector32Term::Variable(variable) => std::hash::Hash::hash(variable, hasher),
        Bitvector32Term::MemoryLoad(_, pointer, kind) => {
            std::hash::Hash::hash(kind, hasher);
            hash_memory_blind_pointer(pointer, hasher)
        }
        Bitvector32Term::PointerAddress(pointer, _) => {
            std::hash::Hash::hash("address", hasher);
            hash_memory_blind_pointer(pointer, hasher)
        }
        crate::kernel::binary_bitvector32_term!(left, right) => {
            std::hash::Hash::hash(&term.machine_operator(), hasher);
            hash_memory_blind_bitvector(left, hasher);
            hash_memory_blind_bitvector(right, hasher);
        }
        Bitvector32Term::Int64From32(value)
        | Bitvector32Term::Int64FromUInt32(value)
        | Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::UInt32From64(value)
        | Bitvector32Term::UInt64FromInt32(value)
        | Bitvector32Term::UInt64FromInt64(value) => hash_memory_blind_bitvector(value, hasher),
        Bitvector32Term::Unary {
            format,
            op,
            operand,
        } => {
            std::hash::Hash::hash(format, hasher);
            std::hash::Hash::hash(op, hasher);
            hash_memory_blind_bitvector(operand, hasher)
        }
        Bitvector32Term::Binary {
            format,
            op,
            left,
            right,
        } => {
            std::hash::Hash::hash(format, hasher);
            std::hash::Hash::hash(op, hasher);
            hash_memory_blind_bitvector(left, hasher);
            hash_memory_blind_bitvector(right, hasher);
        }
        Bitvector32Term::Float32Binary { left, right, .. }
        | Bitvector32Term::Float64Binary { left, right, .. } => {
            hash_memory_blind_bitvector(left, hasher);
            hash_memory_blind_bitvector(right, hasher);
        }
        Bitvector32Term::Float32Negate(value) | Bitvector32Term::Float64Negate(value) => {
            hash_memory_blind_bitvector(value, hasher)
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            hash_memory_blind_condition(condition, hasher);
            hash_memory_blind_bitvector(then_term, hasher);
            hash_memory_blind_bitvector(else_term, hasher);
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            hash_memory_blind_bitvector(start, hasher);
            hash_memory_blind_bitvector(end, hasher);
            hash_memory_blind_bitvector(initial, hasher);
            std::hash::Hash::hash(accumulator, hasher);
            std::hash::Hash::hash(item, hasher);
            hash_memory_blind_bitvector(body, hasher);
        }
        Bitvector32Term::PureFunctionApplication { name, arguments } => {
            std::hash::Hash::hash(name, hasher);
            for argument in arguments {
                hash_memory_blind_bitvector(argument, hasher);
            }
        }
        Bitvector32Term::ClickFunctionApplication { .. }
        | Bitvector32Term::AlgebraicMatch { .. } => std::hash::Hash::hash(term, hasher),
        Bitvector32Term::IntegerToMachine { value, destination } => {
            std::hash::Hash::hash(destination, hasher);
            std::hash::Hash::hash(value, hasher);
        }
    }
}

fn collect_condition_memory_load_keys(
    condition: &ConditionTerm,
    keys: &mut BTreeSet<(PointerBlock, u64)>,
) {
    let mut collect_binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        collect_bitvector_memory_load_keys(left, keys);
        collect_bitvector_memory_load_keys(right, keys);
    };
    match condition {
        ConditionTerm::PointerValueEqual(left, right) => {
            for pointer in left.pointers().chain(right.pointers()) {
                collect_pointer_offset_memory_load_keys(&pointer.offset, keys);
            }
        }

        ConditionTerm::AlgebraicEqual(left, right) => {
            left.for_each_bitvector_term(|term| collect_bitvector_memory_load_keys(term, keys));
            right.for_each_bitvector_term(|term| collect_bitvector_memory_load_keys(term, keys));
        }
        crate::kernel::binary_bitvector_condition!(left, right) => collect_binary(left, right),
        ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
            float_condition
                .for_each_bitvector_term(|term| collect_bitvector_memory_load_keys(term, keys));
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            collect_pointer_offset_memory_load_keys(left, keys);
            collect_pointer_offset_memory_load_keys(right, keys);
        }
        ConditionTerm::PointerEqual(left, right) => {
            collect_pointer_offset_memory_load_keys(&left.offset, keys);
            collect_pointer_offset_memory_load_keys(&right.offset, keys);
        }
        crate::kernel::integer_comparison_condition!(_, _) => {}
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {}
        // As a word-valued Click application's: its arguments are not keyed.
        ConditionTerm::BoolApplication(_) => {}
        ConditionTerm::BoolIf {
            condition,
            then_condition,
            else_condition,
        } => {
            for condition in [condition, then_condition, else_condition] {
                collect_condition_memory_load_keys(condition, keys);
            }
        }
        ConditionTerm::BoolEqual(left, right) => {
            collect_condition_memory_load_keys(left, keys);
            collect_condition_memory_load_keys(right, keys);
        }
        ConditionTerm::BoolLoad(_, pointer) => {
            keys.insert((
                pointer.block.clone(),
                memory_blind_pointer_fingerprint(pointer),
            ));
            collect_pointer_offset_memory_load_keys(&pointer.offset, keys);
        }
    }
}

fn collect_pointer_offset_memory_load_keys(
    offset: &PointerOffsetTerm,
    keys: &mut BTreeSet<(PointerBlock, u64)>,
) {
    offset.for_each_scaled_value(|value| collect_bitvector_memory_load_keys(value, keys));
}

fn collect_bitvector_memory_load_keys(
    term: &Bitvector32Term,
    keys: &mut BTreeSet<(PointerBlock, u64)>,
) {
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::UInt32Constant(_)
        | Bitvector32Term::Variable(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::MachineIntegerConstant(_) => {}
        Bitvector32Term::MemoryLoad(_, pointer, _) => {
            keys.insert((
                pointer.block.clone(),
                memory_blind_pointer_fingerprint(pointer),
            ));
            collect_pointer_offset_memory_load_keys(&pointer.offset, keys);
        }
        Bitvector32Term::PointerAddress(pointer, _) => {
            collect_pointer_offset_memory_load_keys(&pointer.offset, keys);
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_memory_load_keys(condition, keys);
            collect_bitvector_memory_load_keys(then_term, keys);
            collect_bitvector_memory_load_keys(else_term, keys);
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_bitvector_memory_load_keys(start, keys);
            collect_bitvector_memory_load_keys(end, keys);
            collect_bitvector_memory_load_keys(initial, keys);
            collect_bitvector_memory_load_keys(body, keys);
        }
        Bitvector32Term::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_bitvector_memory_load_keys(argument, keys);
            }
        }
        Bitvector32Term::ClickFunctionApplication { .. }
        | Bitvector32Term::AlgebraicMatch { .. } => {}
        Bitvector32Term::IntegerToMachine { .. } => {}
        Bitvector32Term::BoolCast { value, .. } => collect_condition_memory_load_keys(value, keys),
        term => {
            if let Some((_, left, right)) = term.as_binary() {
                collect_bitvector_memory_load_keys(left, keys);
                collect_bitvector_memory_load_keys(right, keys);
            } else {
                let (_, value) = term
                    .as_unary()
                    .expect("every other term is binary or unary");
                collect_bitvector_memory_load_keys(value, keys);
            }
        }
    }
}

/// Collect every current-snapshot load nested in a lowered term.  This is the
/// boundary used by dynamic resource checking, so an unrecognised carrier is
/// an error rather than an invitation to silently forget a memory dependency.
pub(crate) fn current_memory_loads_in_term(
    term: &Term,
    current_memory: &CMemory,
) -> Result<Vec<(Pointer, u32)>, String> {
    let mut loads = Vec::new();
    collect_term_memory_loads(term, current_memory, &mut loads, &mut BTreeSet::new())?;
    loads.sort();
    loads.dedup();
    Ok(loads)
}

fn collect_term_memory_loads(
    term: &Term,
    current_memory: &CMemory,
    loads: &mut Vec<(Pointer, u32)>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    match term {
        Term::Condition(condition) => {
            collect_condition_memory_loads(condition, current_memory, loads, seen_integers)
        }
        Term::Bitvector32(term) => {
            collect_bitvector_memory_loads(term, current_memory, loads, None, seen_integers)
        }
        Term::Integer(term) => {
            collect_integer_memory_loads(term, current_memory, loads, seen_integers)
        }
        Term::PointerOffset(offset) => {
            collect_pointer_offset_memory_loads(offset, current_memory, loads, seen_integers)
        }
        Term::CValue(value) => {
            collect_cvalue_memory_loads(value, current_memory, loads, seen_integers)
        }
        Term::Sequence(sequence) => {
            collect_sequence_memory_loads(sequence, current_memory, loads, seen_integers)
        }
        Term::Algebraic(term) => {
            collect_algebraic_memory_loads(term, current_memory, loads, seen_integers)
        }
        Term::CExpressionOutcome(outcome) => match outcome {
            CExpressionOutcome::Value(value) => {
                collect_cvalue_memory_loads(value, current_memory, loads, seen_integers)
            }
            CExpressionOutcome::UndefinedBehavior(_) | CExpressionOutcome::RuntimeError(_) => {
                Ok(())
            }
        },
        Term::CStatementOutcome(outcome) => match outcome.as_ref() {
            CStatementOutcome::Normal(state)
            | CStatementOutcome::Break(state)
            | CStatementOutcome::Continue(state)
            | CStatementOutcome::Jump { state, .. } => {
                let _ = state;
                Ok(())
            }
            CStatementOutcome::Return { value, state }
            | CStatementOutcome::Throw { value, state } => {
                let _ = state;
                collect_cvalue_memory_loads(value, current_memory, loads, seen_integers)
            }
            CStatementOutcome::VerificationDiverges
            | CStatementOutcome::UndefinedBehavior(_)
            | CStatementOutcome::RuntimeError(_) => Ok(()),
        },
        Term::CFunctionOutcome(outcome) => match outcome.as_ref() {
            CFunctionOutcome::Return { value, state }
            | CFunctionOutcome::Throw { value, state } => {
                let _ = state;
                collect_cvalue_memory_loads(value, current_memory, loads, seen_integers)
            }
            CFunctionOutcome::VerificationDiverges
            | CFunctionOutcome::UndefinedBehavior(_)
            | CFunctionOutcome::RuntimeError(_) => Ok(()),
        },
        Term::CMemory(_) | Term::CState(_) => Ok(()),
    }
}

fn collect_condition_memory_loads(
    condition: &ConditionTerm,
    current_memory: &CMemory,
    loads: &mut Vec<(Pointer, u32)>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    match condition {
        ConditionTerm::PointerValueEqual(left, right) => {
            for pointer in left.pointers().chain(right.pointers()) {
                collect_pointer_offset_memory_loads(
                    &pointer.offset,
                    current_memory,
                    loads,
                    seen_integers,
                )?;
            }
            Ok(())
        }

        ConditionTerm::AlgebraicEqual(left, right) => {
            collect_algebraic_memory_loads(left, current_memory, loads, seen_integers)?;
            collect_algebraic_memory_loads(right, current_memory, loads, seen_integers)
        }
        ConditionTerm::Compare {
            format,
            left,
            right,
            ..
        }
        | ConditionTerm::Overflows {
            format,
            left,
            right,
            ..
        } => {
            let width = Some(format.carrier_bytes());
            collect_bitvector_memory_loads(left, current_memory, loads, width, seen_integers)?;
            collect_bitvector_memory_loads(right, current_memory, loads, width, seen_integers)
        }
        ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
            let width = if matches!(condition, ConditionTerm::Float32(_)) {
                4
            } else {
                8
            };
            let mut result = Ok(());
            float_condition.for_each_bitvector_term(|term| {
                if result.is_ok() {
                    result = collect_bitvector_memory_loads(
                        term,
                        current_memory,
                        loads,
                        Some(width),
                        seen_integers,
                    );
                }
            });
            result
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            collect_pointer_offset_memory_loads(left, current_memory, loads, seen_integers)?;
            collect_pointer_offset_memory_loads(right, current_memory, loads, seen_integers)
        }
        ConditionTerm::PointerEqual(left, right) => {
            collect_pointer_offset_memory_loads(
                &left.offset,
                current_memory,
                loads,
                seen_integers,
            )?;
            collect_pointer_offset_memory_loads(&right.offset, current_memory, loads, seen_integers)
        }
        crate::kernel::integer_comparison_condition!(left, right) => {
            collect_integer_memory_loads(left, current_memory, loads, seen_integers)?;
            collect_integer_memory_loads(right, current_memory, loads, seen_integers)
        }
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => Ok(()),
        ConditionTerm::BoolApplication(_) => {
            Err("opaque Click function may hide a current memory load".into())
        }
        ConditionTerm::BoolIf {
            condition,
            then_condition,
            else_condition,
        } => {
            for condition in [condition, then_condition, else_condition] {
                collect_condition_memory_loads(condition, current_memory, loads, seen_integers)?;
            }
            Ok(())
        }
        ConditionTerm::BoolEqual(left, right) => {
            collect_condition_memory_loads(left, current_memory, loads, seen_integers)?;
            collect_condition_memory_loads(right, current_memory, loads, seen_integers)
        }
        // A `bool` cell is one byte.
        ConditionTerm::BoolLoad(memory, pointer) => {
            if CMemorySnapshotIdentity::of(memory.memory())
                == CMemorySnapshotIdentity::of(current_memory)
            {
                loads.push((pointer.as_ref().clone(), 1));
            }
            collect_pointer_offset_memory_loads(
                &pointer.offset,
                current_memory,
                loads,
                seen_integers,
            )
        }
    }
}

fn collect_pointer_offset_memory_loads(
    offset: &PointerOffsetTerm,
    current_memory: &CMemory,
    loads: &mut Vec<(Pointer, u32)>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => Ok(()),
        PointerOffsetTerm::Add(left, right) => {
            collect_pointer_offset_memory_loads(left, current_memory, loads, seen_integers)?;
            collect_pointer_offset_memory_loads(right, current_memory, loads, seen_integers)
        }
        PointerOffsetTerm::Int32Scaled { value, .. } => {
            collect_bitvector_memory_loads(value, current_memory, loads, Some(4), seen_integers)
        }
        PointerOffsetTerm::Int64Scaled { value, .. } => {
            collect_bitvector_memory_loads(value, current_memory, loads, Some(8), seen_integers)
        }
    }
}

fn collect_bitvector_memory_loads(
    term: &Bitvector32Term,
    current_memory: &CMemory,
    loads: &mut Vec<(Pointer, u32)>,
    width: Option<u32>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    collect_bitvector_memory_loads_with_width(term, current_memory, loads, width, seen_integers)
}

fn collect_bitvector_memory_loads_with_width(
    term: &Bitvector32Term,
    current_memory: &CMemory,
    loads: &mut Vec<(Pointer, u32)>,
    width: Option<u32>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    match term {
        Bitvector32Term::MachineIntegerCast { value, source, .. } => {
            collect_bitvector_memory_loads_with_width(
                value,
                current_memory,
                loads,
                Some(source.format().byte_width()),
                seen_integers,
            )
        }

        Bitvector32Term::Constant(_)
        | Bitvector32Term::UInt32Constant(_)
        | Bitvector32Term::Variable(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::MachineIntegerConstant(_) => Ok(()),
        Bitvector32Term::MemoryLoad(memory, pointer, _) => {
            if CMemorySnapshotIdentity::of(memory.memory())
                == CMemorySnapshotIdentity::of(current_memory)
            {
                let width = width.ok_or_else(|| {
                    "current memory load has no statically known byte width".to_string()
                })?;
                loads.push((pointer.as_ref().clone(), width));
            }
            collect_pointer_offset_memory_loads(
                &pointer.offset,
                current_memory,
                loads,
                seen_integers,
            )
        }
        Bitvector32Term::PointerAddress(pointer, _) => collect_pointer_offset_memory_loads(
            &pointer.offset,
            current_memory,
            loads,
            seen_integers,
        ),
        crate::kernel::binary_machine_term!(left, right)
        | Bitvector32Term::Float32Binary { left, right, .. }
        | Bitvector32Term::Float64Binary { left, right, .. } => {
            let child_width = if matches!(
                term,
                crate::kernel::binary_wide_term!(..) | Bitvector32Term::Float64Binary { .. }
            ) {
                Some(8)
            } else {
                width
            };
            collect_bitvector_memory_loads_with_width(
                left,
                current_memory,
                loads,
                child_width,
                seen_integers,
            )?;
            collect_bitvector_memory_loads_with_width(
                right,
                current_memory,
                loads,
                child_width,
                seen_integers,
            )
        }
        Bitvector32Term::Int64From32(value)
        | Bitvector32Term::Int64FromUInt32(value)
        | Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::UInt32From64(value)
        | Bitvector32Term::UInt64FromInt32(value)
        | Bitvector32Term::UInt64FromInt64(value)
        | Bitvector32Term::Unary { operand: value, .. }
        | Bitvector32Term::Float32Negate(value)
        | Bitvector32Term::Float64Negate(value) => {
            let child_width = if matches!(term, Bitvector32Term::Float64Negate(_)) {
                Some(8)
            } else {
                width
            };
            collect_bitvector_memory_loads_with_width(
                value,
                current_memory,
                loads,
                child_width,
                seen_integers,
            )
        }
        Bitvector32Term::IntegerToMachine { value, destination } => {
            let width = Some(match destination {
                MachineIntegerType::Int8 => 1,
                MachineIntegerType::Int16 | MachineIntegerType::UInt16 => 2,
                MachineIntegerType::UInt8 => 1,
                MachineIntegerType::Int32 | MachineIntegerType::UInt32 => 4,
                MachineIntegerType::Int64 | MachineIntegerType::UInt64 => 8,
                MachineIntegerType::Int128 | MachineIntegerType::UInt128 => 16,
            });
            collect_integer_memory_loads_with_width(
                value,
                current_memory,
                loads,
                width,
                seen_integers,
            )
        }
        Bitvector32Term::BoolCast { value, .. } => {
            collect_condition_memory_loads(value, current_memory, loads, seen_integers)
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_memory_loads(condition, current_memory, loads, seen_integers)?;
            collect_bitvector_memory_loads_with_width(
                then_term,
                current_memory,
                loads,
                width,
                seen_integers,
            )?;
            collect_bitvector_memory_loads_with_width(
                else_term,
                current_memory,
                loads,
                width,
                seen_integers,
            )
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_bitvector_memory_loads_with_width(
                start,
                current_memory,
                loads,
                width,
                seen_integers,
            )?;
            collect_bitvector_memory_loads_with_width(
                end,
                current_memory,
                loads,
                width,
                seen_integers,
            )?;
            collect_bitvector_memory_loads_with_width(
                initial,
                current_memory,
                loads,
                width,
                seen_integers,
            )?;
            collect_bitvector_memory_loads_with_width(
                body,
                current_memory,
                loads,
                width,
                seen_integers,
            )
        }
        Bitvector32Term::PureFunctionApplication { arguments, .. } => {
            let _ = (arguments, width, seen_integers);
            Err("opaque pure function may hide a current memory load".into())
        }
        Bitvector32Term::ClickFunctionApplication { .. } => {
            Err("opaque Click function may hide a current memory load".into())
        }
        Bitvector32Term::AlgebraicMatch { scrutinee, arms } => {
            collect_algebraic_memory_loads(scrutinee, current_memory, loads, seen_integers)?;
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_memory_loads(
                        binding,
                        current_memory,
                        loads,
                        seen_integers,
                    )?;
                }
                collect_bitvector_memory_loads_with_width(
                    &arm.body,
                    current_memory,
                    loads,
                    width,
                    seen_integers,
                )?;
            }
            Ok(())
        }
    }
}

fn collect_cvalue_memory_loads(
    value: &CValue,
    current_memory: &CMemory,
    loads: &mut Vec<(Pointer, u32)>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    match value.numeric_value() {
        CValue::PointerInteger(_) => unreachable!("numeric projection"),
        CValue::Int128(term) | CValue::UInt128(term) => collect_bitvector_memory_loads_with_width(
            term,
            current_memory,
            loads,
            Some(16),
            seen_integers,
        ),

        CValue::Parameter(term) => {
            collect_algebraic_memory_loads(term, current_memory, loads, seen_integers)
        }
        CValue::Void => Ok(()),
        CValue::Bool(term) | CValue::UInt8(term) => collect_bitvector_memory_loads_with_width(
            term,
            current_memory,
            loads,
            Some(1),
            seen_integers,
        ),
        CValue::Int8(term) => collect_bitvector_memory_loads_with_width(
            term,
            current_memory,
            loads,
            Some(1),
            seen_integers,
        ),
        CValue::Int16(term) | CValue::UInt16(term) => collect_bitvector_memory_loads_with_width(
            term,
            current_memory,
            loads,
            Some(2),
            seen_integers,
        ),
        CValue::Int32(term) | CValue::UInt32(term) | CValue::Float32(term) => {
            collect_bitvector_memory_loads_with_width(
                term,
                current_memory,
                loads,
                Some(4),
                seen_integers,
            )
        }
        CValue::Int64(term) | CValue::UInt64(term) | CValue::Float64(term) => {
            collect_bitvector_memory_loads_with_width(
                term,
                current_memory,
                loads,
                Some(8),
                seen_integers,
            )
        }
        CValue::Pointer(pointer) => collect_pointer_offset_memory_loads(
            &pointer.pointer().offset,
            current_memory,
            loads,
            seen_integers,
        ),
    }
}

fn collect_sequence_memory_loads(
    sequence: &SequenceTerm,
    current_memory: &CMemory,
    loads: &mut Vec<(Pointer, u32)>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    match sequence.node.as_ref() {
        SequenceTermNode::Literal(values) => {
            for value in values.iter() {
                collect_cvalue_memory_loads(value, current_memory, loads, seen_integers)?;
            }
            Ok(())
        }
        SequenceTermNode::Concat(left, right) => {
            collect_sequence_memory_loads(left, current_memory, loads, seen_integers)?;
            collect_sequence_memory_loads(right, current_memory, loads, seen_integers)
        }
    }
}

fn collect_algebraic_value_memory_loads(
    value: &AlgebraicValue,
    current_memory: &CMemory,
    loads: &mut Vec<(Pointer, u32)>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    match value {
        AlgebraicValue::C(value) => {
            collect_cvalue_memory_loads(value, current_memory, loads, seen_integers)
        }
        AlgebraicValue::Integer(value) => {
            collect_integer_memory_loads(value, current_memory, loads, seen_integers)
        }
        AlgebraicValue::Algebraic(value) => {
            collect_algebraic_memory_loads(value, current_memory, loads, seen_integers)
        }
    }
}

fn collect_algebraic_memory_loads(
    term: &AlgebraicTerm,
    current_memory: &CMemory,
    loads: &mut Vec<(Pointer, u32)>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    match &term.node {
        AlgebraicTermNode::Variable(_) => Ok(()),
        AlgebraicTermNode::Constructor { fields, .. } => {
            for field in fields {
                collect_algebraic_value_memory_loads(field, current_memory, loads, seen_integers)?;
            }
            Ok(())
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            collect_algebraic_memory_loads(scrutinee, current_memory, loads, seen_integers)?;
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_memory_loads(
                        binding,
                        current_memory,
                        loads,
                        seen_integers,
                    )?;
                }
                collect_algebraic_memory_loads(&arm.body, current_memory, loads, seen_integers)?;
            }
            Ok(())
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            let _ = (arguments, current_memory, loads, seen_integers);
            Err("opaque algebraic function may hide a current memory load".into())
        }
        AlgebraicTermNode::MemoryLoad { memory, pointer } => {
            collect_bitvector_memory_loads_with_width(
                &AlgebraicTermNode::memory_load_carrier(memory, pointer),
                current_memory,
                loads,
                Some(crate::kernel::ABSTRACT_VALUE_WIDTH),
                seen_integers,
            )
        }
        AlgebraicTermNode::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_memory_loads(condition, current_memory, loads, seen_integers)?;
            collect_algebraic_memory_loads(then_term, current_memory, loads, seen_integers)?;
            collect_algebraic_memory_loads(else_term, current_memory, loads, seen_integers)
        }
    }
}

fn collect_integer_memory_loads(
    term: &IntegerTerm,
    current_memory: &CMemory,
    loads: &mut Vec<(Pointer, u32)>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    collect_integer_node_memory_loads(term, current_memory, loads, None, seen_integers)
}

fn collect_integer_memory_loads_with_width(
    term: &SharedIntegerTerm,
    current_memory: &CMemory,
    loads: &mut Vec<(Pointer, u32)>,
    width: Option<u32>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    if !seen_integers.insert(term.id()) {
        return Ok(());
    }
    collect_integer_node_memory_loads(term.as_ref(), current_memory, loads, width, seen_integers)
}

fn collect_integer_node_memory_loads(
    term: &IntegerTerm,
    current_memory: &CMemory,
    loads: &mut Vec<(Pointer, u32)>,
    width: Option<u32>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    match term {
        IntegerTerm::Constant(_) | IntegerTerm::Variable(_) => Ok(()),
        IntegerTerm::Machine(value) => collect_bitvector_memory_loads_with_width(
            value.value(),
            current_memory,
            loads,
            Some(match value.ty() {
                MachineIntegerType::UInt8 => 1,
                MachineIntegerType::Int8 => 1,
                MachineIntegerType::Int16 | MachineIntegerType::UInt16 => 2,
                MachineIntegerType::Int32 | MachineIntegerType::UInt32 => 4,
                MachineIntegerType::Int64 | MachineIntegerType::UInt64 => 8,
                MachineIntegerType::Int128 | MachineIntegerType::UInt128 => 16,
            }),
            seen_integers,
        ),
        IntegerTerm::Negate(value) => collect_integer_memory_loads_with_width(
            value,
            current_memory,
            loads,
            width,
            seen_integers,
        ),
        crate::kernel::binary_integer_term!(left, right) => {
            collect_integer_memory_loads_with_width(
                left,
                current_memory,
                loads,
                width,
                seen_integers,
            )?;
            collect_integer_memory_loads_with_width(
                right,
                current_memory,
                loads,
                width,
                seen_integers,
            )
        }
        IntegerTerm::PureFunctionApplication(application) => {
            let _ = (application, current_memory, loads, seen_integers);
            Err("opaque integer function may hide a current memory load".into())
        }
        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_algebraic_memory_loads(scrutinee, current_memory, loads, seen_integers)?;
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_memory_loads(
                        binding,
                        current_memory,
                        loads,
                        seen_integers,
                    )?;
                }
                collect_integer_memory_loads_with_width(
                    &arm.body,
                    current_memory,
                    loads,
                    width,
                    seen_integers,
                )?;
            }
            Ok(())
        }
        IntegerTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_memory_loads(condition, current_memory, loads, seen_integers)?;
            collect_integer_memory_loads_with_width(
                then_term,
                current_memory,
                loads,
                width,
                seen_integers,
            )?;
            collect_integer_memory_loads_with_width(
                else_term,
                current_memory,
                loads,
                width,
                seen_integers,
            )
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            body,
            ..
        } => {
            match index {
                IntegerRangeFoldIndex::Int32 { start, end }
                | IntegerRangeFoldIndex::UInt64 { start, end } => {
                    let endpoint_width = if matches!(index, IntegerRangeFoldIndex::UInt64 { .. }) {
                        8
                    } else {
                        4
                    };
                    collect_bitvector_memory_loads_with_width(
                        start.value(),
                        current_memory,
                        loads,
                        Some(endpoint_width),
                        seen_integers,
                    )?;
                    collect_bitvector_memory_loads_with_width(
                        end.value(),
                        current_memory,
                        loads,
                        Some(endpoint_width),
                        seen_integers,
                    )?;
                }
                IntegerRangeFoldIndex::Integer { start, end } => {
                    collect_integer_memory_loads_with_width(
                        start,
                        current_memory,
                        loads,
                        width,
                        seen_integers,
                    )?;
                    collect_integer_memory_loads_with_width(
                        end,
                        current_memory,
                        loads,
                        width,
                        seen_integers,
                    )?;
                }
            }
            collect_integer_memory_loads_with_width(
                initial,
                current_memory,
                loads,
                width,
                seen_integers,
            )?;
            collect_integer_memory_loads_with_width(
                body,
                current_memory,
                loads,
                width,
                seen_integers,
            )
        }
    }
}

#[cfg(test)]
impl Proposition {
    pub(super) fn peel_implications(&self) -> &Self {
        match self {
            Self::Implies(_, body) => body.peel_implications(),
            _ => self,
        }
    }
}

/// What an equality between an algebraic `if` and a constructor decides:
/// `if c { A } else { B } == K` with `A` a constructor other than `K`'s
/// holds exactly when `c` is false and `B == K`, and with `B` one other than
/// `K`'s exactly when `c` is true and `A == K`. The condition, its value,
/// and the equality of the branch that remains.
fn decided_algebraic_if(proposition: &Proposition) -> Option<(ConditionTerm, bool, Proposition)> {
    let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = proposition else {
        return None;
    };
    let (conditional, constructor) = match (&left.node, &right.node) {
        (AlgebraicTermNode::If { .. }, AlgebraicTermNode::Constructor { .. }) => (left, right),
        (AlgebraicTermNode::Constructor { .. }, AlgebraicTermNode::If { .. }) => (right, left),
        _ => return None,
    };
    let (
        AlgebraicTermNode::If {
            condition,
            then_term,
            else_term,
        },
        AlgebraicTermNode::Constructor { variant, .. },
    ) = (&conditional.node, &constructor.node)
    else {
        return None;
    };
    let other_constructor = |term: &AlgebraicTerm| matches!(&term.node, AlgebraicTermNode::Constructor { variant: other, .. } if other != variant);
    let (value, selected) = if other_constructor(then_term) {
        (false, else_term)
    } else if other_constructor(else_term) {
        (true, then_term)
    } else {
        return None;
    };
    Some((
        condition.as_ref().clone(),
        value,
        Proposition::Equal(
            Term::Algebraic(selected.as_ref().clone()),
            Term::Algebraic(constructor.clone()),
        ),
    ))
}

/// Recompute the field equalities justified by one exact equality between
/// applications of the same checked algebraic constructor. This single
/// definition is shared by evidence production, index maintenance, and proof
/// checking so none of those layers can disagree about the rule.
pub(crate) fn algebraic_constructor_field_equalities(
    proposition: &Proposition,
) -> Option<Vec<Proposition>> {
    let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = proposition else {
        return None;
    };
    if left.algebraic_type != right.algebraic_type {
        return None;
    }
    let (
        AlgebraicTermNode::Constructor {
            variant: left_variant,
            ..
        },
        AlgebraicTermNode::Constructor {
            variant: right_variant,
            ..
        },
    ) = (&left.node, &right.node)
    else {
        return None;
    };
    if left_variant != right_variant {
        return None;
    }
    let left_fields = left.checked_constructor_fields()?;
    let right_fields = right.checked_constructor_fields()?;
    left_fields
        .iter()
        .zip(right_fields)
        .map(|(left, right)| match (left, right) {
            (AlgebraicValue::C(left), AlgebraicValue::C(right)) => {
                c_value_comparison_proposition(left, CComparisonOperator::Equal, right)
            }
            (AlgebraicValue::Algebraic(left), AlgebraicValue::Algebraic(right)) => {
                Some(Proposition::Equal(
                    Term::Algebraic(left.clone()),
                    Term::Algebraic(right.clone()),
                ))
            }
            _ => None,
        })
        .collect()
}

fn is_algebraic_constructor_conflict(proposition: &Proposition) -> bool {
    let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = proposition else {
        return false;
    };
    if left.algebraic_type != right.algebraic_type
        || left.checked_constructor_fields().is_none()
        || right.checked_constructor_fields().is_none()
    {
        return false;
    }
    matches!(
        (&left.node, &right.node),
        (
            AlgebraicTermNode::Constructor { variant: left, .. },
            AlgebraicTermNode::Constructor { variant: right, .. }
        ) if left != right
    )
}

impl PureFactContext {
    #[cfg(test)]
    pub(crate) fn reset_bitvector_equality_index_fact_visits() {
        BITVECTOR_EQUALITY_INDEX_FACT_VISITS.with(|visits| visits.set(0));
    }

    #[cfg(test)]
    pub(crate) fn bitvector_equality_index_fact_visits() -> usize {
        BITVECTOR_EQUALITY_INDEX_FACT_VISITS.with(Cell::get)
    }

    /// How many condition facts `exact_signed_constant` has examined on this
    /// thread since the last reset.
    #[cfg(test)]
    pub(crate) fn exact_constant_fact_visits() -> usize {
        EXACT_CONSTANT_FACT_VISITS.with(Cell::get)
    }

    /// How many condition facts the condition-fact queries have examined on
    /// this thread since the last reset.
    #[cfg(test)]
    pub(crate) fn condition_fact_visits() -> usize {
        CONDITION_FACT_VISITS.with(Cell::get)
    }

    #[cfg(test)]
    pub(crate) fn reset_condition_fact_visits() {
        CONDITION_FACT_VISITS.with(|visits| visits.set(0));
    }

    #[cfg(test)]
    pub(crate) fn reset_exact_constant_fact_visits() {
        EXACT_CONSTANT_FACT_VISITS.with(|visits| visits.set(0));
    }

    pub(in crate::kernel) fn has_same_reasoning_policy(&self, other: &Self) -> bool {
        self.reasoning_policy == other.reasoning_policy
    }

    fn fingerprint<T: std::hash::Hash>(tag: u64, value: &T) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        std::hash::Hasher::write_u64(&mut hasher, tag);
        std::hash::Hash::hash(value, &mut hasher);
        std::hash::Hasher::finish(&hasher)
    }

    fn recompute_content_fingerprint(&mut self) {
        let mut fingerprint = 0;
        for fact in self.condition_facts.scan_for_upkeep() {
            fingerprint ^= Self::fingerprint(1, &fact);
        }
        for fact in self.prop_facts.scan_for_upkeep() {
            fingerprint ^= Self::fingerprint(2, fact);
        }
        for (variable, definitions) in self
            .equality_graph
            .admitted
            .typed_pointer_read_definitions
            .iter()
        {
            for (key, (value, _)) in definitions.iter() {
                fingerprint ^= Self::typed_pointer_read_fingerprint(*variable, key, value);
            }
        }
        for resources in self.resource_compositions.scan_for_upkeep() {
            fingerprint ^= Self::fingerprint(3, resources);
        }
        if let Some(owners) = &self.store_owners {
            fingerprint ^= Self::fingerprint(5, owners);
        }
        fingerprint ^= self.reasoning_policy.fingerprint();
        self.content_fingerprint = fingerprint;
    }

    fn adjust_signed_order_bound(&mut self, condition: &ConditionTerm, value: bool, insert: bool) {
        self.checked_order_bounds.adjust(condition, value, insert);
        self.order_facts_by_lower.adjust(condition, value, insert);
        self.signed_variable_chains.adjust(condition, value, insert);
        if let Some((left, right, strict)) = condition_as_order_fact(condition, value) {
            let mut index = std::mem::take(&mut self.signed_order_bounds);
            Self::adjust_order_bound_index(&mut index, left, right, strict, insert);
            self.signed_order_bounds = index;
        } else if let Some((left, right, strict)) = condition_as_int64_order_fact(condition, value)
        {
            self.adjust_wide_order_edges(1, &left, &right, strict, insert);
            let mut index = std::mem::take(&mut self.int64_signed_order_bounds);
            Self::adjust_order_bound_index(&mut index, left, right, strict, insert);
            self.int64_signed_order_bounds = index;
        } else if let Some((left, right, strict)) =
            condition_reasoning::condition_as_uint32_order_fact(condition, value)
        {
            let mut index = std::mem::take(&mut self.uint32_order_bounds);
            Self::adjust_order_bound_index(&mut index, left, right, strict, insert);
            self.uint32_order_bounds = index;
        } else if let Some((left, right, strict)) =
            condition_reasoning::condition_as_uint64_order_fact(condition, value)
        {
            self.adjust_wide_order_edges(0, &left, &right, strict, insert);
            let mut index = std::mem::take(&mut self.uint64_order_bounds);
            Self::adjust_order_bound_index(&mut index, left, right, strict, insert);
            self.uint64_order_bounds = index;
        }
    }

    /// Files or removes one 64-bit order fact `left < right` (or `<=`) in
    /// the direction-split edges of `kind` (0 unsigned, 1 signed), under
    /// canonical terms: an upward edge from `left` and a downward one from
    /// `right`.
    fn adjust_wide_order_edges(
        &mut self,
        kind: usize,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        strict: bool,
        insert: bool,
    ) {
        let left = crate::kernel::eval::canonical_term(left);
        let right = crate::kernel::eval::canonical_term(right);
        for (direction, from, to) in [(0, &left, &right), (1, &right, &left)] {
            let index = &mut self.wide_order_edges[kind][direction];
            let mut edges = index.get(from).cloned().unwrap_or_default();
            let edge = (to.clone(), strict);
            let count = edges.get(&edge).copied().unwrap_or(0);
            if insert {
                edges = edges.with_inserted(edge, count + 1);
            } else if count <= 1 {
                edges = edges.without_key(&edge);
            } else {
                edges = edges.with_inserted(edge, count - 1);
            }
            *index = if edges.is_empty() {
                index.without_key(from)
            } else {
                index.with_inserted(from.clone(), edges)
            };
        }
    }

    fn adjust_order_bound_index(
        index: &mut crate::persistent::PersistentMap<
            Bitvector32Term,
            crate::persistent::PersistentMap<(Bitvector32Term, Bitvector32Term, bool, bool), usize>,
        >,
        left: Bitvector32Term,
        right: Bitvector32Term,
        strict: bool,
        insert: bool,
    ) {
        // Each endpoint is indexed under the term the fact wrote and, when
        // it differs, under its canonical form as an alias: a bound recorded
        // through one term answers a lookup through any equal term. Every
        // entry carries the fact's own endpoint term first, so evidence found
        // through the alias still cites the exact fact.
        let left_alias = crate::kernel::eval::canonical_term(&left);
        let right_alias = crate::kernel::eval::canonical_term(&right);
        let mut entries = vec![
            (left.clone(), (left.clone(), right.clone(), strict, true)),
            (right.clone(), (right.clone(), left.clone(), strict, false)),
        ];
        if left_alias != left {
            entries.push((left_alias, (left.clone(), right.clone(), strict, true)));
        }
        if right_alias != right {
            entries.push((right_alias, (right, left, strict, false)));
        }
        for (endpoint, bound) in entries {
            let mut bounds = index.get(&endpoint).cloned().unwrap_or_default();
            let count = bounds.get(&bound).copied().unwrap_or(0);
            if insert {
                bounds = bounds.with_inserted(bound, count + 1);
            } else if count <= 1 {
                bounds = bounds.without_key(&bound);
            } else {
                bounds = bounds.with_inserted(bound, count - 1);
            }
            *index = if bounds.is_empty() {
                index.without_key(&endpoint)
            } else {
                index.with_inserted(endpoint, bounds)
            };
        }
    }

    /// The pointer whose null-ness one condition fact decides, as the
    /// non-null-block side of an equality against the null pointer.
    ///
    /// Only an equality against the null pointer itself qualifies. A pointer
    /// already displaced from null is not a null test, and a fact relating
    /// two pointers of the null block says nothing about either being null.
    fn condition_as_null_pointer_fact(condition: &ConditionTerm) -> Option<&Pointer> {
        let ConditionTerm::PointerEqual(left, right) = condition else {
            return None;
        };
        let null = Pointer::null();
        match (left.as_ref() == &null, right.as_ref() == &null) {
            (true, false) => Some(right.as_ref()),
            (false, true) => Some(left.as_ref()),
            _ => None,
        }
    }

    /// Files or withdraws one null-ness fact under its pointer's offset.
    ///
    /// Touches exactly the one offset key the fact names, so a context that
    /// gains a null test pays for that test alone.
    fn adjust_null_pointer_offset(&mut self, condition: &ConditionTerm, value: bool, insert: bool) {
        let Some(pointer) = Self::condition_as_null_pointer_fact(condition) else {
            return;
        };
        let (block, offset) = (pointer.block.clone(), pointer.offset.clone());
        let key = (block, value);
        let blocks = self
            .null_pointer_offsets
            .get(&offset)
            .cloned()
            .unwrap_or_default();
        let blocks = if insert {
            blocks.with_inserted(key, condition.clone())
        } else {
            blocks.without_key(&key)
        };
        self.null_pointer_offsets = if blocks.is_empty() {
            self.null_pointer_offsets.without_key(&offset)
        } else {
            self.null_pointer_offsets.with_inserted(offset, blocks)
        };
    }

    /// Files or withdraws one exact pointer equality under both
    /// of its sides. Only a *true* equality says two spellings are one
    /// address; a false one is not an alias and never enters the index, which
    /// also makes withdrawal a no-op for the fact values that were never
    /// filed.
    fn adjust_pointer_address_source(
        &mut self,
        key: ConditionTerm,
        source: &ConditionTerm,
        insert: bool,
    ) -> Option<ConditionTerm> {
        let sources = self
            .equality_graph
            .admitted
            .pointer_address_sources
            .get(&key)
            .cloned()
            .unwrap_or_default();
        let sources = if insert {
            sources.with_value(source.clone())
        } else {
            sources.without_value(source)
        };
        let selected = sources.iter().next().cloned();
        self.equality_graph.admitted.pointer_address_sources = if sources.is_empty() {
            self.equality_graph
                .admitted
                .pointer_address_sources
                .without_key(&key)
        } else {
            self.equality_graph
                .admitted
                .pointer_address_sources
                .with_inserted(key, sources)
        };
        selected
    }

    fn adjust_pointer_block_alias(&mut self, condition: &ConditionTerm, value: bool, insert: bool) {
        if let Some((pointer, alignment)) = condition.as_pointer_alignment() {
            if value && alignment.is_power_of_two() {
                let key = (pointer.clone(), alignment);
                let sources = self
                    .equality_graph
                    .admitted
                    .pointer_alignment_facts
                    .get(&key)
                    .cloned()
                    .unwrap_or_default();
                let sources = if insert {
                    sources.with_value(condition.clone())
                } else {
                    sources.without_value(condition)
                };
                if sources.is_empty() {
                    self.equality_graph
                        .admitted
                        .pointer_alignment_facts
                        .remove(&key);
                } else {
                    self.equality_graph
                        .admitted
                        .pointer_alignment_facts
                        .insert(key, sources);
                }
                if insert {
                    self.equality_graph.register_alignment(pointer, alignment);
                } else {
                    self.rebuild_equality_graph();
                }
            }
            return;
        }
        let (left, right) = match condition {
            ConditionTerm::PointerEqual(left, right) => (left.as_ref(), right.as_ref()),
            ConditionTerm::PointerValueEqual(left, right) => (left.pointer(), right.pointer()),
            _ => return,
        };
        if !value || left == right {
            return;
        }
        let key = if left < right {
            ConditionTerm::pointer_equal(left.clone(), right.clone())
        } else {
            ConditionTerm::pointer_equal(right.clone(), left.clone())
        };
        let source = self.adjust_pointer_address_source(key, condition, insert);
        for (key, alias) in [(left, right), (right, left)] {
            let aliases = self
                .equality_graph
                .admitted
                .pointer_block_aliases
                .get(key)
                .cloned()
                .unwrap_or_default();
            let aliases = if let Some(source) = &source {
                aliases.with_inserted(alias.clone(), source.clone())
            } else {
                aliases.without_key(alias)
            };
            let filed = !aliases.is_empty();
            self.equality_graph.admitted.pointer_block_aliases = if filed {
                self.equality_graph
                    .admitted
                    .pointer_block_aliases
                    .with_inserted(key.clone(), aliases)
            } else {
                self.equality_graph
                    .admitted
                    .pointer_block_aliases
                    .without_key(key)
            };
            let bucket = memory_reasoning::parameter_alias_bucket(key);
            let endpoints = self
                .equality_graph
                .admitted
                .pointer_alias_endpoints_by_object
                .get(&bucket)
                .cloned()
                .unwrap_or_default();
            let endpoints = if filed {
                endpoints.with_value(key.clone())
            } else {
                endpoints.without_value(key)
            };
            self.equality_graph
                .admitted
                .pointer_alias_endpoints_by_object = if endpoints.is_empty() {
                self.equality_graph
                    .admitted
                    .pointer_alias_endpoints_by_object
                    .without_key(&bucket)
            } else {
                self.equality_graph
                    .admitted
                    .pointer_alias_endpoints_by_object
                    .with_inserted(bucket, endpoints)
            };
            let spellings = self
                .equality_graph
                .admitted
                .pointer_block_aliases_by_offset
                .get(&key.offset)
                .cloned()
                .unwrap_or_default();
            let spellings = if filed {
                spellings.with_value(key.clone())
            } else {
                spellings.without_value(key)
            };
            self.equality_graph.admitted.pointer_block_aliases_by_offset = if spellings.is_empty() {
                self.equality_graph
                    .admitted
                    .pointer_block_aliases_by_offset
                    .without_key(&key.offset)
            } else {
                self.equality_graph
                    .admitted
                    .pointer_block_aliases_by_offset
                    .with_inserted(key.offset.clone(), spellings)
            };
        }
        if insert {
            self.equality_graph.add_equality(left, right);
        } else if source.is_none() {
            self.rebuild_equality_graph();
        }
    }

    /// Rebuilds all graph fragments from their exact equality indexes. A union-find
    /// cannot forget one equality, so a withdrawal refiles the equalities
    /// that remain: work in the equalities held, not in unrelated facts.
    fn rebuild_equality_graph(&mut self) {
        #[cfg(test)]
        if let Some(graph) = &self.restoring_pointer_graph {
            self.equality_graph = graph.as_ref().clone();
            return;
        }
        self.equality_graph.rebuild_from_inputs();
    }

    fn rebuild_algebraic_graph_equalities(&mut self) {
        self.equality_graph.admitted.algebraic_graph_equalities = Default::default();
        self.rebuild_equality_graph();
        let conditions = self.condition_facts.clone();
        for (condition, value) in conditions.scan_for_upkeep() {
            if matches!(condition, ConditionTerm::AlgebraicEqual(..)) {
                self.adjust_algebraic_graph_equality(
                    &Proposition::ConditionIs(condition.clone(), *value),
                    true,
                );
            }
        }
        let propositions = self.prop_facts.clone();
        for proposition in propositions.scan_for_upkeep() {
            self.adjust_algebraic_graph_equality(proposition, true);
        }
    }

    pub(in crate::kernel) fn designations_equal(&self, left: &Pointer, right: &Pointer) -> bool {
        left == right
            || self
                .equality_graph
                .admitted
                .designation_graph
                .equal(left, right)
            || self.equality_graph.designations_equal(left, right)
            || crate::kernel::memory_provenance::pointer_read_designations_equal(left, right, self)
            || self
                .equality_graph
                .admitted
                .designation_graph
                .unique_direct_alias(right)
                .is_some_and(|alias| {
                    crate::instrumentation::record_deterministic_work(1);
                    crate::kernel::memory_provenance::pointer_read_designations_equal(
                        left, alias, self,
                    )
                })
            || self
                .equality_graph
                .admitted
                .designation_graph
                .unique_direct_alias(left)
                .is_some_and(|alias| {
                    crate::instrumentation::record_deterministic_work(1);
                    crate::kernel::memory_provenance::pointer_read_designations_equal(
                        alias, right, self,
                    )
                })
    }

    pub(in crate::kernel) fn opaque_extents_equal(&self, a: &Pointer, b: &Pointer) -> bool {
        self.equality_graph.admitted.extent_graph.equal(a, b)
            || self.equality_graph.opaque_extents_equal(a, b)
            || crate::kernel::memory_provenance::pointer_read_extents_equal(a, b, self)
            || self
                .equality_graph
                .admitted
                .extent_graph
                .unique_direct_alias(b)
                .is_some_and(|alias| {
                    crate::instrumentation::record_deterministic_work(1);
                    crate::kernel::memory_provenance::pointer_read_extents_equal(a, alias, self)
                })
            || self
                .equality_graph
                .admitted
                .extent_graph
                .unique_direct_alias(a)
                .is_some_and(|alias| {
                    crate::instrumentation::record_deterministic_work(1);
                    crate::kernel::memory_provenance::pointer_read_extents_equal(alias, b, self)
                })
    }

    pub(in crate::kernel) fn access_designations_match(
        &self,
        required: (&Pointer, Option<&Pointer>),
        available: &CMemoryRange,
    ) -> bool {
        self.designations_equal(required.0, &available.designation)
            && required
                .1
                .is_none_or(|extent| match available.opaque_extent.as_deref() {
                    Some(source) => self.opaque_extents_equal(extent, source),
                    None => {
                        available.carrier_extent_known
                            && self.equality_graph.opaque_extent_is_root(extent)
                    }
                })
    }

    pub(in crate::kernel) fn pointer_designations_match(
        &self,
        left: &CPointerValue,
        right: &CPointerValue,
    ) -> bool {
        if self.pointer_designations_match_without_stored_values(left, right) {
            return true;
        }
        // A complete read can carry a pointer copied from a different cell.
        // Compare the producer's entire stored value once; scalar address
        // aliases and partial stores cannot supply its designation or bounds.
        let stored_value = |value: &CPointerValue| {
            // A cast or member selection has already chosen its own view.
            // Recover only the untouched opaque value of a complete read.
            if value.extent_is_known()
                || value.extent().is_some()
                || value.opaque_extent() != Some(value.designation())
            {
                return None;
            }
            crate::kernel::memory_provenance::complete_pointer_read_value(value.designation(), self)
        };
        let stored_left = stored_value(left);
        let stored_right = stored_value(right);
        if stored_left.is_none() && stored_right.is_none() {
            return false;
        }
        self.pointer_designations_match_without_stored_values(
            stored_left.as_ref().unwrap_or(left),
            stored_right.as_ref().unwrap_or(right),
        )
    }

    fn pointer_designations_match_without_stored_values(
        &self,
        left: &CPointerValue,
        right: &CPointerValue,
    ) -> bool {
        // Null is one pointer value, with no allocation or selected object.
        // Establishing its zero address therefore does not transfer authority.
        ((left.is_null() || self.pointers_known_equal(left.pointer(), &Pointer::null()))
            && (right.is_null() || self.pointers_known_equal(right.pointer(), &Pointer::null())))
            || self
                .equality_graph
                .admitted
                .pointer_value_classes
                .equal(left, right)
            || self.equality_graph.knows_condition(
                &ConditionTerm::PointerValueEqual(Box::new(left.clone()), Box::new(right.clone())),
                true,
            )
            || (self.designations_equal(left.designation(), right.designation())
                && match (left.extent(), right.extent()) {
                    (None, None) if left.extent_is_known() && right.extent_is_known() => true,
                    (None, None) if !left.extent_is_known() && !right.extent_is_known() => left
                        .opaque_extent()
                        .zip(right.opaque_extent())
                        .is_some_and(|(a, b)| self.opaque_extents_equal(a, b)),
                    (Some(a), Some(b)) => {
                        a.width == b.width && self.equality_graph.are_equal(&a.start, &b.start)
                    }
                    _ => false,
                })
    }

    pub(in crate::kernel) fn pointer_value_at_entry(&self, value: &CPointerValue) -> CPointerValue {
        if value.extent_is_known() {
            return value.clone();
        }
        let representative = self
            .equality_graph
            .admitted
            .pointer_value_classes
            .representative(value);
        let representative = super::pointer_designations::prefer_pointer(
            &representative,
            &self.equality_graph.pointer_value_representative(value),
        );
        let mut framed_address = None;
        let representative = if !representative.extent_is_known()
            && value.designation().as_loaded_value().is_some()
            && value.opaque_extent() == Some(value.designation())
        {
            self.known_value_of_framed_pointer_read(value)
                .inspect(|known| {
                    framed_address = Some(known.pointer().clone());
                })
                .unwrap_or(representative)
        } else {
            representative
        };
        if !representative.extent_is_known() {
            // Typed loads already return the complete stored pointer when one
            // exists. Normalizing their result must not repeat that history
            // search, including for opaque pointers reconstructed from words.
            // Only full pointer premises above can supply additional bounds.
            return value.clone();
        }
        let adopted = value
            .clone()
            .with_designation(std::sync::Arc::new(representative.designation().clone()))
            .with_extent(representative.extent().cloned())
            .with_opaque_extent(
                representative
                    .opaque_extent()
                    .cloned()
                    .map(std::sync::Arc::new),
            );
        let adopted = match framed_address {
            Some(address) => adopted.with_address(address),
            None => adopted,
        };
        if representative.extent().is_none() {
            adopted.with_root_extent()
        } else {
            adopted
        }
    }

    /// Address aliases select existing full-value premises; only the selected
    /// read's complete eight-byte source can authorize their pointer metadata.
    fn known_value_of_framed_pointer_read(&self, value: &CPointerValue) -> Option<CPointerValue> {
        let source = {
            let _checking =
                crate::instrumentation::CheckingWorkScope::new("select framed pointer source", 1);
            crate::instrumentation::record_deterministic_work(1);
            let alias = self
                .equality_graph
                .unique_exact_pointer_alias(value.pointer())?;
            let address = ConditionTerm::pointer_equal(value.pointer().clone(), alias.clone());
            let sources = self
                .equality_graph
                .admitted
                .pointer_address_sources
                .get(&address)
                .or_else(|| {
                    self.equality_graph
                        .admitted
                        .pointer_address_sources
                        .get(&address.flipped())
                })?;
            // A source bucket can grow with snapshots of this same address. Its
            // cached cardinality decides whether implicit selection is unambiguous.
            if sources.len() != 1 {
                return None;
            }
            sources.iter().next()?
        };
        crate::instrumentation::record_deterministic_work(1);
        let ConditionTerm::PointerValueEqual(left, right) = source else {
            return None;
        };
        for read in [left.as_ref(), right.as_ref()] {
            if read.pointer() != value.pointer()
                || read.extent_is_known()
                || read.extent().is_some()
                || read.opaque_extent() != Some(read.designation())
            {
                continue;
            }
            let representative = self
                .equality_graph
                .admitted
                .pointer_value_classes
                .representative(read);
            let representative = super::pointer_designations::prefer_pointer(
                &representative,
                &self.equality_graph.pointer_value_representative(read),
            );
            if !representative.extent_is_known() {
                continue;
            }
            if crate::kernel::memory_provenance::pointer_read_designations_equal(
                value.designation(),
                read.designation(),
                self,
            ) && crate::kernel::memory_provenance::pointer_read_extents_equal(
                value.designation(),
                read.designation(),
                self,
            ) {
                return Some(representative);
            }
        }
        None
    }

    fn adjust_pointer_value_equality(&mut self, proposition: &Proposition, insert: bool) {
        let (left, right) = match proposition {
            Proposition::Equal(
                Term::CValue(CValue::Pointer(left)),
                Term::CValue(CValue::Pointer(right)),
            ) => (left, right),
            Proposition::ConditionIs(ConditionTerm::PointerValueEqual(left, right), true) => {
                (left.as_ref(), right.as_ref())
            }
            _ => return,
        };
        let key = (left.clone(), right.clone());
        if insert {
            self.equality_graph.admitted.pointer_value_equalities = self
                .equality_graph
                .admitted
                .pointer_value_equalities
                .with_value(key);
            self.equality_graph.admitted.designation_graph.insert(
                left.designation(),
                right.designation(),
                |a, _| a.clone(),
            );
            if left.extent().is_none()
                && right.extent().is_none()
                && !left.extent_is_known()
                && !right.extent_is_known()
                && let Some((a, b)) = left.opaque_extent().zip(right.opaque_extent())
            {
                self.equality_graph
                    .admitted
                    .extent_graph
                    .insert(a, b, |a, _| a.clone());
            }
            self.equality_graph.admitted.pointer_value_classes.insert(
                left,
                right,
                super::pointer_designations::prefer_pointer,
            );
            self.equality_graph.add_pointer_value_equality(left, right);
        } else {
            self.equality_graph.admitted.pointer_value_equalities = self
                .equality_graph
                .admitted
                .pointer_value_equalities
                .without_value(&key);
            self.equality_graph.admitted.designation_graph.remove(
                left.designation(),
                right.designation(),
                |a, _| a.clone(),
            );
            if left.extent().is_none()
                && right.extent().is_none()
                && !left.extent_is_known()
                && !right.extent_is_known()
                && let Some((a, b)) = left.opaque_extent().zip(right.opaque_extent())
            {
                self.equality_graph
                    .admitted
                    .extent_graph
                    .remove(a, b, |a, _| a.clone());
            }
            self.equality_graph.admitted.pointer_value_classes.remove(
                left,
                right,
                super::pointer_designations::prefer_pointer,
            );
            self.rebuild_equality_graph();
        }
    }

    fn adjust_algebraic_graph_equality(&mut self, proposition: &Proposition, insert: bool) {
        let (left, right) = match proposition {
            Proposition::Equal(Term::Algebraic(a), Term::Algebraic(b)) => (a, b),
            Proposition::ConditionIs(ConditionTerm::AlgebraicEqual(a, b), true) => {
                (a.as_ref(), b.as_ref())
            }
            _ => return,
        };
        if left.algebraic_type != right.algebraic_type
            || !left.is_well_formed()
            || !right.is_well_formed()
        {
            return;
        }
        // Retained explicit edges use stable IDs. Deep model keys never enter
        // the persistent graph or its support-count map.
        let atom = |term: &AlgebraicTerm| {
            SharedPureApplication::intern(
                "equality:algebraic-edge".into(),
                vec![PureFunctionArgument::Algebraic(term.clone())],
            )
        };
        let (left_atom, right_atom) = (atom(left), atom(right));
        let edge = if left_atom <= right_atom {
            (left_atom, right_atom)
        } else {
            (right_atom, left_atom)
        };
        let count = self
            .equality_graph
            .admitted
            .algebraic_graph_equalities
            .get(&edge)
            .copied()
            .unwrap_or(0);
        if insert {
            self.equality_graph
                .admitted
                .algebraic_graph_equalities
                .insert(edge, count + 1);
            self.equality_graph.add_algebraic_equality(left, right);
        } else if count > 1 {
            self.equality_graph
                .admitted
                .algebraic_graph_equalities
                .insert(edge, count - 1);
        } else {
            self.equality_graph
                .admitted
                .algebraic_graph_equalities
                .remove(&edge);
            self.rebuild_equality_graph();
        }
    }

    fn adjust_uint64_graph_equality(
        &mut self,
        condition: &ConditionTerm,
        value: bool,
        insert: bool,
    ) {
        let (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left,
                right,
            },
            true,
        ) = (condition, value)
        else {
            return;
        };
        let edge = if insert {
            let edge = (
                super::equality_graph::MachineAtom::uint64(crate::kernel::canonical_term(left)),
                super::equality_graph::MachineAtom::uint64(crate::kernel::canonical_term(right)),
            );
            self.equality_graph
                .admitted
                .uint64_input_edges
                .insert(condition.clone(), edge.clone());
            edge
        } else {
            let Some(edge) = self
                .equality_graph
                .admitted
                .uint64_input_edges
                .get(condition)
                .cloned()
            else {
                return;
            };
            self.equality_graph
                .admitted
                .uint64_input_edges
                .remove(condition);
            edge
        };
        let count = self
            .equality_graph
            .admitted
            .uint64_graph_equalities
            .get(&edge)
            .copied()
            .unwrap_or(0);
        if insert {
            self.equality_graph
                .admitted
                .uint64_graph_equalities
                .insert(edge, count + 1);
            self.equality_graph.add_uint64_equality(left, right);
        } else if count > 1 {
            self.equality_graph
                .admitted
                .uint64_graph_equalities
                .insert(edge, count - 1);
        } else {
            self.equality_graph
                .admitted
                .uint64_graph_equalities
                .remove(&edge);
            self.rebuild_equality_graph();
        }
    }

    pub(in crate::kernel) fn uint64_values_known_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        self.equality_graph.are_uint64_equal(left, right)
    }

    fn adjust_int32_graph_equality(
        &mut self,
        condition: &ConditionTerm,
        value: bool,
        insert: bool,
    ) {
        if !value {
            return;
        }
        // Preserve the same exact-premise translation as the legacy scalar
        // equality index. Equal byte offsets imply equal int32 element-index
        // residues only when both offsets admit that checked interpretation.
        let derived;
        let (left, right) = match condition {
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            } => (left.as_ref(), right.as_ref()),
            condition if condition.true_pointer_offset_sides().is_some() => {
                let (left, right) = condition.true_pointer_offset_sides().expect("offset view");
                let Some(pair) = int32_element_index_from_offset(left)
                    .zip(int32_element_index_from_offset(right))
                else {
                    return;
                };
                derived = pair;
                (&derived.0, &derived.1)
            }
            _ => return,
        };
        // Count exact premises under the canonical edge rather than interning
        // raw MemoryLoad payloads. Raw interning can compare whole snapshots
        // across verification arenas. Counts preserve independent spellings
        // that canonicalize to the same edge when one premise is withdrawn.
        let edge = if insert {
            let edge = (
                super::equality_graph::MachineAtom::int32(crate::kernel::canonical_term(left)),
                super::equality_graph::MachineAtom::int32(crate::kernel::canonical_term(right)),
            );
            self.equality_graph
                .admitted
                .int32_input_edges
                .insert(condition.clone(), edge.clone());
            edge
        } else {
            let Some(edge) = self
                .equality_graph
                .admitted
                .int32_input_edges
                .get(condition)
                .cloned()
            else {
                return;
            };
            self.equality_graph
                .admitted
                .int32_input_edges
                .remove(condition);
            edge
        };
        let count = self
            .equality_graph
            .admitted
            .int32_graph_equalities
            .get(&edge)
            .copied()
            .unwrap_or(0);
        if insert {
            self.equality_graph
                .admitted
                .int32_graph_equalities
                .insert(edge, count + 1);
            self.equality_graph.add_int32_equality(left, right);
        } else if count > 1 {
            self.equality_graph
                .admitted
                .int32_graph_equalities
                .insert(edge, count - 1);
        } else {
            self.equality_graph
                .admitted
                .int32_graph_equalities
                .remove(&edge);
            self.rebuild_equality_graph();
        }
    }

    /// Diagnostic-only access to already admitted read equalities.
    pub(crate) fn read_equality_checkpoint(&self) -> crate::kernel::ReadEqualityCheckpoint {
        self.equality_graph.read_equality_checkpoint()
    }

    pub(crate) fn read_equalities_since(
        &self,
        checkpoint: &crate::kernel::ReadEqualityCheckpoint,
    ) -> crate::kernel::ReadEqualityDelta {
        self.equality_graph.read_equalities_since(checkpoint)
    }

    /// File the typed producer's checked value against an exact defining
    /// equation already admitted on this path. Plain propositions cannot
    /// create this bridge; the execution fact must carry producer metadata.
    pub(in crate::kernel) fn assume_execution_pure_fact(
        mut self,
        fact: &ExecutionPureFact,
    ) -> Self {
        self = self.assume_proposition(fact.proposition().clone());
        if !fact.is_certified() {
            return self;
        }
        let Some(
            binding @ GeneratedLoadBinding::Exact {
                variable,
                pointer: address,
                load: Bitvector32Term::MemoryLoad(memory, _, kind),
                typed_pointer_value: Some(value),
                ..
            },
        ) = fact.generated_load_binding()
        else {
            return self;
        };
        if Some(*kind) != LoadKind::of_type(CType::Int32Pointer)
            || crate::kernel::registered_load_bytes_for_variable(variable)
                != Some(C_POINTER_BYTE_WIDTH)
            || !generated_load_binding_matches_proposition(binding, fact.proposition())
            || crate::kernel::eval::typed_pointer_read_variable(value) != Some(*variable)
        {
            return self;
        }
        let condition = ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(Bitvector32Term::Variable(*variable)),
            right: Box::new(Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(address.clone()),
                *kind,
            )),
        };
        if self.condition_facts.get(&condition) != Some(&true) {
            return self;
        }
        self.file_typed_pointer_read(*variable, memory, address, value);
        self
    }

    /// Select one unambiguous certified program read retained in this
    /// context. Its immutable pair comes from the retained binding, not the
    /// live naming registry. No definition is published to sibling contexts.
    pub(in crate::kernel) fn retained_pointer_read_application(
        &self,
        value: &Pointer,
    ) -> Option<Pointer> {
        let variable = crate::kernel::eval::typed_pointer_read_variable(value)?;
        let definitions = self
            .equality_graph
            .admitted
            .typed_pointer_read_definitions
            .get(&variable)?;
        if definitions.len() != 1 {
            return None;
        }
        let ((_, address), (retained, source)) = definitions.iter().next()?;
        (retained == value).then(|| Pointer::loaded_value(source, address))
    }

    /// Publish a typed read's definition and locally checked source equality.
    /// The graph is part of the trusted kernel. One exact materialization or
    /// separate store edge is checked here;
    /// equality queries never search history.
    /// No proposition or read authority is introduced. Checked unions belong
    /// only to this persistent proof context; definitions are unconditional.
    pub(in crate::kernel) fn register_pointer_read(
        &self,
        value: &Pointer,
        memory: &SharedCMemory,
        address: &Pointer,
    ) {
        self.equality_graph
            .register_pointer_read_definition(value, memory, address);
        self.register_pointer_read_source(memory, address);
    }

    /// Reconcile a retained, checked pointer read with a cached alias value.
    /// Only spellings in its checked address class are queried in this exact
    /// snapshot. Logical term construction does not perform this cell search.
    pub(in crate::kernel) fn register_checked_pointer_read(
        &self,
        value: &Pointer,
        memory: &SharedCMemory,
        address: &Pointer,
    ) {
        self.register_pointer_read(value, memory, address);
        self.register_cached_pointer_read_value(memory, address);
    }

    fn register_cached_pointer_read_value(&self, memory: &SharedCMemory, address: &Pointer) {
        let start = crate::kernel::prelude::canonical_load_projection_source(memory, address)
            .unwrap_or_else(|| memory.clone());
        for spelling in self.equality_graph.pointer_spellings(address) {
            if let Some(CValue::Pointer(value)) = start.known_value(&spelling) {
                self.equality_graph.add_checked_pointer_value_equality(
                    &CPointerValue::new(Pointer::loaded_value(memory, address), value.c_type()),
                    &value,
                );
                return;
            }
        }
    }

    /// This rule relates load applications only. An execution value's bridge
    /// remains scoped to its certified binding, including restricted contexts.
    fn register_pointer_read_source(&self, memory: &SharedCMemory, address: &Pointer) {
        if let Some(source) = self.pointer_read_source(memory, address) {
            self.equality_graph.add_checked_pointer_read_equality(
                &Pointer::loaded_value(memory, address),
                &Pointer::loaded_value(&source, address),
            );
        }
    }

    pub(in crate::kernel) fn pointer_read_source(
        &self,
        memory: &SharedCMemory,
        address: &Pointer,
    ) -> Option<SharedCMemory> {
        // This producer names an LP64 pointer read, whose width is known
        // even when no scalar load was recorded at the same address.
        let bytes = crate::kernel::C_POINTER_BYTE_WIDTH;
        let start = crate::kernel::prelude::canonical_load_projection_source(memory, address)
            .unwrap_or_else(|| memory.clone());
        let derivation = start.derivation()?;
        match derivation.as_ref() {
            CMemoryDerivation::CellsSeeded { run, .. } => run.read_source(address, bytes),
            CMemoryDerivation::Store {
                base,
                pointer: write,
                value,
            } => {
                // Select over exactly one store. Align to its explicitly
                // named block using established graph equality, then check
                // complete byte separation, or use the selected ownership
                // composition's two disjoint complete cells. This checks one
                // store edge; it never searches older snapshots.
                let read = if write.blocks_proven_distinct(address) {
                    Some(address.clone())
                } else {
                    self.equality_graph.pointer_in_block(address, &write.block)
                };
                let separate = read.is_some_and(|read| {
                    crate::kernel::reasoning::exact_access_byte_overlap(
                        write,
                        value.byte_width(),
                        &read,
                        bytes,
                    ) == Some(crate::kernel::reasoning::AccessByteOverlap::Separate)
                })
                    || crate::kernel::memory_provenance::indexed_store_byte_separation_evidence(
                        write,
                        value.byte_width(),
                        address,
                        bytes,
                        self,
                    )
                    .is_some();
                separate.then(|| base.clone())
            }
            _ => None,
        }
    }

    fn file_typed_pointer_read(
        &mut self,
        variable: Variable,
        memory: &SharedCMemory,
        address: &Pointer,
        value: &Pointer,
    ) {
        let key = (memory.arena_id(), address.clone());
        let definitions = self
            .equality_graph
            .admitted
            .typed_pointer_read_definitions
            .get(&variable)
            .cloned()
            .unwrap_or_default();
        if definitions.contains_key(&key) {
            return;
        }
        let definitions = definitions.with_inserted(key.clone(), (value.clone(), memory.clone()));
        self.equality_graph.admitted.typed_pointer_read_definitions = self
            .equality_graph
            .admitted
            .typed_pointer_read_definitions
            .with_inserted(variable, definitions);
        self.content_fingerprint ^= Self::typed_pointer_read_fingerprint(variable, &key, value);
        self.equality_graph
            .add_equality(value, &Pointer::loaded_value(memory, address));
        self.register_pointer_read_source(memory, address);
        self.register_cached_pointer_read_value(memory, address);
    }

    fn typed_pointer_read_fingerprint(
        variable: Variable,
        key: &((u32, u32), Pointer),
        value: &Pointer,
    ) -> u64 {
        Self::fingerprint(4, &(variable, key, value))
    }

    #[cfg(test)]
    fn withdraw_typed_pointer_read_definition(&mut self, condition: &ConditionTerm, value: bool) {
        if !value {
            return;
        }
        let ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        } = condition
        else {
            return;
        };
        let definition = match (left.as_ref(), right.as_ref()) {
            (
                Bitvector32Term::Variable(variable),
                Bitvector32Term::MemoryLoad(memory, address, _),
            )
            | (
                Bitvector32Term::MemoryLoad(memory, address, _),
                Bitvector32Term::Variable(variable),
            ) => (*variable, memory, address.as_ref()),
            _ => return,
        };
        let (variable, memory, address) = definition;
        let key = (memory.arena_id(), address.clone());
        let definitions = self
            .equality_graph
            .admitted
            .typed_pointer_read_definitions
            .get(&variable)
            .cloned()
            .unwrap_or_default();
        if !definitions.contains_key(&key) {
            return;
        }
        let pointer_value = &definitions.get(&key).expect("checked above").0;
        self.content_fingerprint ^=
            Self::typed_pointer_read_fingerprint(variable, &key, pointer_value);
        let definitions = definitions.without_key(&key);
        self.equality_graph.admitted.typed_pointer_read_definitions = if definitions.is_empty() {
            self.equality_graph
                .admitted
                .typed_pointer_read_definitions
                .without_key(&variable)
        } else {
            self.equality_graph
                .admitted
                .typed_pointer_read_definitions
                .with_inserted(variable, definitions)
        };
        self.rebuild_equality_graph();
    }

    fn adjust_pointer_offset_alias(
        &mut self,
        condition: &ConditionTerm,
        value: bool,
        insert: bool,
    ) {
        let (left, right) = match condition {
            ConditionTerm::PointerOffsetEqual(left, right) => (left.as_ref(), right.as_ref()),
            ConditionTerm::PointerValueEqual(left, right) if left.block == right.block => {
                (&left.offset, &right.offset)
            }
            _ => return,
        };
        if !value || left == right {
            return;
        }
        let key = if left < right {
            ConditionTerm::PointerOffsetEqual(Box::new(left.clone()), Box::new(right.clone()))
        } else {
            ConditionTerm::PointerOffsetEqual(Box::new(right.clone()), Box::new(left.clone()))
        };
        let source = self.adjust_pointer_address_source(key, condition, insert);
        let retained = source.is_some();
        for (key, alias) in [(left, right), (right, left)] {
            let aliases = self
                .equality_graph
                .admitted
                .pointer_offset_aliases
                .get(key)
                .cloned()
                .unwrap_or_default();
            let aliases = if retained {
                aliases.with_value(alias.clone())
            } else {
                aliases.without_value(alias)
            };
            let root = crate::kernel::primitives::offset_root_atom(alias);
            let rooted = self
                .equality_graph
                .admitted
                .pointer_offset_aliases_by_root
                .get(&root)
                .cloned()
                .unwrap_or_default();
            let pair = (key.clone(), alias.clone());
            let rooted = if retained {
                rooted.with_value(pair)
            } else {
                rooted.without_value(&pair)
            };
            self.equality_graph.admitted.pointer_offset_aliases_by_root = if rooted.is_empty() {
                self.equality_graph
                    .admitted
                    .pointer_offset_aliases_by_root
                    .without_key(&root)
            } else {
                self.equality_graph
                    .admitted
                    .pointer_offset_aliases_by_root
                    .with_inserted(root, rooted)
            };
            self.equality_graph.admitted.pointer_offset_aliases = if aliases.is_empty() {
                self.equality_graph
                    .admitted
                    .pointer_offset_aliases
                    .without_key(key)
            } else {
                self.equality_graph
                    .admitted
                    .pointer_offset_aliases
                    .with_inserted(key.clone(), aliases)
            };
        }
        if insert {
            self.equality_graph.add_offset_equality(left, right);
        } else if !retained {
            self.rebuild_equality_graph();
        }
    }

    /// The offsets with a same-block exact alias whose root atom is `root`
    /// (`resource_algebra::offset_root_atom`): by symmetry of the stated
    /// equalities, the bases one hop from an address at that root. Keyed by
    /// the root, so the answer costs the equalities naming it.
    pub(in crate::kernel) fn offsets_with_an_alias_at_root(
        &self,
        root: &Option<PointerOffsetTerm>,
    ) -> Vec<PointerOffsetTerm> {
        self.equality_graph.offsets_with_an_alias_at_root(root)
    }

    /// Whether any exact equality joins two blocks.
    pub(in crate::kernel) fn has_pointer_block_aliases(&self) -> bool {
        self.equality_graph.has_pointer_block_aliases()
    }

    pub(crate) fn exact_pointer_offset_aliases(
        &self,
        pointer: &Pointer,
    ) -> impl Iterator<Item = Pointer> + '_ {
        self.equality_graph.exact_pointer_offset_aliases(pointer)
    }

    pub(in crate::kernel) fn exact_pointer_offset_alias_count(&self, pointer: &Pointer) -> usize {
        self.equality_graph
            .exact_pointer_offset_alias_count(pointer)
    }

    /// Re-express one selected address using checked graph equality to a
    /// supplied base. This proposes a spelling, not separation authority;
    /// consumers recheck the full pointer equality and complete byte ranges.
    /// `pointer` spelled in `block` when they are one block or one affine
    /// class of the graph. The shallow half of
    /// [`crate::kernel::reasoning::pointer_in_block_for_memory_resolution`]:
    /// no snapshot comparison. It locates an address and grants no access.
    pub(in crate::kernel) fn pointer_in_block(
        &self,
        pointer: &Pointer,
        block: &PointerBlock,
    ) -> Option<Pointer> {
        if pointer.block == *block {
            return Some(pointer.clone());
        }
        self.equality_graph.pointer_in_block(pointer, block)
    }

    pub(in crate::kernel) fn pointer_at_known_base(
        &self,
        pointer: &Pointer,
        base: &Pointer,
    ) -> Option<Pointer> {
        self.equality_graph.pointer_at_base(pointer, base)
    }

    /// Retain the supplying native index while aligning one selected address.
    /// The spelling supplies no range bounds or access authority.
    pub(in crate::kernel) fn pointer_at_known_base_with_wide_index(
        &self,
        pointer: &Pointer,
        base: &Pointer,
    ) -> Option<Pointer> {
        self.equality_graph
            .pointer_at_base_with_wide_index(pointer, base)
    }

    /// Re-express a selected field only when the maintained affine classes
    /// give a constant byte displacement. This does not expand producer
    /// expressions or retry symbolic range-bound reasoning.
    pub(in crate::kernel) fn pointer_at_known_constant_base(
        &self,
        pointer: &Pointer,
        base: &Pointer,
    ) -> Option<Pointer> {
        fn constant_spine(pointer: &Pointer) -> Option<(Pointer, i64)> {
            let mut offset = &pointer.offset;
            let mut bytes = 0i64;
            while let PointerOffsetTerm::Add(left, right) = offset {
                crate::instrumentation::record_deterministic_work(1);
                let (rest, extra) = match (left.as_ref(), right.as_ref()) {
                    (rest, PointerOffsetTerm::Constant(extra))
                    | (PointerOffsetTerm::Constant(extra), rest) => (rest, extra),
                    _ => break,
                };
                bytes = bytes.checked_add(*extra)?;
                offset = rest;
            }
            // A wholly constant offset is its block's origin displaced by
            // it, as `parent->right` is `parent` plus the field's offset.
            if let PointerOffsetTerm::Constant(extra) = offset {
                return Some((
                    Pointer {
                        block: pointer.block.clone(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    bytes.checked_add(*extra)?,
                ));
            }
            Some((
                Pointer {
                    block: pointer.block.clone(),
                    offset: offset.clone(),
                },
                bytes,
            ))
        }
        let (origin, displacement) = constant_spine(pointer)?;
        let (base_origin, base_displacement) = constant_spine(base)?;
        // For residual symbolic arithmetic, consult only recorded affine
        // coordinates. Term registration here would revisit array-index
        // dependencies after the direct membership check already failed.
        if matches!(origin.offset, PointerOffsetTerm::Add(..))
            || matches!(base_origin.offset, PointerOffsetTerm::Add(..))
        {
            return self.equality_graph.pointer_at_constant_base(pointer, base);
        }
        if self.equality_graph.are_equal(&origin, &base_origin) {
            return Some(Pointer {
                block: base.block.clone(),
                offset: PointerOffsetTerm::add(
                    base.offset.clone(),
                    PointerOffsetTerm::Constant(displacement.checked_sub(base_displacement)?),
                ),
            });
        }
        self.equality_graph.pointer_at_constant_base(pointer, base)
    }

    /// The pointers an exact fact proves equal to this one, in the index's
    /// own order. One hop: an alias of an alias is not reported, so the
    /// answer is bounded by the equalities stated about this pointer and no
    /// query walks an equality graph.
    /// The pointers with at least one exact alias, in pointer order.
    pub(crate) fn exactly_aliased_pointers(&self) -> impl ExactSizeIterator<Item = &Pointer> {
        self.equality_graph.exactly_aliased_pointers()
    }

    pub(crate) fn exact_pointer_aliases(
        &self,
        pointer: &Pointer,
    ) -> impl Iterator<Item = &Pointer> {
        self.equality_graph.exact_pointer_aliases(pointer)
    }

    /// The pointers a chain of recorded cross-block equalities joins to
    /// `pointer`. Address-only equalities are edges too, so this proposes
    /// candidates and grants nothing; consumers recheck full equality.
    pub(in crate::kernel) fn pointer_alias_class(&self, pointer: &Pointer) -> Vec<Pointer> {
        self.equality_graph.pointer_alias_class(pointer)
    }

    pub(super) fn rebuild_null_pointer_offsets(&mut self) {
        self.null_pointer_offsets = crate::persistent::PersistentMap::default();
        let facts = self
            .condition_facts
            .scan_for_upkeep()
            .map(|(condition, value)| (condition.clone(), *value))
            .collect::<Vec<_>>();
        for (condition, value) in facts {
            self.adjust_null_pointer_offset(&condition, value, true);
        }
    }

    pub(super) fn separated_anchor_key(
        left: PointerOffsetTerm,
        right: PointerOffsetTerm,
    ) -> (PointerOffsetTerm, PointerOffsetTerm) {
        if left <= right {
            (left, right)
        } else {
            (right, left)
        }
    }

    pub(super) fn separated_pointer_key(left: Pointer, right: Pointer) -> (Pointer, Pointer) {
        if left <= right {
            (left, right)
        } else {
            (right, left)
        }
    }

    /// Index one stated separation by its nonempty anchors. Common-block
    /// anchors also distinguish offsets; different blocks distinguish only
    /// complete pointers. Updates touch just this fact's selected key.
    fn adjust_separated_anchor_offsets(
        &mut self,
        proposition: &Proposition,
        left: &CMemoryRange,
        right: &CMemoryRange,
        insert: bool,
    ) {
        let (Some(left_anchor), Some(right_anchor)) =
            (memory_range_anchor(left), memory_range_anchor(right))
        else {
            return;
        };
        if left.base().block != right.base().block {
            let key = Self::separated_pointer_key(
                Pointer {
                    block: left.base().block.clone(),
                    offset: left_anchor,
                },
                Pointer {
                    block: right.base().block.clone(),
                    offset: right_anchor,
                },
            );
            let facts = self
                .separated_anchor_pointers
                .get(&key)
                .cloned()
                .unwrap_or_default();
            let facts = if insert {
                facts.with_value(proposition.clone())
            } else {
                facts.without_value(proposition)
            };
            self.separated_anchor_pointers = if facts.is_empty() {
                self.separated_anchor_pointers.without_key(&key)
            } else {
                self.separated_anchor_pointers.with_inserted(key, facts)
            };
            return;
        }
        let key = Self::separated_anchor_key(left_anchor, right_anchor);
        let facts = self
            .separated_anchor_offsets
            .get(&key)
            .cloned()
            .unwrap_or_default();
        let facts = if insert {
            facts.with_value(proposition.clone())
        } else {
            facts.without_value(proposition)
        };
        self.separated_anchor_offsets = if facts.is_empty() {
            self.separated_anchor_offsets.without_key(&key)
        } else {
            self.separated_anchor_offsets.with_inserted(key, facts)
        };
    }

    /// Rebuilds the anchor separation index from the stated memory
    /// separations it mirrors.
    #[cfg(test)]
    pub(super) fn rebuild_separated_anchor_offsets(&mut self) {
        self.separated_anchor_offsets = crate::persistent::PersistentMap::default();
        self.separated_anchor_pointers = crate::persistent::PersistentMap::default();
        let stated = self
            .prop_facts
            .iter()
            .filter_map(|proposition| {
                Self::proposition_memory_separation(proposition)
                    .map(|(left, right)| (proposition.clone(), left, right))
            })
            .collect::<Vec<_>>();
        for (proposition, left, right) in stated {
            self.adjust_separated_anchor_offsets(&proposition, &left, &right, true);
        }
    }

    pub(super) fn rebuild_signed_order_bounds(&mut self) {
        self.checked_order_bounds = Default::default();
        self.order_facts_by_lower = OrderFactsByLower::default();
        self.signed_order_bounds = crate::persistent::PersistentMap::default();
        self.int64_signed_order_bounds = crate::persistent::PersistentMap::default();
        self.uint32_order_bounds = crate::persistent::PersistentMap::default();
        self.uint64_order_bounds = crate::persistent::PersistentMap::default();
        self.wide_order_edges = Default::default();
        let facts = self
            .condition_facts
            .scan_for_upkeep()
            .map(|(condition, value)| (condition.clone(), *value))
            .collect::<Vec<_>>();
        for (condition, value) in facts {
            self.adjust_signed_order_bound(&condition, value, true);
        }
    }

    pub(super) fn rebuild_memory_load_condition_facts(&mut self) {
        self.memory_load_condition_facts = crate::persistent::PersistentMap::default();
        let conditions = self
            .condition_facts
            .scan_for_upkeep()
            .map(|(key, _)| key)
            .cloned()
            .collect::<Vec<_>>();
        for condition in conditions {
            self.adjust_memory_load_condition_index(&condition, true);
        }
        self.equality_graph.admitted.scalar_evidence_inputs = Default::default();
        self.equality_graph.admitted.scalar_dependency_inputs = Default::default();
        self.equality_graph.admitted.scalar_dependencies = Default::default();
        self.equality_graph.admitted.scalar_deferred_inputs = 0;
        self.equality_graph.admitted.scalar_evidence_keys = Default::default();
        self.equality_graph.admitted.bitvector64_equality_facts =
            crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.wide_load_sources = Default::default();
        self.equality_graph
            .admitted
            .wide_pointer_alias_endpoints_by_object = crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.exact_constant_equalities =
            crate::persistent::PersistentMap::default();
        let conditions = self.condition_facts.clone();
        for (condition, value) in conditions.scan_for_upkeep() {
            self.adjust_scalar_evidence_input(condition, *value, true);
            self.adjust_bitvector64_equality(condition, *value, true);
            self.adjust_exact_constant_equality(condition, *value, true);
        }
    }

    /// Rebuilds the condition-match indexes from `condition_facts`, for a
    /// context whose condition facts were replaced wholesale.
    ///
    /// The exact pointer-alias indexes are derived from the same facts and
    /// are rebuilt with them: a restricted context must not answer an alias
    /// query from an equality it no longer holds.
    fn rebuild_condition_match_indexes(&mut self) {
        self.equality_graph.admitted.scalar_evidence_inputs = Default::default();
        self.equality_graph.admitted.scalar_dependency_inputs = Default::default();
        self.equality_graph.admitted.scalar_dependencies = Default::default();
        self.equality_graph.admitted.scalar_deferred_inputs = 0;
        self.equality_graph.admitted.scalar_evidence_keys = Default::default();
        let prior_typed_reads = self
            .equality_graph
            .admitted
            .typed_pointer_read_definitions
            .clone();
        self.checked_scalar_facts = Default::default();
        self.condition_facts_by_sides = crate::persistent::PersistentMap::default();
        self.bool_equation_partners = crate::persistent::PersistentMap::default();
        self.pointer_offset_equalities_by_shape = crate::persistent::PersistentMap::default();
        self.condition_facts_by_variable = crate::persistent::PersistentMap::default();
        self.snapshot_condition_variable_base = crate::persistent::PersistentMap::default();
        self.snapshot_condition_variable_changes = crate::persistent::PersistentMap::default();
        self.snapshot_condition_variables = std::sync::Arc::new(std::sync::OnceLock::new());
        self.open_condition_facts = crate::persistent::PersistentMap::default();
        self.order_condition_facts = Default::default();
        self.difference_graph.reset();
        self.contradictions.reset();
        self.equality_graph.admitted.pointer_alignment_facts =
            crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.pointer_block_aliases =
            crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.pointer_block_aliases_by_offset =
            crate::persistent::PersistentMap::default();
        self.equality_graph
            .admitted
            .pointer_alias_endpoints_by_object = crate::persistent::PersistentMap::default();
        self.equality_graph.clear_condition_pointer_facts();
        self.equality_graph.reset_closure();
        self.equality_graph.admitted.algebraic_graph_equalities = Default::default();
        self.equality_graph.admitted.congruence_conditions =
            crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.int32_graph_equalities =
            crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.int32_input_edges = Default::default();
        self.equality_graph.admitted.uint64_graph_equalities =
            crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.uint64_input_edges = Default::default();
        self.equality_graph.admitted.typed_pointer_read_definitions =
            crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.pointer_offset_aliases =
            crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.pointer_offset_aliases_by_root =
            crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.pointer_address_sources = Default::default();
        self.equality_graph.admitted.designation_graph = Default::default();
        self.equality_graph.admitted.extent_graph = Default::default();
        self.equality_graph.admitted.pointer_value_classes = Default::default();
        self.equality_graph.admitted.pointer_value_equalities = Default::default();
        let conditions = self.condition_facts.clone();
        for (condition, value) in conditions.scan_for_upkeep() {
            self.adjust_pointer_class_fact(
                &Proposition::ConditionIs(condition.clone(), *value),
                true,
            );
            if matches!(condition, ConditionTerm::PointerValueEqual(..)) {
                self.adjust_pointer_value_equality(
                    &Proposition::ConditionIs(condition.clone(), *value),
                    true,
                );
            }
            self.adjust_scalar_evidence_input(condition, *value, true);
            self.adjust_condition_variable_index(condition, *value, true, false);
            self.adjust_condition_side_indexes(condition, *value, true);
            self.adjust_pointer_block_alias(condition, *value, true);
            self.adjust_pointer_offset_alias(condition, *value, true);
            self.adjust_int32_graph_equality(condition, *value, true);
            self.adjust_uint64_graph_equality(condition, *value, true);
            self.adjust_algebraic_graph_equality(
                &Proposition::ConditionIs(condition.clone(), *value),
                true,
            );
            if self.equality_graph.add_condition(condition, *value) {
                self.equality_graph
                    .admitted
                    .congruence_conditions
                    .insert(condition.clone(), *value);
            }
        }
        // Restore typing support by the selected equations' load variables,
        // rather than walking every pointer read in the ambient context.
        for (condition, value) in conditions.scan_for_upkeep() {
            if !*value {
                continue;
            }
            let ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            } = condition
            else {
                continue;
            };
            let (Bitvector32Term::Variable(variable), Bitvector32Term::MemoryLoad(_, _, _)) =
                (left.as_ref(), right.as_ref())
            else {
                continue;
            };
            let Some(kind) = crate::kernel::registered_load_kind_for_variable(variable) else {
                continue;
            };
            if let Some(definitions) = prior_typed_reads.get(variable) {
                for ((_, address), (pointer_value, memory)) in definitions.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    let definition = ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(Bitvector32Term::Variable(*variable)),
                        right: Box::new(Bitvector32Term::MemoryLoad(
                            memory.clone(),
                            Box::new(address.clone()),
                            kind,
                        )),
                    };
                    if self.condition_facts.get(&definition) == Some(&true) {
                        self.file_typed_pointer_read(*variable, memory, address, pointer_value);
                    }
                }
            }
        }
        // The scalar and condition model fragments above already describe
        // the selected context. Add its proposition model edges directly;
        // do not reconstruct those fragments a second time.
        let propositions = self.prop_facts.clone();
        for proposition in propositions.scan_for_upkeep() {
            self.adjust_algebraic_graph_equality(proposition, true);
            self.adjust_pointer_class_fact(proposition, true);
            self.adjust_pointer_value_equality(proposition, true);
        }
    }

    /// Files or withdraws one condition fact under its match key and, when
    /// a side is not an atom, among the open facts of its family.
    fn adjust_condition_match_indexes(
        &mut self,
        condition: &ConditionTerm,
        value: bool,
        insert: bool,
    ) {
        if matches!(condition, ConditionTerm::PointerValueEqual(..)) {
            self.adjust_pointer_value_equality(
                &Proposition::ConditionIs(condition.clone(), value),
                insert,
            );
        }
        let proposition = Proposition::ConditionIs(condition.clone(), value);
        if !insert {
            self.adjust_atomic_connection_fact(&proposition, false);
        }
        self.adjust_condition_variable_index(condition, value, insert, true);
        self.adjust_condition_side_indexes(condition, value, insert);
        if insert {
            self.adjust_atomic_connection_fact(&proposition, true);
        }
    }

    fn adjust_condition_variable_index(
        &mut self,
        condition: &ConditionTerm,
        value: bool,
        insert: bool,
        entry_charged: bool,
    ) {
        let _index_timing =
            crate::instrumentation::OperationTiming::new("", "", "condition variable indexing");
        // assume_condition charges one unit for filing the context entry,
        // including its first adjacency. A restriction rebuild has no such
        // entry charge. Account for additional variables separately so a
        // wide condition remains charged in proportion to its syntax.
        if !entry_charged {
            crate::instrumentation::record_deterministic_work(1);
        }
        let mut variables = BTreeSet::new();
        let deferred = super::reasoning::variable_collection::collect_condition_index_variables(
            condition,
            &mut variables,
        );
        if deferred {
            // Extend the last completed index by a deferred delta. Adding a
            // new snapshot fact must not re-index older snapshot facts.
            if let Some(index) = self.snapshot_condition_variables.get() {
                self.snapshot_condition_variable_base = index.clone();
                self.snapshot_condition_variable_changes =
                    crate::persistent::PersistentMap::default();
            }
            self.snapshot_condition_variable_changes = self
                .snapshot_condition_variable_changes
                .with_inserted(condition.clone(), insert.then_some(value));
            self.snapshot_condition_variables = std::sync::Arc::new(std::sync::OnceLock::new());
        } else {
            crate::instrumentation::record_deterministic_work(variables.len().saturating_sub(1));
            let indexed = SharedIndexFact::new(condition.clone());
            for variable in variables {
                let facts = self
                    .condition_facts_by_variable
                    .get(&variable)
                    .cloned()
                    .unwrap_or_default();
                let facts = if insert {
                    facts.with_inserted(indexed.clone(), value)
                } else {
                    facts.without_key(&indexed)
                };
                self.condition_facts_by_variable = if facts.is_empty() {
                    self.condition_facts_by_variable.without_key(&variable)
                } else {
                    self.condition_facts_by_variable
                        .with_inserted(variable, facts)
                };
            }
        }
    }

    fn adjust_condition_side_indexes(
        &mut self,
        condition: &ConditionTerm,
        value: bool,
        insert: bool,
    ) {
        if insert {
            self.difference_graph.assume(condition, value);
        } else {
            self.difference_graph.withdraw(condition);
        }
        self.checked_scalar_facts.adjust(condition, value, insert);
        self.contradictions.adjust(condition, value, insert);
        if let (ConditionTerm::PointerOffsetEqual(left, right), true) = (condition, value) {
            for shape in [offset_snapshot_shape(left), offset_snapshot_shape(right)] {
                let filed = self
                    .pointer_offset_equalities_by_shape
                    .get(&shape)
                    .cloned()
                    .unwrap_or_default();
                let filed = if insert {
                    filed.with_value(condition.clone())
                } else {
                    filed.without_value(condition)
                };
                self.pointer_offset_equalities_by_shape = if filed.is_empty() {
                    self.pointer_offset_equalities_by_shape.without_key(&shape)
                } else {
                    self.pointer_offset_equalities_by_shape
                        .with_inserted(shape, filed)
                };
            }
        }
        if let ConditionTerm::BoolEqual(left, right) = condition {
            for (operand, partner) in [(left, right), (right, left)] {
                let partners = self
                    .bool_equation_partners
                    .get(operand.as_ref())
                    .cloned()
                    .unwrap_or_default();
                let partners = if insert {
                    partners.with_inserted(partner.as_ref().clone(), value)
                } else {
                    partners.without_key(partner.as_ref())
                };
                self.bool_equation_partners = if partners.is_empty() {
                    self.bool_equation_partners.without_key(operand.as_ref())
                } else {
                    self.bool_equation_partners
                        .with_inserted(operand.as_ref().clone(), partners)
                };
            }
        }
        if condition_as_order_fact(condition, value).is_some() {
            self.order_condition_facts = if insert {
                self.order_condition_facts
                    .with_inserted(condition.clone(), value)
            } else {
                self.order_condition_facts.without_key(condition)
            };
        }
        if let Some(key) = condition_match_key(condition) {
            let family = key.family();
            let facts = self
                .condition_facts_by_sides
                .get(&key)
                .cloned()
                .unwrap_or_default();
            let facts = if insert {
                facts.with_inserted(condition.clone(), value)
            } else {
                facts.without_key(condition)
            };
            self.condition_facts_by_sides = if facts.is_empty() {
                self.condition_facts_by_sides.without_key(&key)
            } else {
                self.condition_facts_by_sides.with_inserted(key, facts)
            };
            if condition_has_an_open_side(condition) {
                let facts = self
                    .open_condition_facts
                    .get(&family)
                    .cloned()
                    .unwrap_or_default();
                let facts = if insert {
                    facts.with_inserted(condition.clone(), value)
                } else {
                    facts.without_key(condition)
                };
                self.open_condition_facts = if facts.is_empty() {
                    self.open_condition_facts.without_key(&family)
                } else {
                    self.open_condition_facts.with_inserted(family, facts)
                };
            }
        }
    }

    /// Files or withdraws one true equality under each side it pins to a
    /// constant. The two sides are filed exactly as `exact_signed_constant`
    /// used to read them from a scan: the left side names the right side's
    /// constant, and the right side, unless it is the left side itself,
    /// names the left side's.
    fn adjust_exact_constant_equality(
        &mut self,
        condition: &ConditionTerm,
        value: bool,
        insert: bool,
    ) {
        let (ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        }) = condition
        else {
            return;
        };
        if !value {
            return;
        }
        let mut filed = vec![(left.as_ref(), exact_equality_constant(right))];
        if left != right {
            filed.push((right.as_ref(), exact_equality_constant(left)));
        }
        for (term, constant) in filed {
            let Some(constant) = constant else {
                continue;
            };
            let facts = self
                .equality_graph
                .exact_literal_sources(term)
                .cloned()
                .unwrap_or_default();
            let facts = if insert {
                facts.with_inserted(condition.clone(), constant)
            } else {
                facts.without_key(condition)
            };
            self.equality_graph.admitted.exact_constant_equalities = if facts.is_empty() {
                self.equality_graph
                    .admitted
                    .exact_constant_equalities
                    .without_key(term)
            } else {
                self.equality_graph
                    .admitted
                    .exact_constant_equalities
                    .with_inserted(term.clone(), facts)
            };
        }
    }

    fn adjust_bitvector64_equality(
        &mut self,
        condition: &ConditionTerm,
        value: bool,
        insert: bool,
    ) {
        let ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        } = condition
        else {
            return;
        };
        if !value {
            return;
        }
        for side in [left.as_ref(), right.as_ref()] {
            if let Some((_, pointer, kind)) = load_snapshot_and_pointer(side) {
                let key = (pointer, kind);
                let sources = self
                    .equality_graph
                    .admitted
                    .wide_load_sources
                    .get(&key)
                    .cloned()
                    .unwrap_or_default();
                let sources = if insert {
                    sources.with_value(condition.clone())
                } else {
                    sources.without_value(condition)
                };
                if sources.is_empty() {
                    self.equality_graph.admitted.wide_load_sources.remove(&key);
                } else {
                    self.equality_graph
                        .admitted
                        .wide_load_sources
                        .insert(key, sources);
                }
            }
        }
        // A word whose recorded equal names a pointer address is filed by
        // class, so the integer-to-pointer cast finds the fact from an equal
        // word (`pointer_tags::form_of`). Other equalities file nothing.
        if insert {
            for (endpoint, other) in [
                (left.as_ref(), right.as_ref()),
                (right.as_ref(), left.as_ref()),
            ] {
                if mentions_pointer_address(other) {
                    self.equality_graph.record_wide_equation_endpoint(endpoint);
                }
            }
        }
        for (endpoint, other) in [
            (left.as_ref(), right.as_ref()),
            (right.as_ref(), left.as_ref()),
        ] {
            let neighbors = self
                .equality_graph
                .admitted
                .bitvector64_equality_facts
                .get(endpoint)
                .cloned()
                .unwrap_or_default();
            let neighbors = if insert {
                neighbors.with_inserted(other.clone(), condition.clone())
            } else {
                let reversed = ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    left: right.clone(),
                    right: left.clone(),
                };
                if reversed != *condition && self.condition_facts.get(&reversed) == Some(&true) {
                    neighbors.with_inserted(other.clone(), reversed)
                } else {
                    neighbors.without_key(other)
                }
            };
            if let Some(pointer) = endpoint.address_pointer() {
                let bucket = memory_reasoning::parameter_alias_bucket(pointer);
                let endpoints = self
                    .equality_graph
                    .admitted
                    .wide_pointer_alias_endpoints_by_object
                    .get(&bucket)
                    .cloned()
                    .unwrap_or_default();
                let endpoints = if neighbors.is_empty() {
                    endpoints.without_value(endpoint)
                } else {
                    endpoints.with_value(endpoint.clone())
                };
                self.equality_graph
                    .admitted
                    .wide_pointer_alias_endpoints_by_object = if endpoints.is_empty() {
                    self.equality_graph
                        .admitted
                        .wide_pointer_alias_endpoints_by_object
                        .without_key(&bucket)
                } else {
                    self.equality_graph
                        .admitted
                        .wide_pointer_alias_endpoints_by_object
                        .with_inserted(bucket, endpoints)
                };
            }
            self.equality_graph.admitted.bitvector64_equality_facts = if neighbors.is_empty() {
                self.equality_graph
                    .admitted
                    .bitvector64_equality_facts
                    .without_key(endpoint)
            } else {
                self.equality_graph
                    .admitted
                    .bitvector64_equality_facts
                    .with_inserted(endpoint.clone(), neighbors)
            };
        }
    }

    /// Exact full-width equality neighbours of this term, with their checked
    /// premise. This indexed query never searches unrelated snapshot facts.
    pub(in crate::kernel) fn exact_uint64_equalities(
        &self,
        term: &Bitvector32Term,
    ) -> impl Iterator<Item = (&Bitvector32Term, &ConditionTerm)> {
        self.equality_graph.exact_uint64_equalities(term)
    }

    /// A full-width observer result can name the same unchanged cell at a
    /// later snapshot. Inspect only equality neighbors of the queried values;
    /// never search unrelated conditions for a matching load.
    pub(in crate::kernel) fn uint64_values_equal_for_range_resolution(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let same_load = |a: &Bitvector32Term, b: &Bitvector32Term| {
            let (Some((am, ap, ak)), Some((bm, bp, bk))) =
                (load_snapshot_and_pointer(a), load_snapshot_and_pointer(b))
            else {
                return false;
            };
            ak == LoadKind::Bits64
                && bk == ak
                && ap == bp
                && memories_match_for_pointer_load(&am, &bm, &ap)
        };
        left == right
            || self.decide(&ConditionTerm::uint64_equal(left.clone(), right.clone())) == Some(true)
            || same_load(left, right)
            || self.exact_uint64_equalities(left).any(|(other, _)| {
                crate::instrumentation::record_deterministic_work(1);
                other == right || same_load(other, right)
            })
            || self.exact_uint64_equalities(right).any(|(other, _)| {
                crate::instrumentation::record_deterministic_work(1);
                other == left || same_load(other, left)
            })
    }

    /// The terms recorded as 64-bit equal to `term` by one exact fact, each
    /// with the stored fact so a certificate can cite it exactly. Loads may
    /// also match the same pointer in a snapshot whose differing cells are
    /// structurally irrelevant to that pointer; this is an assumption-free
    /// snapshot check, not contextual frame reconstruction.
    pub(in crate::kernel) fn recorded_uint64_equals(
        &self,
        term: &Bitvector32Term,
    ) -> Vec<(Bitvector32Term, ConditionTerm)> {
        self.equality_graph.recorded_uint64_equals(term)
    }

    fn adjust_scalar_evidence_input(
        &mut self,
        condition: &ConditionTerm,
        value: bool,
        insert: bool,
    ) {
        self.equality_graph
            .adjust_scalar_evidence_input(condition, value, insert);
    }

    /// The members of `term`'s recorded-equality class other than `term`:
    /// one walk over the indexed equality graph, bounded by the class.
    pub(in crate::kernel) fn recorded_equality_class(
        &self,
        term: &Bitvector32Term,
    ) -> BTreeSet<Bitvector32Term> {
        self.equality_graph
            .scalar_evidence_class(term)
            .into_iter()
            .collect()
    }

    /// Files or withdraws `condition` under each memory load it mentions.
    /// The cost is one walk of the condition and one update per load key.
    fn adjust_memory_load_condition_index(&mut self, condition: &ConditionTerm, insert: bool) {
        let mut keys = BTreeSet::new();
        collect_condition_memory_load_keys(condition, &mut keys);
        for key in keys {
            let bucket = self
                .memory_load_condition_facts
                .get(&key)
                .cloned()
                .unwrap_or_default();
            let bucket = if insert {
                bucket.with_value(condition.clone())
            } else {
                bucket.without_value(condition)
            };
            self.memory_load_condition_facts = if bucket.is_empty() {
                self.memory_load_condition_facts.without_key(&key)
            } else {
                self.memory_load_condition_facts.with_inserted(key, bucket)
            };
        }
    }

    pub(crate) fn exact_memory_load_condition_candidates(
        &self,
        pointer: &Pointer,
    ) -> impl Iterator<Item = (&ConditionTerm, bool)> {
        let exact_key = (
            pointer.block.clone(),
            memory_blind_pointer_fingerprint(pointer),
        );
        self.memory_load_condition_facts
            .get(&exact_key)
            .into_iter()
            .flat_map(|conditions| conditions.iter())
            .filter_map(|condition| {
                self.condition_facts
                    .get(condition)
                    .copied()
                    .map(|value| (condition, value))
            })
    }

    fn adjust_stated_proposition_index(&mut self, proposition: &Proposition, insert: bool) {
        let index = match &self.stated_proposition_index {
            StatedPropositionIndex::Built(index) => index,
            // A fact the key builder declines by shape never enters the
            // index, so it needs no node (and no copy of a deep chain).
            StatedPropositionIndex::Deferred(_)
                if crate::kernel::proof::proposition_identity_key_declines_shape(proposition) =>
            {
                return;
            }
            StatedPropositionIndex::Deferred(node) => {
                self.stated_proposition_index = StatedPropositionIndex::Deferred(
                    std::sync::Arc::new(DeferredStatedIndexNode {
                        parent: std::sync::Mutex::new(Some(node.clone())),
                        adjustment: Some((
                            crate::kernel::clone_proposition_iteratively(proposition),
                            insert,
                        )),
                        built: std::sync::OnceLock::new(),
                    }),
                );
                return;
            }
        };
        let Some(key) = crate::kernel::proof::proposition_identity_key(proposition) else {
            // A checked key walk may stop at an exhausted tactic budget after
            // the source fact map has already changed. Drop the whole derived
            // index in that case: a missing index only loses an optimization,
            // while retaining an old entry could make a removed fact appear
            // available. The next insertion/rebuild repopulates it.
            if crate::instrumentation::deadline_exceeded_with_work(0) {
                self.stated_proposition_index = StatedPropositionIndex::default();
            }
            return;
        };
        let index = adjust_stated_index(index, key, proposition, insert);
        self.stated_proposition_index = StatedPropositionIndex::Built(index);
    }

    fn rebuild_stated_proposition_index(&mut self) {
        let mut index = StatedIndexMap::default();
        let mut add = |proposition: &Proposition| {
            let Some(key) = crate::kernel::proof::proposition_identity_key(proposition) else {
                return;
            };
            index = adjust_stated_index(&index, key, proposition, true);
        };
        for (condition, value) in self.condition_facts.scan_for_upkeep() {
            add(&Proposition::ConditionIs(condition.clone(), *value));
        }
        for proposition in self.prop_facts.scan_for_upkeep() {
            add(proposition);
        }
        self.stated_proposition_index = StatedPropositionIndex::Built(index);
    }

    /// Builds a deferred stated-proposition index now, as the first query
    /// would. Tests that measure the query itself call it so the one-time
    /// keying of the facts assumed since the last query is not counted
    /// against the lookup.
    #[cfg(test)]
    pub(crate) fn build_stated_proposition_index(&self) {
        let _ = self.stated_proposition_index();
    }

    /// The stated facts alpha-equal to `goal` can only be those filed under
    /// its identity key: the facts of that bucket. None when the key builder
    /// declines `goal` or the index could not be completed in budget.
    pub(in crate::kernel) fn stated_identity_bucket(
        &self,
        goal: &Proposition,
    ) -> impl Iterator<Item = &Proposition> {
        crate::kernel::proof::proposition_identity_key(goal)
            .and_then(|key| self.stated_proposition_index()?.get(&key))
            .into_iter()
            .flat_map(|bucket| bucket.iter())
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// The stated-proposition index, or `None` when a deferred index could
    /// not be completed within the active budget.
    fn stated_proposition_index(&self) -> Option<&StatedIndexMap> {
        match &self.stated_proposition_index {
            StatedPropositionIndex::Built(index) => Some(index),
            StatedPropositionIndex::Deferred(node) => node.force(),
        }
    }

    pub(super) fn clear_proposition_facts(&mut self) {
        self.clear_proposition_facts_with_graph_rebuild(true);
    }

    fn clear_proposition_facts_with_graph_rebuild(&mut self, rebuild_graph: bool) {
        self.prop_facts = Default::default();
        self.equality_graph.clear_proposition_pointer_facts();
        self.execution_fact_projection = self
            .execution_fact_projection
            .iter()
            .filter(|(key, _)| matches!(key, ContextFactKey::Condition(_)))
            .map(|(key, fact)| (key.clone(), fact.clone()))
            .collect();
        self.rebuild_atomic_connection_facts();
        self.rebuild_stated_proposition_index();
        self.disjunction_facts = crate::kernel::fact_collections::ScanSet::default();
        self.equality_graph
            .admitted
            .algebraic_constructor_field_equalities = crate::persistent::PersistentMap::default();
        self.algebraic_constructor_conflicts = crate::persistent::PersistentMap::default();
        self.algebraic_variable_constructors = crate::persistent::PersistentMap::default();
        self.algebraic_variable_variant_evidence = crate::persistent::PersistentMap::default();
        self.resource_compositions = Default::default();
        self.store_owners = None;
        self.composition_members = Default::default();
        self.composition_object_resources = Default::default();
        self.memory_read_defined_facts = crate::persistent::PersistentMap::default();
        self.memory_loadable_facts = crate::persistent::PersistentMap::default();
        self.memory_loadable_object_facts = crate::persistent::PersistentMap::default();
        self.memory_loadable_shape_facts = crate::persistent::PersistentMap::default();
        self.memory_separation_facts = crate::persistent::PersistentMap::default();
        self.resource_contains_facts = crate::persistent::PersistentMap::default();
        self.memory_effect_facts = crate::persistent::PersistentMap::default();
        self.nonmemory_separation_facts = std::sync::Arc::new(Vec::new());
        self.nonmemory_separations_by_side = crate::persistent::PersistentMap::default();
        self.resource_containers = crate::persistent::PersistentMap::default();
        self.memory_containers = crate::persistent::PersistentMap::default();
        self.separation_facts = crate::kernel::fact_collections::ScanSet::default();
        self.separation_facts_by_block = crate::persistent::PersistentMap::default();
        self.wide_separation_facts_by_block = crate::persistent::PersistentMap::default();
        self.separated_address_classes = Default::default();
        self.separated_anchor_offsets = crate::persistent::PersistentMap::default();
        self.separated_anchor_pointers = crate::persistent::PersistentMap::default();
        self.recompute_content_fingerprint();
        // No model support can change in a model-free context. Rebuilding
        // the complete scalar graph here would touch unrelated facts before
        // a restriction replaces its condition indexes.
        if rebuild_graph
            && !self
                .equality_graph
                .admitted
                .algebraic_graph_equalities
                .is_empty()
        {
            self.rebuild_algebraic_graph_equalities();
        }
    }

    #[cfg(test)]
    pub(super) fn retain_proposition_facts(&mut self, keep: impl FnMut(&Proposition) -> bool) {
        let mut keep = keep;
        self.prop_facts = self
            .prop_facts
            .iter()
            .filter(|proposition| keep(proposition))
            .cloned()
            .collect();
        self.execution_fact_projection = self
            .execution_fact_projection
            .iter()
            .filter(|(key, _)| match key {
                ContextFactKey::Condition(_) => true,
                ContextFactKey::Proposition(proposition) => self.prop_facts.contains(proposition),
            })
            .map(|(key, fact)| (key.clone(), fact.clone()))
            .collect();
        self.rebuild_stated_proposition_index();
        self.disjunction_facts = self
            .prop_facts
            .iter()
            .filter(|fact| matches!(fact, Proposition::Or(_, _)))
            .fold(
                crate::kernel::fact_collections::ScanSet::default(),
                |index, fact| index.with_value(crate::kernel::clone_proposition_iteratively(fact)),
            );
        self.rebuild_atomic_connection_facts();
        self.rebuild_algebraic_constructor_field_equalities();
        self.rebuild_memory_loadable_facts();
        self.rebuild_memory_separation_facts();
        self.recompute_content_fingerprint();
        self.equality_graph.clear_proposition_pointer_facts();
        let propositions = self.prop_facts.clone();
        for proposition in propositions.iter() {
            self.adjust_pointer_class_fact(proposition, true);
        }
        self.rebuild_algebraic_graph_equalities();
    }

    fn adjust_pointer_class_fact(&mut self, proposition: &Proposition, insert: bool) {
        if !matches!(
            proposition,
            Proposition::Equal(..)
                | Proposition::Predicate { .. }
                | Proposition::CResourceSeparate { .. }
                | Proposition::ConditionIs(
                    ConditionTerm::AlgebraicEqual(..) | ConditionTerm::PointerValueEqual(..),
                    true
                )
        ) {
            return;
        }
        let key = match proposition {
            Proposition::ConditionIs(condition, _) => ContextFactKey::Condition(condition.clone()),
            _ => ContextFactKey::Proposition(proposition.clone()),
        };
        if let Some(source) = self.execution_fact_projection.get(&key) {
            self.equality_graph.adjust_pointer_fact(source, insert);
        }
    }

    pub(crate) fn function_contract_facts_for(
        &self,
        pointer: &Pointer,
    ) -> impl Iterator<Item = (String, Proposition)> {
        self.equality_graph.pointer_function_contracts(pointer)
    }

    fn proposition_memory_separation(
        proposition: &Proposition,
    ) -> Option<(CMemoryRange, CMemoryRange)> {
        proposition
            .memory_separation()
            .map(|(left, right)| (left.clone(), right.clone()))
    }

    fn adjust_memory_loadable_fact(&mut self, proposition: &Proposition, insert: bool) {
        if let Proposition::CMemoryReadDefined {
            pointer,
            value_type,
            ..
        } = proposition
        {
            let key = (
                crate::kernel::api::canonicalize_pointer_loads(pointer),
                *value_type,
            );
            let facts = self
                .memory_read_defined_facts
                .get(&key)
                .cloned()
                .unwrap_or_default();
            let facts = if insert {
                facts.with_value(proposition.clone())
            } else {
                facts.without_value(proposition)
            };
            self.memory_read_defined_facts = if facts.is_empty() {
                self.memory_read_defined_facts.without_key(&key)
            } else {
                self.memory_read_defined_facts.with_inserted(key, facts)
            };
            return;
        }
        let Proposition::CMemoryLoadable { base, .. } = proposition else {
            return;
        };
        let object = base.object_identity();
        let object_facts = self
            .memory_loadable_object_facts
            .get(&object)
            .cloned()
            .unwrap_or_default();
        let object_facts = if insert {
            object_facts.with_value(proposition.clone())
        } else {
            object_facts.without_value(proposition)
        };
        self.memory_loadable_object_facts = if object_facts.is_empty() {
            self.memory_loadable_object_facts.without_key(&object)
        } else {
            self.memory_loadable_object_facts
                .with_inserted(object, object_facts)
        };

        // Persistent, so a context forked from this one shares every block's
        // facts and an insertion copies only the path to its own block.
        let block_facts = self
            .memory_loadable_facts
            .get(&base.block)
            .cloned()
            .unwrap_or_default();
        let block_facts = if insert {
            block_facts.with_value(proposition.clone())
        } else {
            block_facts.without_value(proposition)
        };
        self.memory_loadable_facts = if block_facts.is_empty() {
            self.memory_loadable_facts.without_key(&base.block)
        } else {
            self.memory_loadable_facts
                .with_inserted(base.block.clone(), block_facts)
        };

        let fingerprint = memory_blind_pointer_fingerprint(base);
        let block_shapes = self
            .memory_loadable_shape_facts
            .get(&base.block)
            .cloned()
            .unwrap_or_default();
        let shape_facts = block_shapes.get(&fingerprint).cloned().unwrap_or_default();
        let shape_facts = if insert {
            shape_facts.with_value(proposition.clone())
        } else {
            shape_facts.without_value(proposition)
        };
        let block_shapes = if shape_facts.is_empty() {
            block_shapes.without_key(&fingerprint)
        } else {
            block_shapes.with_inserted(fingerprint, shape_facts)
        };
        self.memory_loadable_shape_facts = if block_shapes.is_empty() {
            self.memory_loadable_shape_facts.without_key(&base.block)
        } else {
            self.memory_loadable_shape_facts
                .with_inserted(base.block.clone(), block_shapes)
        };
    }

    #[cfg(test)]
    fn rebuild_memory_loadable_facts(&mut self) {
        self.memory_read_defined_facts = crate::persistent::PersistentMap::default();
        self.memory_loadable_facts = crate::persistent::PersistentMap::default();
        self.memory_loadable_object_facts = crate::persistent::PersistentMap::default();
        self.memory_loadable_shape_facts = crate::persistent::PersistentMap::default();
        let facts = self.prop_facts.iter().cloned().collect::<Vec<_>>();
        for proposition in facts {
            self.adjust_memory_loadable_fact(&proposition, true);
        }
    }

    fn adjust_algebraic_constructor_field_equalities(
        &mut self,
        proposition: &Proposition,
        insert: bool,
    ) {
        let Some(fields) = algebraic_constructor_field_equalities(proposition) else {
            return;
        };
        for (field_index, field) in fields.into_iter().enumerate() {
            let source = (proposition.clone(), field_index);
            let mut sources = self
                .equality_graph
                .admitted
                .algebraic_constructor_field_equalities
                .get(&field)
                .cloned()
                .unwrap_or_default();
            if insert {
                sources = sources.with_inserted(source, ());
            } else {
                sources = sources.without_key(&source);
            }
            self.equality_graph
                .admitted
                .algebraic_constructor_field_equalities = if sources.is_empty() {
                self.equality_graph
                    .admitted
                    .algebraic_constructor_field_equalities
                    .without_key(&field)
            } else {
                self.equality_graph
                    .admitted
                    .algebraic_constructor_field_equalities
                    .with_inserted(field, sources)
            };
        }
    }

    fn adjust_algebraic_constructor_conflict(&mut self, proposition: &Proposition, insert: bool) {
        if !is_algebraic_constructor_conflict(proposition) {
            return;
        }
        self.algebraic_constructor_conflicts = if insert {
            self.algebraic_constructor_conflicts
                .with_inserted(proposition.clone(), ())
        } else {
            self.algebraic_constructor_conflicts
                .without_key(proposition)
        };
    }

    fn adjust_algebraic_variable_constructor(&mut self, proposition: &Proposition, insert: bool) {
        let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = proposition else {
            return;
        };
        let (variable, constructor) = match (&left.node, &right.node) {
            (AlgebraicTermNode::Variable(variable), AlgebraicTermNode::Constructor { .. }) => {
                (*variable, right)
            }
            (AlgebraicTermNode::Constructor { .. }, AlgebraicTermNode::Variable(variable)) => {
                (*variable, left)
            }
            _ => return,
        };
        if left.algebraic_type != right.algebraic_type
            || !left.is_well_formed()
            || !right.is_well_formed()
        {
            return;
        }
        let entries = self
            .algebraic_variable_constructors
            .get(&variable)
            .cloned()
            .unwrap_or_default();
        let entries = if insert {
            entries.with_inserted(proposition.clone(), constructor.clone())
        } else {
            entries.without_key(proposition)
        };
        self.algebraic_variable_constructors = if entries.is_empty() {
            self.algebraic_variable_constructors.without_key(&variable)
        } else {
            self.algebraic_variable_constructors
                .with_inserted(variable, entries)
        };
    }

    /// The variant a premise rules out or witnesses for one symbolic
    /// algebraic value, with the scrutinee it speaks about.
    ///
    /// Only the two shapes arm selection can act on are recognized: a
    /// disequality against a field-free constructor, which rules that variant
    /// out, and an existential equality against a constructor, which witnesses
    /// it. Anything else indexes nothing.
    fn proposition_variant_evidence(
        proposition: &Proposition,
    ) -> Option<(Variable, AlgebraicVariantEvidence)> {
        fn scrutinee_and_constructor(
            proposition: &Proposition,
            bound: &BTreeSet<Variable>,
        ) -> Option<(Variable, String, usize)> {
            let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = proposition
            else {
                return None;
            };
            if left.algebraic_type != right.algebraic_type
                || !left.is_well_formed()
                || !right.is_well_formed()
            {
                return None;
            }
            let (variable, constructor) = match (&left.node, &right.node) {
                (AlgebraicTermNode::Variable(variable), AlgebraicTermNode::Constructor { .. }) => {
                    (*variable, right)
                }
                (AlgebraicTermNode::Constructor { .. }, AlgebraicTermNode::Variable(variable)) => {
                    (*variable, left)
                }
                _ => return None,
            };
            if bound.contains(&variable) {
                return None;
            }
            let AlgebraicTermNode::Constructor { variant, fields } = &constructor.node else {
                return None;
            };
            Some((variable, variant.clone(), fields.len()))
        }

        match proposition {
            Proposition::Not(body) => {
                let (variable, variant, arity) = scrutinee_and_constructor(body, &BTreeSet::new())?;
                // `model != Some(3)` leaves `Some` possible; only a field-free
                // constructor names the whole variant.
                (arity == 0).then_some((
                    variable,
                    AlgebraicVariantEvidence {
                        kind: AlgebraicVariantEvidenceKind::Excluded,
                        variant,
                    },
                ))
            }
            Proposition::Exists { .. } => {
                let mut bound = BTreeSet::new();
                let mut body = proposition;
                while let Proposition::Exists {
                    var, body: inner, ..
                } = body
                {
                    bound.insert(*var);
                    body = inner;
                }
                let (variable, variant, _) = scrutinee_and_constructor(body, &bound)?;
                Some((
                    variable,
                    AlgebraicVariantEvidence {
                        kind: AlgebraicVariantEvidenceKind::Witnessed,
                        variant,
                    },
                ))
            }
            _ => None,
        }
    }

    fn adjust_algebraic_variable_variant_evidence(
        &mut self,
        proposition: &Proposition,
        insert: bool,
    ) {
        let Some((variable, evidence)) = Self::proposition_variant_evidence(proposition) else {
            return;
        };
        let entries = self
            .algebraic_variable_variant_evidence
            .get(&variable)
            .cloned()
            .unwrap_or_default();
        let entries = if insert {
            entries.with_inserted(proposition.clone(), evidence)
        } else {
            entries.without_key(proposition)
        };
        self.algebraic_variable_variant_evidence = if entries.is_empty() {
            self.algebraic_variable_variant_evidence
                .without_key(&variable)
        } else {
            self.algebraic_variable_variant_evidence
                .with_inserted(variable, entries)
        };
    }

    /// Every premise of this context that rules out or witnesses a variant of
    /// `variable`, with the premise itself so a selection can cite it.
    pub(in crate::kernel) fn algebraic_variant_evidence(
        &self,
        variable: Variable,
    ) -> impl Iterator<Item = (&Proposition, &AlgebraicVariantEvidence)> {
        crate::instrumentation::record_deterministic_work(1);
        self.algebraic_variable_variant_evidence
            .get(&variable)
            .into_iter()
            .flat_map(crate::persistent::PersistentMap::iter)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// Whether these facts give `value` a constructor.
    pub(crate) fn knows_algebraic_constructor(&self, value: &AlgebraicTerm) -> bool {
        self.known_algebraic_constructor(value).is_some()
    }

    /// The constructor a fact equates algebraic variable `variable` to.
    pub(in crate::kernel) fn variable_algebraic_constructor(
        &self,
        variable: Variable,
    ) -> Option<AlgebraicTerm> {
        let (premise, constructor) = self
            .algebraic_variable_constructors
            .get(&variable)?
            .iter()
            .next()
            .map(|(premise, constructor)| (premise.clone(), constructor.clone()))?;
        record_reasoning_provenance(self, &premise);
        Some(constructor)
    }

    /// Whether a fact equates some algebraic variable to a constructor.
    pub(crate) fn has_algebraic_constructor_facts(&self) -> bool {
        !self.algebraic_variable_constructors.is_empty()
    }

    pub(in crate::kernel) fn known_algebraic_constructor(
        &self,
        value: &AlgebraicTerm,
    ) -> Option<AlgebraicTerm> {
        match &value.node {
            AlgebraicTermNode::Constructor { .. } => value.is_well_formed().then(|| value.clone()),
            // A constructor stated for the variable itself comes first. On an
            // infeasible path the variable's class can join two constructors
            // (a matched `Left` arm and a derived `Top`), and the class keeps
            // only the first witness it saw; the stated one is what the proof
            // is reasoning about.
            AlgebraicTermNode::Variable(variable)
                if let Some((premise, constructor)) = self
                    .algebraic_variable_constructors
                    .get(variable)
                    .and_then(|constructors| {
                        constructors
                            .iter()
                            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
                            .find(|(_, constructor)| {
                                constructor.algebraic_type == value.algebraic_type
                            })
                    }) =>
            {
                record_reasoning_provenance(self, premise);
                Some(constructor.clone())
            }
            _ => {
                let constructor = self.equality_graph.known_algebraic_constructor(value)?;
                record_reasoning_provenance(
                    self,
                    &Proposition::Equal(
                        Term::Algebraic(value.clone()),
                        Term::Algebraic(constructor.clone()),
                    ),
                );
                Some(constructor)
            }
        }
    }

    #[cfg(test)]
    fn rebuild_algebraic_constructor_field_equalities(&mut self) {
        self.algebraic_variable_constructors = crate::persistent::PersistentMap::default();
        self.algebraic_variable_variant_evidence = crate::persistent::PersistentMap::default();
        self.equality_graph
            .admitted
            .algebraic_constructor_field_equalities = crate::persistent::PersistentMap::default();
        self.algebraic_constructor_conflicts = crate::persistent::PersistentMap::default();
        let facts = self.prop_facts.iter().cloned().collect::<Vec<_>>();
        for proposition in facts {
            self.adjust_algebraic_constructor_field_equalities(&proposition, true);
            self.adjust_algebraic_constructor_conflict(&proposition, true);
            self.adjust_algebraic_variable_constructor(&proposition, true);
            self.adjust_algebraic_variable_variant_evidence(&proposition, true);
        }
    }

    pub(crate) fn algebraic_constructor_field_sources(
        &self,
        field: &Proposition,
    ) -> impl Iterator<Item = &(Proposition, usize)> {
        self.equality_graph
            .algebraic_constructor_field_sources(field)
    }

    /// Whether an exact same-constructor equality in this context entails
    /// `field`. This is the checked no-confusion rule used by explicit
    /// `extract`; the persistent index keeps the query independent of the
    /// number of unrelated facts in the proof state.
    pub(crate) fn contains_algebraic_constructor_field_equality(
        &self,
        field: &Proposition,
    ) -> bool {
        self.algebraic_constructor_field_sources(field)
            .next()
            .is_some()
    }

    /// Test census of the loadable facts whose base is in `block`.
    #[cfg(test)]
    pub(crate) fn memory_loadable_candidates(
        &self,
        block: &PointerBlock,
    ) -> impl Iterator<Item = &Proposition> {
        self.memory_loadable_facts
            .get(block)
            .into_iter()
            .flat_map(|facts| facts.iter())
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// Return at most one fact per structural or indexed address shape.
    /// Ambiguous buckets and other alias spellings require premise search.
    /// A singleton selected source may be checked across block spellings.
    pub(crate) fn memory_loadable_candidates_for_base(
        &self,
        base: &Pointer,
    ) -> impl Iterator<Item = &Proposition> {
        self.memory_loadable_candidates_for_base_with_aliases(base, true, None)
    }

    pub(crate) fn memory_loadable_exact_candidates_for_base(
        &self,
        base: &Pointer,
    ) -> impl Iterator<Item = &Proposition> {
        self.memory_loadable_candidates_for_base_with_aliases(base, false, None)
    }

    /// Enumerating an ambiguous address bucket is premise search. The checker
    /// can instead receive one explicitly selected source view.
    pub(crate) fn search_memory_loadable_candidates_for_base(
        &self,
        permission: crate::SearchPermission,
        base: &Pointer,
    ) -> impl Iterator<Item = &Proposition> {
        self.memory_loadable_candidates_for_base_with_aliases(base, true, Some(permission))
    }

    fn memory_loadable_candidates_for_base_with_aliases(
        &self,
        base: &Pointer,
        include_other_spellings: bool,
        permission: Option<crate::SearchPermission>,
    ) -> impl Iterator<Item = &Proposition> {
        crate::instrumentation::record_deterministic_work(1);
        let search = permission.is_some();
        let exact = self
            .memory_loadable_shape_facts
            .get(&base.block)
            .and_then(|shapes| shapes.get(&memory_blind_pointer_fingerprint(base)))
            .filter(|facts| search || facts.len() == 1)
            .into_iter()
            .flat_map(|facts| facts.iter());
        // Do not even prepare an alias class when the exact address answers.
        let related =
            std::iter::once_with(move || self.memory_loadable_related_candidates(base, permission))
                .take(usize::from(
                    include_other_spellings && !self.memory_loadable_facts.is_empty(),
                ))
                .flatten();
        exact
            .chain(related)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
            .filter(move |fact| match fact {
                Proposition::CMemoryLoadable { base: source, .. } => {
                    !base.blocks_proven_distinct(source)
                }
                _ => false,
            })
    }

    /// Class enumeration is premise selection, not part of checked lookup.
    fn memory_loadable_aliases_for_search(
        &self,
        _permission: crate::SearchPermission,
        base: &Pointer,
    ) -> impl Iterator<Item = Pointer> {
        self.exact_pointer_aliases(base)
            .cloned()
            .chain(self.equality_graph.pointer_spellings(base))
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    fn memory_loadable_related_candidates(
        &self,
        base: &Pointer,
        permission: Option<crate::SearchPermission>,
    ) -> impl Iterator<Item = &Proposition> {
        let search = permission.is_some();
        // Structural and maintained class coordinates select keys, never all
        // class members or ranges sharing a block. The exact key was already
        // visited by the caller. Only a planner can append other spellings.
        let mut anchors = vec![Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        }];
        let mut offsets = vec![&base.offset];
        while let Some(offset) = offsets.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if let PointerOffsetTerm::Add(left, right) = offset {
                for part in [left.as_ref(), right.as_ref()] {
                    anchors.push(Pointer {
                        block: base.block.clone(),
                        offset: part.clone(),
                    });
                    offsets.push(part);
                }
            }
        }
        // Two indexed coordinates, independent of the number of spellings:
        // the maintained affine representative and a unique concrete anchor.
        if let Some(coordinate) = self.equality_graph.canonical_pointer(base)
            && let Some(offset) = coordinate.offset.to_offset_term()
        {
            anchors.push(Pointer {
                block: coordinate.representative.clone(),
                offset: PointerOffsetTerm::Constant(0),
            });
            anchors.push(Pointer {
                block: coordinate.representative,
                offset,
            });
        }
        let storage = self.equality_graph.storage_address(base);
        anchors.push(Pointer {
            block: storage.block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        });
        anchors.push(storage);
        if let Some(permission) = permission {
            anchors.extend(self.memory_loadable_aliases_for_search(permission, base));
        }
        let mut keys =
            BTreeSet::from([(base.block.clone(), memory_blind_pointer_fingerprint(base))]);
        let anchors = anchors
            .into_iter()
            .filter_map(|anchor| {
                crate::instrumentation::record_deterministic_work(1);
                let key = (
                    anchor.block.clone(),
                    memory_blind_pointer_fingerprint(&anchor),
                );
                keys.insert(key.clone()).then_some(key)
            })
            .collect::<Vec<_>>();
        // A selected singleton can cover an address whose structural anchor
        // normalization erased. Cached length avoids an ambient walk.
        let singleton =
            self.memory_loadable_facts
                .get(&base.block)
                .filter(|facts| facts.len() == 1)
                .or_else(|| {
                    // An explicitly selected view may use another block's
                    // spelling. Cached lengths select it without an alias
                    // walk; coverage still checks the two supplied addresses.
                    (self.memory_loadable_facts.len() == 1)
                        .then(|| self.memory_loadable_facts.values().next())
                        .flatten()
                        .filter(|facts| facts.len() == 1)
                })
                .and_then(|facts| facts.iter().next())
                .filter(|fact| match fact {
                    Proposition::CMemoryLoadable { base, .. } => !keys
                        .contains(&(base.block.clone(), memory_blind_pointer_fingerprint(base))),
                    _ => false,
                });
        anchors
            .into_iter()
            .flat_map(move |(block, fingerprint)| {
                crate::instrumentation::record_deterministic_work(1);
                self.memory_loadable_shape_facts
                    .get(&block)
                    .and_then(|shapes| shapes.get(&fingerprint))
                    .filter(|facts| search || facts.len() == 1)
                    .into_iter()
                    .flat_map(|facts| facts.iter())
            })
            .chain(singleton)
    }

    /// The read-defined facts stated at `pointer` for `value_type`, at one
    /// of its exact aliases, or at another spelling in its equality class:
    /// the keys [`Self::has_memory_read_defined_evidence`] looks up.
    pub(crate) fn search_memory_read_defined_candidates(
        &self,
        _permission: crate::SearchPermission,
        pointer: &Pointer,
        value_type: CType,
    ) -> Vec<&Proposition> {
        let spellings = self.equality_graph.pointer_spellings(pointer);
        std::iter::once(pointer)
            .chain(self.exact_pointer_aliases(pointer))
            .chain(spellings.iter())
            .filter_map(|candidate| {
                crate::instrumentation::record_deterministic_work(1);
                self.memory_read_defined_facts.get(&(
                    crate::kernel::api::canonicalize_pointer_loads(candidate),
                    value_type,
                ))
            })
            .flat_map(crate::persistent::PersistentSet::iter)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
            .collect()
    }

    /// The separation facts the prover consults directly for two memory
    /// ranges: those stated between their blocks, and the residue with a
    /// non-memory side. `None` for any other query shape, which the prover
    /// answers by scanning.
    pub(crate) fn resource_separation_candidates(
        &self,
        left: &CResource,
        right: &CResource,
    ) -> Option<Vec<&Proposition>> {
        let (CResource::Memory(left), CResource::Memory(right)) = (left, right) else {
            return None;
        };
        Some(
            self.memory_separation_candidates(&left.base().block, &right.base().block)
                .map(|(proposition, _, _)| proposition)
                .chain(self.nonmemory_separation_facts.iter())
                .collect(),
        )
    }

    /// Memory separations selected by the caller's containment blocks.
    /// Callers additionally name pointers whose related roots and affine
    /// block classes a wide side may cover. A translated window may have no
    /// exact alias at its shifted address, but retains its base's block class.
    /// Results retain proposition order, so a `find`
    /// selects the same witness as the full scan.
    pub(in crate::kernel) fn memory_separations_near<'a, 'b>(
        &'a self,
        blocks: impl IntoIterator<Item = &'b PointerBlock>,
        wide_pointers: impl IntoIterator<Item = &'b Pointer>,
    ) -> std::collections::BTreeSet<&'a Proposition> {
        let blocks = blocks.into_iter().cloned().collect::<BTreeSet<_>>();
        let mut candidates = BTreeSet::new();
        let mut visit = |index: &'a crate::persistent::PersistentMap<
            PointerBlock,
            crate::persistent::PersistentSet<Proposition>,
        >,
                         block: &PointerBlock| {
            crate::instrumentation::record_deterministic_work(1);
            for fact in index
                .get(block)
                .into_iter()
                .flat_map(crate::persistent::PersistentSet::iter)
            {
                crate::instrumentation::record_deterministic_work(1);
                candidates.insert(fact);
            }
        };
        for block in &blocks {
            visit(&self.separation_facts_by_block, block);
        }
        if !self.wide_separation_facts_by_block.is_empty() {
            let mut wide_blocks = blocks;
            for pointer in wide_pointers {
                wide_blocks.extend(self.equality_graph.pointer_class_blocks(&pointer.block));
                wide_blocks.extend(crate::kernel::primitives::related_pointer_root_blocks(
                    pointer, self,
                ));
            }
            for block in wide_blocks {
                visit(&self.wide_separation_facts_by_block, &block);
            }
        }
        candidates
    }

    pub(in crate::kernel) fn memory_loadable_candidates_for_object(
        &self,
        pointer: &Pointer,
    ) -> impl Iterator<Item = &Proposition> {
        crate::instrumentation::record_deterministic_work(1);
        self.memory_loadable_object_facts
            .get(&pointer.object_identity())
            .into_iter()
            .flat_map(crate::persistent::PersistentSet::iter)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    fn memory_separation_key(
        left: &PointerBlock,
        right: &PointerBlock,
    ) -> (PointerBlock, PointerBlock) {
        if left <= right {
            (left.clone(), right.clone())
        } else {
            (right.clone(), left.clone())
        }
    }

    /// Files or withdraws a memory effect fact under both of its memories.
    fn adjust_memory_effect_fact(&mut self, proposition: &Proposition, insert: bool) {
        let (Proposition::CMemoryEffectSummary { before, after, .. }
        | Proposition::CMemoryMutatesOnly { before, after, .. }
        | Proposition::CHeapAllocationFreed { before, after, .. }) = proposition
        else {
            return;
        };
        for memory in [before, after] {
            let summaries = self
                .memory_effect_facts
                .get(memory)
                .cloned()
                .unwrap_or_default();
            let summaries = if insert {
                summaries.with_value(proposition.clone())
            } else {
                summaries.without_value(proposition)
            };
            self.memory_effect_facts = if summaries.is_empty() {
                self.memory_effect_facts.without_key(memory)
            } else {
                self.memory_effect_facts
                    .with_inserted(memory.clone(), summaries)
            };
        }
    }

    /// The memory effect facts with `memory` as their `before` or `after`.
    pub(in crate::kernel) fn memory_effect_facts_naming(
        &self,
        memory: &CMemory,
    ) -> impl Iterator<Item = &Proposition> {
        self.memory_effect_facts
            .get(memory)
            .into_iter()
            .flat_map(crate::persistent::PersistentSet::iter)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// Every memory effect fact once, charged one unit per filed entry. A
    /// fact is filed under both of its memories; it is yielded from the
    /// bucket of its `before` memory.
    pub(in crate::kernel) fn memory_effect_fact_propositions(
        &self,
    ) -> impl Iterator<Item = &Proposition> {
        self.memory_effect_facts.iter().flat_map(|(memory, facts)| {
            facts
                .iter()
                .inspect(|_| crate::instrumentation::record_deterministic_work(1))
                .filter(move |fact| {
                    matches!(
                        fact,
                        Proposition::CMemoryEffectSummary { before, .. }
                        | Proposition::CMemoryMutatesOnly { before, .. }
                        | Proposition::CHeapAllocationFreed { before, .. }
                            if before == memory
                    )
                })
        })
    }

    /// Files or withdraws a `CResourceContains` fact under its parent's key.
    fn adjust_resource_contains_fact(&mut self, proposition: &Proposition, insert: bool) {
        let Proposition::CResourceContains { parent, child } = proposition else {
            return;
        };
        match &**child {
            CResource::Memory(range) => {
                self.memory_containers = with_adjusted_member(
                    &self.memory_containers,
                    &range.base().block,
                    proposition,
                    insert,
                );
            }
            child => {
                self.resource_containers =
                    with_adjusted_member(&self.resource_containers, child, proposition, insert);
            }
        }
        let key = ResourceContainsKey::of(parent);
        let facts = self
            .resource_contains_facts
            .get(&key)
            .cloned()
            .unwrap_or_default();
        let facts = if insert {
            facts.with_value(proposition.clone())
        } else {
            facts.without_value(proposition)
        };
        self.resource_contains_facts = if facts.is_empty() {
            self.resource_contains_facts.without_key(&key)
        } else {
            self.resource_contains_facts.with_inserted(key, facts)
        };
    }

    /// The separation facts with a side that may contain `resource`, a
    /// non-memory resource. Containment of a non-memory resource is identity
    /// or a chain of containment facts down to it
    /// (`proves_resource_contains_inner`), so its containers are walked
    /// upward through the facts filed under each child. A memory parent on
    /// the way is contained by range, up to memory resolution: by a stated
    /// separation's memory side filed under a block related to its base
    /// (`memory_separations_near`), or by a non-memory side, which the
    /// residual list holds (`nonmemory_separation_facts`).
    pub(in crate::kernel) fn separations_with_side_containing(
        &self,
        resource: &CResource,
    ) -> BTreeSet<&Proposition> {
        let mut containers = BTreeSet::from([resource]);
        let mut memory_parents = Vec::new();
        let mut pending = vec![resource];
        while let Some(current) = pending.pop() {
            for fact in self
                .resource_containers
                .get(current)
                .into_iter()
                .flat_map(crate::persistent::PersistentSet::iter)
            {
                crate::instrumentation::record_deterministic_work(1);
                let Proposition::CResourceContains { parent, .. } = fact else {
                    continue;
                };
                if let CResource::Memory(range) = &**parent {
                    memory_parents.push(range);
                    continue;
                }
                if containers.insert(parent) {
                    pending.push(parent);
                }
            }
        }
        let mut separations = BTreeSet::new();
        for container in containers {
            crate::instrumentation::record_deterministic_work(1);
            for fact in self
                .nonmemory_separations_by_side
                .get(container)
                .into_iter()
                .flat_map(crate::persistent::PersistentSet::iter)
            {
                crate::instrumentation::record_deterministic_work(1);
                separations.insert(fact);
            }
        }
        if !memory_parents.is_empty() {
            let blocks = memory_parents
                .iter()
                .flat_map(|range| {
                    crate::kernel::primitives::related_pointer_root_blocks(range.base(), self)
                })
                .collect::<BTreeSet<_>>();
            separations.extend(self.memory_separations_near(
                blocks.iter(),
                memory_parents.iter().map(|range| range.base()),
            ));
            separations.extend(self.nonmemory_separation_facts.iter().inspect(|_| {
                crate::instrumentation::record_deterministic_work(1);
            }));
        }
        separations
    }

    /// The `CResourceContains` facts whose parent `current` may contain by
    /// `resource_contains_builtin`: filed under `current` itself, or for a
    /// memory range under its base block and the blocks of the base's exact
    /// aliases.
    pub(super) fn resource_contains_candidates(&self, current: &CResource) -> Vec<&Proposition> {
        let mut keys = vec![ResourceContainsKey::of(current)];
        if let CResource::Memory(range) = current {
            for alias in self.exact_pointer_aliases(range.base()) {
                let key = ResourceContainsKey::Block(alias.block.clone());
                if !keys.contains(&key) {
                    keys.push(key);
                }
            }
        }
        keys.iter()
            .filter_map(|key| self.resource_contains_facts.get(key))
            .flat_map(crate::persistent::PersistentSet::iter)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
            .collect()
    }

    fn adjust_memory_separation_fact(&mut self, proposition: &Proposition, insert: bool) {
        let Some(pair) = Self::proposition_memory_separation(proposition) else {
            return;
        };
        self.adjust_separated_anchor_offsets(proposition, &pair.0, &pair.1, insert);
        if let (Some(left), Some(right)) =
            (memory_range_anchor(&pair.0), memory_range_anchor(&pair.1))
        {
            self.separated_address_classes.adjust(
                proposition,
                Pointer {
                    block: pair.0.base().block.clone(),
                    offset: left,
                },
                Pointer {
                    block: pair.1.base().block.clone(),
                    offset: right,
                },
                insert,
                &self.equality_graph,
            );
        }
        let key = Self::memory_separation_key(&pair.0.base().block, &pair.1.base().block);
        // Persistent by block pair, so an insertion copies only its own
        // pair's bucket, not every other pair's.
        let mut pairs = self
            .memory_separation_facts
            .get(&key)
            .cloned()
            .unwrap_or_default();
        if insert {
            std::sync::Arc::make_mut(&mut pairs).push((proposition.clone(), pair.0, pair.1));
        } else if let Some(position) = pairs
            .iter()
            .position(|candidate| candidate.0 == *proposition)
        {
            std::sync::Arc::make_mut(&mut pairs).remove(position);
        }
        self.memory_separation_facts = if pairs.is_empty() {
            self.memory_separation_facts.without_key(&key)
        } else {
            self.memory_separation_facts.with_inserted(key, pairs)
        };
    }

    #[cfg(test)]
    fn rebuild_memory_separation_facts(&mut self) {
        self.resource_contains_facts = crate::persistent::PersistentMap::default();
        self.memory_effect_facts = crate::persistent::PersistentMap::default();
        self.memory_separation_facts = crate::persistent::PersistentMap::default();
        self.nonmemory_separation_facts = std::sync::Arc::new(Vec::new());
        self.nonmemory_separations_by_side = crate::persistent::PersistentMap::default();
        self.resource_containers = crate::persistent::PersistentMap::default();
        self.memory_containers = crate::persistent::PersistentMap::default();
        self.separation_facts = self
            .prop_facts
            .iter()
            .filter(|fact| matches!(fact, Proposition::CResourceSeparate { .. }))
            .fold(
                crate::kernel::fact_collections::ScanSet::default(),
                |index, fact| index.with_value(fact.clone()),
            );
        self.separation_facts_by_block = crate::persistent::PersistentMap::default();
        self.wide_separation_facts_by_block = crate::persistent::PersistentMap::default();
        self.separated_address_classes = Default::default();
        let facts = self.prop_facts.iter().cloned().collect::<Vec<_>>();
        for proposition in facts {
            self.adjust_separation_block_fact(&proposition, true);
            self.adjust_memory_separation_fact(&proposition, true);
            self.adjust_nonmemory_separation_fact(&proposition, true);
            self.adjust_resource_contains_fact(&proposition, true);
            self.adjust_memory_effect_fact(&proposition, true);
        }
        // The anchor index mirrors the stated separations just rebuilt.
        self.rebuild_separated_anchor_offsets();
    }

    /// Files or withdraws a memory separation under each endpoint block,
    /// in the narrow or wide index according to its bounds.
    fn adjust_separation_block_fact(&mut self, proposition: &Proposition, insert: bool) {
        let Some((left, right)) = proposition.memory_separation() else {
            return;
        };
        let index = if left.wide_bounds().is_some() || right.wide_bounds().is_some() {
            &mut self.wide_separation_facts_by_block
        } else {
            &mut self.separation_facts_by_block
        };
        let mut blocks = vec![left.base().block.clone()];
        if right.base().block != left.base().block {
            blocks.push(right.base().block.clone());
        }
        for key in blocks {
            let bucket = index.get(&key).cloned().unwrap_or_default();
            let bucket = if insert {
                bucket.with_value(proposition.clone())
            } else {
                bucket.without_value(proposition)
            };
            *index = if bucket.is_empty() {
                index.without_key(&key)
            } else {
                index.with_inserted(key, bucket)
            };
        }
    }

    /// Maintains the residual separation-fact list: `CResourceSeparate`
    /// facts with at least one non-memory side, which the block-pair index
    /// cannot serve but whose containment may entail memory separation.
    fn adjust_nonmemory_separation_fact(&mut self, proposition: &Proposition, insert: bool) {
        let Proposition::CResourceSeparate { left, right } = proposition else {
            return;
        };
        if Self::proposition_memory_separation(proposition).is_some() {
            return;
        }
        for side in [left, right] {
            if !matches!(**side, CResource::Memory(_)) {
                self.nonmemory_separations_by_side = with_adjusted_member(
                    &self.nonmemory_separations_by_side,
                    side,
                    proposition,
                    insert,
                );
            }
        }
        let residuals = std::sync::Arc::make_mut(&mut self.nonmemory_separation_facts);
        if insert {
            if !residuals.contains(proposition) {
                residuals.push(proposition.clone());
            }
        } else if let Some(position) = residuals
            .iter()
            .position(|candidate| candidate == proposition)
        {
            residuals.remove(position);
        }
    }

    /// Stated separations whose nonempty anchors are exactly these addresses.
    /// Unlike the block-pair bucket, unrelated external parameters cannot be
    /// candidates. Consumers must still check both complete access widths.
    pub(in crate::kernel) fn anchored_memory_separation_candidates(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> impl Iterator<Item = &Proposition> {
        let left = self.equality_graph.storage_address(left);
        let right = self.equality_graph.storage_address(right);
        let facts = if left.block == right.block {
            self.separated_anchor_offsets
                .get(&Self::separated_anchor_key(left.offset, right.offset))
        } else {
            self.separated_anchor_pointers
                .get(&Self::separated_pointer_key(left, right))
        };
        facts.into_iter().flat_map(|facts| facts.iter())
    }

    /// The stated memory separations between these two blocks, from the
    /// block-pair index. A composition's same-block separations are not
    /// here: they are asked of the composition when a query needs one
    /// ([`Self::composition_separated_members`]).
    pub(super) fn memory_separation_candidates(
        &self,
        left: &PointerBlock,
        right: &PointerBlock,
    ) -> impl Iterator<Item = (&Proposition, &CMemoryRange, &CMemoryRange)> + Clone {
        let key = Self::memory_separation_key(left, right);
        self.memory_separation_facts
            .get(&key)
            .map(|pairs| pairs.as_slice())
            .unwrap_or(&[])
            .iter()
            .map(|(proposition, left, right)| (proposition, left, right))
    }

    /// The composition law, asked on demand: the first held composition with
    /// two distinct owned members that it separates, `left` accepting the
    /// first, `right` the second, and `admit` the pair
    /// (`ResourceContext::separated_owned_members`). The members may lie in
    /// different blocks. Each composition asks its members of the two
    /// blocks, so the query costs the members it reads and never their
    /// pairs, and nothing is stated into this context beforehand.
    ///
    /// `left_at` and `right_at` are addresses the two sides are spelled at;
    /// they choose which members are asked first and never change the
    /// answer (`ResourceContext::separated_owned_members`).
    pub(in crate::kernel) fn composition_separated_members<'a>(
        &'a self,
        left_at: &Pointer,
        right_at: &Pointer,
        left: impl Fn(&CMemoryRange) -> bool,
        right: impl Fn(&CMemoryRange) -> bool,
        admit: impl Fn(&CMemoryRange, &CMemoryRange) -> bool,
    ) -> Option<(&'a ResourceContext, &'a CMemoryRange, &'a CMemoryRange)> {
        let (left_block, right_block) = (&left_at.block, &right_at.block);
        // A composition holding the pair is listed under each member's
        // block (`CompositionMemberIndex`).
        self.composition_members
            .listed_under([], [left_block, right_block])
            .into_iter()
            .find_map(|resources| {
                resources
                    .separated_owned_members(
                        left_block,
                        right_block,
                        left_at,
                        right_at,
                        self,
                        &left,
                        &right,
                        &admit,
                    )
                    .map(|(left, right)| (resources, left, right))
            })
    }

    /// Separation of an exposed owner and a checked loan-bound projection.
    /// Candidate lookup uses only the queried address keys, and the retained
    /// composition is the authority subsequently checked by memory evidence.
    pub(in crate::kernel) fn borrow_partition_separated_members<'a>(
        &'a self,
        left: &Pointer,
        right: &Pointer,
        contains_left: impl Fn(&CMemoryRange) -> bool,
        contains_right: impl Fn(&CMemoryRange) -> bool,
    ) -> Option<(&'a ResourceContext, &'a CMemoryRange, &'a CMemoryRange)> {
        for source in self
            .composition_object_resources
            .partition_sources_at(&[left, right])
        {
            if !self.resource_compositions.contains(source) {
                continue;
            }
            for borrowed in [false, true] {
                if let Some((a, b)) = source
                    .partition_memory_member_at(left, borrowed, &contains_left)
                    .zip(source.partition_memory_member_at(right, !borrowed, &contains_right))
                    && !self.memory_ranges_overlap_after_base_equality(a, b)
                {
                    record_implicit_reasoning_provenance(
                        self,
                        &Proposition::CResourceComposition(source.clone()),
                    );
                    return Some((source, a, b));
                }
            }
        }
        None
    }

    /// Publish the held entry composition's address input once in this
    /// context's lineage. This prepares an index over the explicit input;
    /// subsequent equality facts advance only their own class deltas.
    /// The publication changes no logical facts or resource permissions.
    pub(crate) fn with_prepared_resource_addresses(mut self, resources: &ResourceContext) -> Self {
        let observable = resources.observable_composition();
        observable.synchronize_memory_equalities(&self);
        self.composition_object_resources.admit(&observable);
        self
    }

    pub(super) fn insert_proposition_fact(&mut self, proposition: Proposition) {
        self.execution_variable_ceiling
            .file_proposition(&proposition);
        if let Proposition::CResourceComposition(resources) = proposition {
            if !self.resource_compositions.contains(&resources) {
                self.resource_compositions =
                    self.resource_compositions.with_value(resources.clone());
                self.composition_members.admit(&resources);
                self.composition_object_resources.admit(&resources);
                self.composition_object_resources
                    .advance_memory_equalities(self);
                self.content_fingerprint ^= Self::fingerprint(3, &resources);
            }
            return;
        }
        if self
            .prop_facts
            .insert(crate::kernel::clone_proposition_iteratively(&proposition))
            .is_none()
        {
            self.execution_fact_projection.insert(
                ContextFactKey::Proposition(proposition.clone()),
                std::sync::Arc::new(ExecutionPureFact::new(proposition.clone())),
            );
            self.adjust_atomic_connection_fact(&proposition, true);
            self.adjust_stated_proposition_index(&proposition, true);
            if matches!(proposition, Proposition::Or(_, _)) {
                self.disjunction_facts = self
                    .disjunction_facts
                    .with_value(crate::kernel::clone_proposition_iteratively(&proposition));
            }
            if matches!(proposition, Proposition::CResourceSeparate { .. }) {
                self.separation_facts = self
                    .separation_facts
                    .with_value(crate::kernel::clone_proposition_iteratively(&proposition));
            }
            self.adjust_algebraic_constructor_field_equalities(&proposition, true);
            self.adjust_algebraic_constructor_conflict(&proposition, true);
            self.adjust_algebraic_variable_constructor(&proposition, true);
            self.adjust_algebraic_graph_equality(&proposition, true);
            self.adjust_pointer_value_equality(&proposition, true);
            self.adjust_algebraic_variable_variant_evidence(&proposition, true);
            self.adjust_memory_loadable_fact(&proposition, true);
            self.adjust_separation_block_fact(&proposition, true);
            self.adjust_memory_separation_fact(&proposition, true);
            self.adjust_nonmemory_separation_fact(&proposition, true);
            self.adjust_resource_contains_fact(&proposition, true);
            self.adjust_memory_effect_fact(&proposition, true);
            self.adjust_pointer_class_fact(&proposition, true);
            self.content_fingerprint ^= Self::fingerprint(2, &proposition);
        }
    }

    #[cfg(test)]
    pub(super) fn remove_proposition_fact(&mut self, proposition: &Proposition) {
        if self.prop_facts.remove(proposition).is_some() {
            self.adjust_pointer_class_fact(proposition, false);
            self.execution_fact_projection
                .remove(&ContextFactKey::Proposition(proposition.clone()));
            self.adjust_atomic_connection_fact(proposition, false);
            self.adjust_stated_proposition_index(proposition, false);
            if matches!(proposition, Proposition::Or(_, _)) {
                self.disjunction_facts = self.disjunction_facts.without_value(proposition);
            }
            if matches!(proposition, Proposition::CResourceSeparate { .. }) {
                self.separation_facts = self.separation_facts.without_value(proposition);
            }
            self.adjust_algebraic_constructor_field_equalities(proposition, false);
            self.adjust_algebraic_constructor_conflict(proposition, false);
            self.adjust_algebraic_variable_constructor(proposition, false);
            self.adjust_algebraic_graph_equality(proposition, false);
            self.adjust_pointer_value_equality(proposition, false);
            self.adjust_algebraic_variable_variant_evidence(proposition, false);
            self.adjust_memory_loadable_fact(proposition, false);
            self.adjust_separation_block_fact(proposition, false);
            self.adjust_memory_separation_fact(proposition, false);
            self.adjust_nonmemory_separation_fact(proposition, false);
            self.adjust_resource_contains_fact(proposition, false);
            self.adjust_memory_effect_fact(proposition, false);
            self.content_fingerprint ^= Self::fingerprint(2, proposition);
        }
    }

    #[cfg(test)]
    pub(crate) fn disjunction_fact_count(&self) -> usize {
        self.disjunction_facts.len()
    }

    #[cfg(test)]
    pub(super) fn reset_condition_implication_antecedent_checks() {
        CONDITION_IMPLICATION_ANTECEDENT_CHECKS.with(|checks| checks.set(0));
    }

    #[cfg(test)]
    pub(super) fn condition_implication_antecedent_checks() -> usize {
        CONDITION_IMPLICATION_ANTECEDENT_CHECKS.with(Cell::get)
    }

    #[cfg(test)]
    pub(super) fn reset_memory_separation_candidate_checks() {
        MEMORY_SEPARATION_CANDIDATE_CHECKS.with(|checks| checks.set(0));
    }

    #[cfg(test)]
    pub(super) fn memory_separation_candidate_checks() -> usize {
        MEMORY_SEPARATION_CANDIDATE_CHECKS.with(Cell::get)
    }

    #[cfg(test)]
    pub(super) fn reset_memory_separation_recursive_candidate_checks() {
        MEMORY_SEPARATION_RECURSIVE_CANDIDATE_CHECKS.with(|checks| checks.set(0));
    }

    #[cfg(test)]
    pub(super) fn memory_separation_recursive_candidate_checks() -> usize {
        MEMORY_SEPARATION_RECURSIVE_CANDIDATE_CHECKS.with(Cell::get)
    }

    /// Keep repeated decisions over this borrowed fact set under one memo
    /// identity. Recursive memory resolution can ask several alias questions
    /// about the same large context; without an enclosing scope each question
    /// re-hashes the entire context before consulting the decision memo.
    pub(super) fn enter_id_scope(&self) -> PureFactContextIdScope {
        PureFactContextIdScope::enter(self)
    }

    pub fn new() -> Self {
        Self::default()
    }

    /// Whether this context's facts (`pure_facts`) are `other`'s by storage
    /// identity: the two hold one and the same condition and proposition
    /// sets, so every fact of either is exactly a fact of the other. A
    /// `false` says nothing.
    pub(crate) fn holds_the_facts_of(&self, other: &Self) -> bool {
        self.condition_facts
            .shares_root_with(&other.condition_facts)
            && self.prop_facts.ptr_eq(&other.prop_facts)
    }

    #[cfg(test)]
    pub(crate) fn shares_fact_storage_with(&self, other: &Self) -> bool {
        self.condition_facts
            .shares_root_with(&other.condition_facts)
            && self
                .signed_order_bounds
                .shares_root_with(&other.signed_order_bounds)
            && self
                .int64_signed_order_bounds
                .shares_root_with(&other.int64_signed_order_bounds)
            && self
                .uint32_order_bounds
                .shares_root_with(&other.uint32_order_bounds)
            && self
                .uint64_order_bounds
                .shares_root_with(&other.uint64_order_bounds)
            && self
                .memory_load_condition_facts
                .shares_root_with(&other.memory_load_condition_facts)
            && self.prop_facts.ptr_eq(&other.prop_facts)
            && self
                .stated_proposition_index
                .shares_storage_with(&other.stated_proposition_index)
            && self
                .equality_graph
                .admitted
                .algebraic_constructor_field_equalities
                .shares_root_with(
                    &other
                        .equality_graph
                        .admitted
                        .algebraic_constructor_field_equalities,
                )
            && self
                .algebraic_constructor_conflicts
                .shares_root_with(&other.algebraic_constructor_conflicts)
            && self
                .algebraic_variable_constructors
                .shares_root_with(&other.algebraic_variable_constructors)
            && self
                .resource_compositions
                .shares_root_with(&other.resource_compositions)
            && self
                .memory_loadable_facts
                .shares_root_with(&other.memory_loadable_facts)
            && self
                .memory_loadable_object_facts
                .shares_root_with(&other.memory_loadable_object_facts)
            && self
                .memory_loadable_shape_facts
                .shares_root_with(&other.memory_loadable_shape_facts)
            && self
                .memory_separation_facts
                .shares_root_with(&other.memory_separation_facts)
    }

    #[cfg(test)]
    pub(crate) fn memory_separation_candidate_count(
        &self,
        left: &PointerBlock,
        right: &PointerBlock,
    ) -> usize {
        self.memory_separation_candidates(left, right).count()
    }

    #[cfg(test)]
    pub(crate) fn memory_loadable_candidate_count(&self, block: &PointerBlock) -> usize {
        self.memory_loadable_candidates(block).count()
    }

    pub(crate) fn memo_fingerprint(&self) -> u64 {
        self.content_fingerprint
    }

    /// This context with `owner`, the writer's current observable
    /// composition or `None` when it has none to state, as the ownership its
    /// stores are separated by. A store writes only memory its writer owns
    /// now, so a cached cell in a different member of that ownership keeps
    /// its value; compositions stated earlier on the path are not consulted,
    /// which keeps a store's work independent of the path's length.
    pub(in crate::kernel) fn with_store_owner(self, owner: Option<ResourceContext>) -> Self {
        self.with_store_owners(owner.into_iter().collect())
    }

    /// This context with `opened`, a composition the store opened from what
    /// its writer holds now, stated and added to the store's owners. Without
    /// owners (a context no writer stated them in) it is only stated.
    pub(in crate::kernel) fn with_additional_store_owner(self, opened: ResourceContext) -> Self {
        match &self.store_owners {
            Some(owners) => {
                let mut owners = owners.as_ref().clone();
                owners.push(opened);
                self.with_store_owners(owners)
            }
            None => self.assume_proposition(Proposition::CResourceComposition(opened)),
        }
    }

    fn with_store_owners(mut self, owners: Vec<ResourceContext>) -> Self {
        for owner in &owners {
            self = self.assume_proposition(Proposition::CResourceComposition(owner.clone()));
        }
        if let Some(previous) = &self.store_owners {
            self.content_fingerprint ^= Self::fingerprint(5, previous);
        }
        let owners = std::sync::Arc::new(owners);
        self.content_fingerprint ^= Self::fingerprint(5, &owners);
        self.store_owners = Some(owners);
        self
    }

    /// The compositions the writer stated as its store owners, if it did.
    pub(in crate::kernel) fn store_owners(&self) -> Option<&[ResourceContext]> {
        self.store_owners.as_deref().map(Vec::as_slice)
    }

    /// A context holding only this context's resource compositions: what
    /// ownership alone proves, independent of any condition or other fact.
    pub(crate) fn compositions_only(&self) -> Self {
        let mut context = Self::new();
        for resources in self.resource_compositions.scan_for_upkeep() {
            context =
                context.assume_proposition(Proposition::CResourceComposition(resources.clone()));
        }
        context
    }

    /// Keep contextual loadability consequences as explicit proof obligations
    /// instead of silently discharging them while symbolic execution is being
    /// planned.
    ///
    /// Condition reasoning is unchanged: this flag only controls the
    /// obligation boundary used by the evaluator.
    pub(crate) fn defer_non_exact_loadability_obligations(self) -> Self {
        self.with_reasoning_policy(ReasoningPolicy::DEFER_NON_EXACT_LOADABILITY_OBLIGATIONS)
    }

    pub(crate) fn should_defer_non_exact_loadability_obligations(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::DEFER_NON_EXACT_LOADABILITY_OBLIGATIONS)
    }

    /// Surface-certificate synthesis uses this only to structurally lower a
    /// candidate form before comparing it with an already-certified
    /// kernel proposition. Ordinary proof checking must not enable it.
    pub(crate) fn allow_symbolic_contract_loads(self) -> Self {
        self.with_reasoning_policy(ReasoningPolicy::ALLOW_SYMBOLIC_CONTRACT_LOADS)
    }

    pub(crate) fn should_allow_symbolic_contract_loads(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::ALLOW_SYMBOLIC_CONTRACT_LOADS)
    }

    /// Evaluate a contract entry's own resource clauses. Each states what the
    /// opaque extent of its pointer covers, so it is assumed, not checked;
    /// the entry builder then records the coverage it states.
    pub(crate) fn assume_entry_clause_extents(self) -> Self {
        self.with_reasoning_policy(ReasoningPolicy::ASSUME_ENTRY_CLAUSE_EXTENTS)
    }

    pub(crate) fn should_assume_entry_clause_extents(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::ASSUME_ENTRY_CLAUSE_EXTENTS)
    }

    /// Project a held resource's body using the domains its fold established.
    /// Ordinary entry requirements and new folds keep their domain obligations.
    pub(crate) fn assume_held_resource_domains(self) -> Self {
        self.with_reasoning_policy(ReasoningPolicy::ASSUME_HELD_RESOURCE_DOMAINS)
    }

    pub(crate) fn should_assume_held_resource_domains(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::ASSUME_HELD_RESOURCE_DOMAINS)
    }

    pub(crate) fn require_owned_expression_loads(mut self) -> Self {
        if self.should_allow_symbolic_contract_loads() {
            self.toggle_reasoning_policy(ReasoningPolicy::ALLOW_SYMBOLIC_CONTRACT_LOADS);
        }
        self.with_reasoning_policy(ReasoningPolicy::REQUIRE_OWNED_EXPRESSION_LOADS)
    }

    /// An empty context with this one's reasoning policy: the context a
    /// fact-free lowering runs in (`kernel::fact_stability`).
    pub(crate) fn without_facts(&self) -> Self {
        let mut empty = Self::new();
        empty.reasoning_policy = self.reasoning_policy;
        empty
    }

    fn with_reasoning_policy(mut self, choice: ReasoningPolicy) -> Self {
        if !self.reasoning_policy.contains(choice) {
            self.toggle_reasoning_policy(choice);
        }
        self
    }

    fn toggle_reasoning_policy(&mut self, choice: ReasoningPolicy) {
        self.reasoning_policy.toggle(choice);
        self.content_fingerprint ^= choice.fingerprint();
    }

    pub(in crate::kernel) fn should_require_owned_expression_loads(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::REQUIRE_OWNED_EXPRESSION_LOADS)
    }

    pub(crate) fn transport_memory_load_condition_facts(self) -> Self {
        self.with_reasoning_policy(ReasoningPolicy::TRANSPORT_MEMORY_LOAD_CONDITION_FACTS)
    }

    pub(crate) fn should_transport_memory_load_condition_facts(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::TRANSPORT_MEMORY_LOAD_CONDITION_FACTS)
    }

    pub(crate) fn defer_non_exact_condition_reasoning(self) -> Self {
        self.with_reasoning_policy(ReasoningPolicy::DEFER_NON_EXACT_CONDITION_REASONING)
    }

    pub(super) fn should_defer_non_exact_condition_reasoning(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::DEFER_NON_EXACT_CONDITION_REASONING)
    }

    /// The pure function definitions the kernel evaluates constant
    /// applications by. A context carries one table.
    pub(crate) fn prefer_symbolic_external_loads(self) -> Self {
        self.with_reasoning_policy(ReasoningPolicy::PREFER_SYMBOLIC_EXTERNAL_LOADS)
    }

    pub(super) fn should_prefer_symbolic_external_loads(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::PREFER_SYMBOLIC_EXTERNAL_LOADS)
    }

    pub(crate) fn force_symbolic_external_loads(self) -> Self {
        self.with_reasoning_policy(ReasoningPolicy::FORCE_SYMBOLIC_EXTERNAL_LOADS)
    }

    pub(crate) fn should_force_symbolic_external_loads(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::FORCE_SYMBOLIC_EXTERNAL_LOADS)
    }

    pub(crate) fn keep_spec_loads_symbolic(self) -> Self {
        self.with_reasoning_policy(ReasoningPolicy::KEEP_SPEC_LOADS_SYMBOLIC)
    }

    pub(super) fn should_keep_spec_loads_symbolic(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::KEEP_SPEC_LOADS_SYMBOLIC)
    }

    /// What difference logic over this context's condition facts decides
    /// about `condition` (`docs/internals/verification-efficiency.md`), with `extra` facts
    /// assumed on top: a path's facts not yet in the context.
    pub(crate) fn difference_decision(
        &self,
        condition: &ConditionTerm,
        extra: &[(ConditionTerm, bool)],
    ) -> Option<bool> {
        self.fast_leaf_decision(condition, extra).or_else(|| {
            // A 64-bit word equality may relate tagged addresses
            // (`address(p) + tag`): the pointer-tag rules decide it, asking
            // only these fast decisions at their leaves.
            let ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left,
                right,
            } = condition
            else {
                return None;
            };
            let mut used = crate::kernel::eval::pointer_tags::UsedFacts::fast_only();
            self.decide_pointer_word_equality_citing(left, right, &mut used)
        })
    }

    /// The fast decisions with no search: the difference graph, asked the
    /// question and its canonical form, and the keyed pointer and division
    /// rules.
    pub(in crate::kernel) fn fast_leaf_decision(
        &self,
        condition: &ConditionTerm,
        extra: &[(ConditionTerm, bool)],
    ) -> Option<bool> {
        if matches!(
            condition,
            ConditionTerm::PointerEqual(..) | ConditionTerm::PointerOffsetEqual(..)
        ) && (self
            .equality_graph
            .admitted
            .pointer_address_sources
            .contains_key(condition)
            || self
                .equality_graph
                .admitted
                .pointer_address_sources
                .contains_key(&condition.flipped()))
        {
            return Some(true);
        }
        // Object-class annotations do not change numeric addresses. The
        // typed numeric graph shares those spellings, including disequality.
        if let ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        } = condition
            && left.address_pointer().is_some()
            && right.address_pointer().is_some()
        {
            if self.equality_graph.are_uint64_equal(left, right) {
                return Some(true);
            }
            if self.equality_graph.knows_condition(condition, false) {
                return Some(false);
            }
            if self.addresses_separated_by_class(condition) {
                return Some(false);
            }
        }
        let graph = self.difference_graph.graph(|| {
            self.condition_facts
                .scan_for_upkeep()
                .map(|(condition, value)| (condition, *value))
                .collect()
        });
        // A load in the question may be spelled as the load itself where
        // the facts name it by its load variable: its canonical form, equal
        // by definition, is asked too.
        let canonical = || {
            let canonical = crate::kernel::eval::canonical_condition(condition);
            (&canonical != condition).then_some(canonical)
        };
        // A pointer comparison the graph leaves open may still be decided
        // unequal by the keyed null-ness and separation indexes
        // (`decide_pointer_disequality`), which search nothing.
        let pointer_disequality = || match condition {
            ConditionTerm::PointerEqual(..) | ConditionTerm::PointerOffsetEqual(..) => {
                self.decide_pointer_disequality(condition)
            }
            // `left != INT_MIN or right != -1` kept whole as a fact: two
            // keyed lookups (`divide_overflow_excluded_by_disjunction`).
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Divide,
                left,
                right,
            } => self
                .divide_overflow_excluded_by_disjunction(left, right)
                .then_some(false),
            _ => None,
        };
        if extra.is_empty() {
            return graph
                .decide(condition)
                .or_else(|| canonical().and_then(|canonical| graph.decide(&canonical)))
                .or_else(pointer_disequality)
                .or_else(|| aliased_operands(graph, condition));
        }
        let mut graph = graph.clone();
        for (fact, value) in extra {
            graph.assume_condition(fact, *value);
        }
        graph
            .decide(condition)
            .or_else(|| canonical().and_then(|canonical| graph.decide(&canonical)))
            .or_else(pointer_disequality)
            .or_else(|| aliased_operands(&graph, condition))
    }

    pub(crate) fn proves_exact(&self, proposition: &Proposition) -> bool {
        if solve_builtin_prop(proposition) {
            return true;
        }
        // The read-over-write authority: a read of a stored cell is the
        // value stored there (`eval::read_over_write_value`). Consulted only
        // when the proposition does not hold as written.
        self.proves_exact_unresolved(proposition)
            || crate::kernel::eval::comparison_form(proposition).is_some_and(|resolved| {
                self.proves_exact_unresolved(&resolved)
                    || crate::kernel::proof::fact_reasoning::normalizes_context_free_leaf(&resolved)
            })
    }

    fn proves_exact_unresolved(&self, proposition: &Proposition) -> bool {
        if solve_builtin_prop(proposition) {
            return true;
        }
        // An exact full-pointer premise directly supplies its numeric
        // equality. Retain the actual source premise for proof reconstruction; this
        // projection never runs in the reverse direction.
        if let Proposition::ConditionIs(
            condition @ (ConditionTerm::PointerEqual(..) | ConditionTerm::PointerOffsetEqual(..)),
            true,
        ) = proposition
            && let Some(source) = self
                .equality_graph
                .admitted
                .pointer_address_sources
                .get(condition)
                .or_else(|| {
                    self.equality_graph
                        .admitted
                        .pointer_address_sources
                        .get(&condition.flipped())
                })
                .and_then(|sources| sources.iter().next())
        {
            record_implicit_reasoning_provenance(
                self,
                &Proposition::ConditionIs(source.clone(), true),
            );
            return true;
        }
        let proved = self.contains_assumed_exact(proposition);
        if proved {
            record_implicit_reasoning_provenance(self, proposition);
        }
        proved
    }

    /// Exact membership in the explicitly assumed fact set, without builtin
    /// solving or proof-provenance side effects. This is the indexed analogue
    /// of searching an ambient proposition slice for an atomic conjunct.
    pub(crate) fn contains_assumed_exact(&self, proposition: &Proposition) -> bool {
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                self.condition_facts.get(condition) == Some(value)
                    || self.prop_facts.contains(proposition)
            }
            Proposition::And(left, right) => {
                self.contains_assumed_exact(left) && self.contains_assumed_exact(right)
            }
            Proposition::CResourceComposition(resources) => {
                self.resource_compositions.contains(resources)
            }
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(condition, value) => {
                    self.condition_facts.get(condition) == Some(&!*value)
                }
                _ => self.prop_facts.contains(proposition),
            },
            _ => self.prop_facts.contains(proposition),
        }
    }

    /// Semantic availability through the shared scoped equality graph and
    /// indexed stated separation and exact native Integer observations.
    /// Exact membership remains separate for
    /// provenance, admission, and withdrawal.
    /// This performs no unfolding, implication search, or snapshot transport.
    pub(crate) fn contains_known(&self, proposition: &Proposition) -> bool {
        // An indexed conflict among checked scalar equalities makes this
        // scoped context impossible. Its semantic consequences need no new
        // search or materialized negation; exact membership stays unchanged.
        if self.equality_graph.has_scalar_constant_conflict() {
            return true;
        }
        // Logical structure is handled by the proof rule. Do not repeatedly
        // traverse a whole conjunction while its caller visits its leaves.
        if matches!(proposition, Proposition::And(..) | Proposition::Or(..)) {
            return self.prop_facts.contains(proposition);
        }
        if self.contains_assumed_exact(proposition) {
            return true;
        }
        match proposition {
            Proposition::Equal(
                Term::CValue(CValue::Pointer(left)),
                Term::CValue(CValue::Pointer(right)),
            ) => {
                self.equality_graph
                    .admitted
                    .pointer_value_classes
                    .equal(left, right)
                    || (self.designations_equal(left.designation(), right.designation())
                        && left.extent() == right.extent()
                        && self.pointers_known_equal(left.pointer(), right.pointer()))
            }
            Proposition::Equal(Term::Algebraic(a), Term::Algebraic(b)) => {
                self.equality_graph.are_algebraic_equal(a, b)
            }
            Proposition::Predicate { .. } => {
                self.equality_graph.knows_pointer_predicate(proposition)
            }
            Proposition::ConditionIs(condition @ ConditionTerm::PointerValueEqual(..), value) => {
                self.decide(condition) == Some(*value)
            }
            Proposition::ConditionIs(condition, value) => {
                self.knows_condition_or_stated_separation(condition, *value)
            }
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(condition, value) => {
                    self.knows_condition_or_stated_separation(condition, !*value)
                }
                _ => false,
            },
            _ => false,
        }
    }

    fn knows_condition_or_stated_separation(&self, condition: &ConditionTerm, value: bool) -> bool {
        self.equality_graph.knows_condition(condition, value)
            // A 32-bit order claim in its mirrored direction (`255 >= x` for
            // `x <= 255`): the graph keeps each order condition in the
            // direction it was stated, and a widening's class holds its
            // operand (rule K8, a relation), so the stated direction over
            // the operand answers the mirrored one over the widening. One
            // more lookup.
            || mirrored_order32(condition)
                .is_some_and(|mirrored| self.equality_graph.knows_condition(&mirrored, value))
            // A signedness conversion's sign test is known when its
            // operand's half-range test is, and the reverse
            // (`condition_reasoning::sign_bit`).
            || self
                .sign_bit_equivalent_conditions(condition)
                .into_iter()
                .any(|equivalent| {
                    Self::without_sign_bit_rule(|| {
                        self.equality_graph.knows_condition(&equivalent, value)
                    })
                })
            || (!value && self.addresses_separated_by_class(condition))
            || native_comparison_of_integer_observation(condition, value).is_some_and(
                |(native, truth)| self.contains_known(&Proposition::ConditionIs(native, truth)),
            )
    }

    pub(in crate::kernel) fn addresses_separated_by_class(
        &self,
        condition: &ConditionTerm,
    ) -> bool {
        // Preserve the direct anchor lookup. Only an alias-dependent query
        // needs to register a condition application in the shared classes.
        if self.stated_pointer_disequality(condition) == Some(false) {
            return true;
        }
        let Some(source) = self.equality_graph.address_separation_source(condition) else {
            return false;
        };
        record_implicit_reasoning_provenance(self, &source);
        true
    }

    /// This context extended by `condition == value`, charged one unit of
    /// deterministic work: every fact a context is built from is charged
    /// once, so a caller that rebuilds a context from a growing list per
    /// item shows as quadratic work rather than hiding in wall time.
    pub fn assume_condition(self, condition: ConditionTerm, value: bool) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        self.assume_condition_uncharged(condition, value)
    }

    fn assume_condition_uncharged(self, condition: ConditionTerm, value: bool) -> Self {
        let (decided, reduced) = if self.condition_facts.get(&condition) == Some(&value) {
            (None, None)
        } else {
            let proposition = Proposition::ConditionIs(condition.clone(), value);
            let decided = match &condition {
                ConditionTerm::AlgebraicEqual(left, right) if value => {
                    decided_algebraic_if(&Proposition::Equal(
                        Term::Algebraic(left.as_ref().clone()),
                        Term::Algebraic(right.as_ref().clone()),
                    ))
                }
                _ => None,
            };
            (decided, self.reduce_by_decided_conditions(&proposition))
        };
        // An 8- or 16-bit signedness conversion's sign test, which names a
        // cast no plain comparison of its operand does, also files its
        // operand's half-range test, and the reverse
        // (`condition_reasoning::sign_bit`). A 32- or 64-bit one needs no
        // filing: both tests compare one word, and a lookup of either finds
        // the other.
        let sign_bit_equivalents = if condition.names_narrow_signedness_cast()
            && self.condition_facts.get(&condition) != Some(&value)
        {
            self.sign_bit_equivalent_conditions(&condition)
        } else {
            Vec::new()
        };
        let mut next = self.assume_condition_once(condition, value);
        if !sign_bit_equivalents.is_empty() {
            next = Self::without_sign_bit_rule(|| {
                sign_bit_equivalents
                    .into_iter()
                    .filter(|equivalent| !matches!(equivalent, ConditionTerm::Constant(_)))
                    .fold(next, |next, equivalent| {
                        next.assume_condition_once(equivalent, value)
                    })
            });
        }
        if let Some((condition, value, selected)) = decided {
            next = next.assume_decided_algebraic_if(condition, value, selected);
        }
        if let Some(reduced) = reduced {
            next = next.assume_proposition_uncharged(reduced);
        }
        next
    }

    /// A repeated assumption is either redundant or immediately contradictory.
    /// Keep the first condition entry and all its indexes. Record contradiction
    /// as an ordinary false proposition, so retained premises and reconstruction
    /// preserve it without needing a hidden flag or an index rebuild. The
    /// proposition set is distinct from the condition map: even a prior
    /// `false == false` fact must not be replaced to record falsehood.
    fn restates_condition(&mut self, condition: &ConditionTerm, value: bool) -> bool {
        let Some(known) = self.condition_facts.get(condition).copied() else {
            return false;
        };
        if known != value {
            self.insert_proposition_fact(Proposition::ConditionIs(
                ConditionTerm::Constant(false),
                true,
            ));
        }
        true
    }

    fn assume_condition_once(mut self, condition: ConditionTerm, value: bool) -> Self {
        // Proof branches frequently restate a path fact (for example while
        // lowering the consequent of an implication). Preserve the shared
        // persistent view on that idempotent insertion: `Arc::make_mut`
        // would otherwise clone the complete fact map and every derived
        // index before discovering that nothing changed.
        if self.restates_condition(&condition, value) {
            return self;
        }
        #[cfg(test)]
        let pointer_predecessor =
            (value && matches!(condition, ConditionTerm::PointerValueEqual(..))).then(|| {
                (
                    std::sync::Arc::new(condition.clone()),
                    std::sync::Arc::new(self.equality_graph.clone()),
                )
            });
        crate::kernel::eval::check_canonical_at_creation(&condition, value);
        crate::kernel::debug_assert_widths(
            "an assumed condition",
            || crate::kernel::condition_narrow_violation(&condition),
            &condition,
        );
        if cfg!(debug_assertions) {
            let widths = &mut self.variable_widths;
            crate::kernel::debug_assert_widths(
                "an assumed condition",
                || match crate::kernel::condition_variable_widths(&condition) {
                    Err(mismatch) => Some(mismatch),
                    Ok(used) => {
                        used.into_iter()
                            .find_map(|(variable, width)| match widths.get(&variable) {
                                Some(&first) if first != width => {
                                    Some(crate::kernel::variable_conflict(first, width))
                                }
                                Some(_) => None,
                                None => {
                                    widths.insert(variable, width);
                                    None
                                }
                            })
                    }
                },
                &condition,
            );
        }
        if let ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        } = &condition
            && let Some((left, right)) = bitvector_equality_after_additive_cancellation(left, right)
        {
            self = self.assume_condition_uncharged(ConditionTerm::equal(left, right), value);
        }
        // An equality naming a C narrowing conversion whose operand this
        // context already places inside the destination range also files the
        // conversion's identity with its operand (`narrowed_cast_identity`),
        // so equality reasoning relates `x == conv(y)` to `x == y`. One
        // memoized decision per bound of each converted side; nothing else
        // in the context is visited.
        if value
            && let ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            } = &condition
        {
            for side in [left.as_ref(), right.as_ref()] {
                if matches!(side, Bitvector32Term::MachineIntegerCast { .. })
                    && let Some(carrier) = self.narrowed_cast_carrier(side)
                {
                    let identity = ConditionTerm::equal(side.clone(), carrier);
                    if identity != condition {
                        self = self.assume_condition_uncharged(identity, true);
                    }
                }
            }
        }
        // A fact that reads a stored cell also files its form over the value
        // stored there (the read-over-write authority,
        // `eval::read_over_write_value`), as a narrowing above files its
        // carrier: one bounded rewrite of this fact, nothing else visited.
        if let Some(Proposition::ConditionIs(resolved, resolved_value)) =
            crate::kernel::eval::comparison_form(&Proposition::ConditionIs(
                condition.clone(),
                value,
            ))
            && resolved != condition
        {
            self = self.assume_condition_uncharged(resolved, resolved_value);
        }
        // The graph derives a same-block comparison's offset view. Do not
        // publish it as an independent premise: it must disappear when the
        // original pointer comparison is withdrawn.
        // An unsigned upper bound below the sign bit, the `uint32` order
        // `x <u c` with `c <= 2^31`, holds exactly when the signed pair
        // `0 <= x` and `x < c` does, so the pair is filed beside it, with the
        // source's strictness: every reader of signed order facts on `x`
        // (interval, index range, and element-membership rules) then sees
        // the range the unsigned test established, through the same indexes
        // it reads for a signed test. Two facts per bound, both on the
        // bounded term itself.
        //
        // A sixty-four-bit `x <u c` with `c <= 2^31` files the same pair on
        // the low word `(uint32)x`, which is `x` itself, and the sign-bit
        // bound `x <=u INT_MAX` that checked range projection asks for by key.
        if let Some((term, bound, strict)) =
            condition_reasoning::unsigned_upper_bound_below_sign_bit(&condition, value)
        {
            // A 32-bit widening of a narrow value has its operand's word
            // (rule K8, a relation), so the range is filed on the operand.
            let term = term
                .narrow_widening32_operand()
                .map_or(term, |(_, operand)| operand);
            self = self.assume_unsigned_word_range(term.clone(), bound, strict);
        } else if let Some((term, bound, strict)) =
            condition_reasoning::uint64_upper_bound_below_sign_bit(&condition, value)
        {
            let term = term.clone();
            let sign_bit_clear = ConditionTerm::uint64_less_equal(
                term.clone(),
                Bitvector32Term::UInt64Constant(i32::MAX as u64),
            );
            if sign_bit_clear != condition {
                self = self.assume_condition_uncharged(sign_bit_clear, true);
            }
            self = self.assume_unsigned_word_range(
                Bitvector32Term::uint32_from_64(term),
                bound,
                strict,
            );
        }
        // An Integer comparison of exact machine observations,
        // `to_integer(x) <= 5` or `to_integer(x) == to_integer(y)` for one
        // machine type, holds exactly when the native comparison of the
        // carriers does, since `to_integer` is injective and preserves
        // order. The native comparison is filed beside it, so built-in
        // checks that read machine facts (resource quantities, overflow
        // and definedness) see what an Integer premise established. One
        // constant check per filed comparison; nothing else is visited.
        if let Some((native, truth)) = native_comparison_of_integer_observation(&condition, value)
            && native != condition
        {
            self = self.assume_condition_uncharged(native, truth);
        } else if let Some(wrapped) = wrapped_equality_of_integer_equality(&condition, value) {
            self = self.assume_condition_uncharged(wrapped, true);
        }
        // The same rule through an in-range machine `+` or `-`: an Integer
        // comparison whose side is the exact value of such an operation,
        // `to_integer(a) <= 4294967295 - to_integer(b)` on `uint32`, holds
        // exactly when the native comparison of the operation does
        // (`a <= 4294967295u32 - b`), once the operation's result lies in
        // its type. A range bound the operands' types do not already imply
        // must be a fact here (`IntegerOperationRangeBound`). At most two
        // sides and two bounds of three spellings each are looked up.
        else if let Some((native, truth, bounds)) =
            native_comparison_through_integer_operations(&condition, value)
            && native != condition
            && bounds.iter().all(|bound| {
                bound
                    .stating_facts()
                    .iter()
                    .any(|fact| self.contains_known(fact))
            })
        {
            self = self.assume_condition_uncharged(native, truth);
        }
        // A signed definedness fact holds exactly when both Integer bounds
        // of its exact result do (`integer_bounds_of_definedness`). When
        // this fact is one bound and the other is already known, the
        // definedness fact is filed beside it, so the built-in overflow
        // check reads what the two Integer premises established. One
        // lookup of two spellings.
        if value
            && let Some(Proposition::ConditionIs(overflow, false)) = definedness_of_integer_bound(
                &Proposition::ConditionIs(canonical_integer_bound_spelling(&condition), true),
            )
            && self.condition_facts.get(&overflow) != Some(&false)
            && integer_bounds_of_definedness(&Proposition::ConditionIs(overflow.clone(), false))
                .iter()
                .all(|bound| match bound {
                    Proposition::ConditionIs(bound, true) => {
                        *bound == canonical_integer_bound_spelling(&condition)
                            || integer_order_spellings(bound).into_iter().any(|spelling| {
                                self.contains_known(&Proposition::ConditionIs(spelling, true))
                            })
                    }
                    _ => false,
                })
        {
            self = self.assume_condition_uncharged(overflow, false);
        }
        // Filing derived facts above can itself establish this condition.
        // Apply the same monotone rule before committing the original entry.
        if self.restates_condition(&condition, value) {
            return self;
        }
        self.execution_variable_ceiling.file_condition(&condition);
        self.condition_facts = self.condition_facts.with_inserted(condition.clone(), value);
        self.execution_fact_projection.insert(
            ContextFactKey::Condition(condition.clone()),
            std::sync::Arc::new(ExecutionPureFact::new(Proposition::ConditionIs(
                condition.clone(),
                value,
            ))),
        );
        self.adjust_pointer_class_fact(&Proposition::ConditionIs(condition.clone(), value), true);
        self.adjust_memory_load_condition_index(&condition, true);
        self.adjust_stated_proposition_index(
            &Proposition::ConditionIs(condition.clone(), value),
            true,
        );
        self.adjust_signed_order_bound(&condition, value, true);
        self.adjust_null_pointer_offset(&condition, value, true);
        self.adjust_pointer_block_alias(&condition, value, true);
        self.adjust_pointer_offset_alias(&condition, value, true);
        self.adjust_int32_graph_equality(&condition, value, true);
        self.adjust_uint64_graph_equality(&condition, value, true);
        self.adjust_algebraic_graph_equality(
            &Proposition::ConditionIs(condition.clone(), value),
            true,
        );
        if value
            && matches!(
                condition,
                ConditionTerm::PointerEqual(..) | ConditionTerm::PointerValueEqual(..)
            )
        {
            self.composition_object_resources
                .advance_memory_equalities(&self);
        }
        self.adjust_scalar_evidence_input(&condition, value, true);
        self.adjust_bitvector64_equality(&condition, value, true);
        self.adjust_exact_constant_equality(&condition, value, true);

        self.adjust_condition_match_indexes(&condition, value, true);
        if self.equality_graph.add_condition(&condition, value) {
            self.equality_graph
                .admitted
                .congruence_conditions
                .insert(condition.clone(), value);
        }
        // A `Bool` value's binders take the truths their own facts gave them
        // (rule L-Eq): those facts may predate the value's classes.
        if condition.is_bool_value_form() {
            self.admit_bool_binder_truths(&condition);
        }
        self.content_fingerprint ^= Self::fingerprint(1, &(condition, value));
        #[cfg(test)]
        if let Some((source, graph)) = pointer_predecessor {
            self.pointer_value_undo = Some(std::sync::Arc::new(PointerValueUndo {
                source,
                graph,
                conditions: self.condition_facts.clone(),
                propositions: self.prop_facts.clone(),
            }));
        }
        self
    }

    /// Admit, for each binder directly under a `Bool` value's conditionals
    /// and equalities, its own filed truth into the e-graph, where an L-Eq
    /// merge can carry it. One indexed lookup per binder of the value.
    fn admit_bool_binder_truths(&mut self, condition: &ConditionTerm) {
        let mut pending = vec![condition];
        while let Some(condition) = pending.pop() {
            match condition {
                ConditionTerm::Variable(_) => {
                    if let Some(value) = self.condition_facts.get(condition).copied()
                        && self.equality_graph.add_condition(condition, value)
                    {
                        self.equality_graph
                            .admitted
                            .congruence_conditions
                            .insert(condition.clone(), value);
                    }
                }
                condition => pending.extend(condition.bool_children()),
            }
        }
    }

    /// Files the signed range of a word an unsigned upper bound below the sign
    /// bit established: `0 <= term`, and `term < bound + 1` (strict source)
    /// or `term <= bound`.
    fn assume_unsigned_word_range(
        mut self,
        term: Bitvector32Term,
        bound: u32,
        strict: bool,
    ) -> Self {
        self = self.assume_condition_uncharged(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), term.clone()),
            true,
        );
        // A bound of `INT_MAX` says nothing every signed word does not.
        if bound == i32::MAX as u32 {
            self
        } else if strict {
            self.assume_condition_uncharged(
                ConditionTerm::signed_less_than(term, Bitvector32Term::Constant(bound + 1)),
                true,
            )
        } else {
            self.assume_condition_uncharged(
                ConditionTerm::signed_less_equal(term, Bitvector32Term::Constant(bound)),
                true,
            )
        }
    }

    /// This context extended by `proposition`, charged one unit of
    /// deterministic work (see [`Self::assume_condition`]).
    /// At least the greatest execution-range variable any of these facts
    /// mentions; see `ExecutionVariableCeiling`.
    pub(in crate::kernel) fn execution_variable_ceiling(&self) -> Option<Variable> {
        self.execution_variable_ceiling.get()
    }

    pub fn assume_proposition(self, proposition: Proposition) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        self.assume_proposition_uncharged(proposition)
    }

    /// [`Self::assume_proposition`] without its charge, for a context build
    /// that is a known violation of the complexity contract
    /// (`docs/internals/verification-efficiency.md`) and whose charge would
    /// fail a scaling regression until its representation changes. Every
    /// caller names the violation it carries.
    pub(crate) fn assume_proposition_uncharged(mut self, proposition: Proposition) -> Self {
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                self = self.assume_condition_uncharged(condition, value);
            }
            Proposition::And(left, right) => {
                self = self.assume_proposition_uncharged(*left);
                self = self.assume_proposition_uncharged(*right);
            }
            Proposition::Not(body) => match *body {
                Proposition::ConditionIs(condition, value) => {
                    self = self.assume_condition_uncharged(condition, !value);
                }
                body => {
                    self.insert_proposition_fact(Proposition::Not(Box::new(body)));
                }
            },
            proposition => {
                let decided = decided_algebraic_if(&proposition);
                let reduced = self.reduce_by_decided_conditions(&proposition);
                let native = self.native_antecedent_reading(&proposition);
                self.insert_proposition_fact(proposition);
                if let Some(native) = native {
                    self.insert_proposition_fact(native);
                }
                if let Some((condition, value, selected)) = decided {
                    self = self.assume_decided_algebraic_if(condition, value, selected);
                }
                if let Some(reduced) = reduced {
                    self = self.assume_proposition_uncharged(reduced);
                }
            }
        }
        self
    }

    /// A quantified fact `forall k { A(k) implies B(k) }` whose antecedent
    /// compares the Integer value of an in-range machine `+` or `-`, such as
    /// `to_integer(k) < to_integer(len) + 1`, filed again with that
    /// comparison read natively, `k < len + 1u64`, as a top-level fact is
    /// ([`native_comparison_through_integer_operations`]). The two
    /// antecedents agree once each operation's result lies in its type, so a
    /// range bound the operand types do not imply must already be a fact, and
    /// it may not name the bound variable. Built-in checks that match a
    /// definition's quantified body fact exactly, such as assembling
    /// `cstr_at(p, len)`, then see what a specification stated with Integer
    /// arithmetic. The work is the antecedent's conjuncts, each one shape
    /// match and at most a few exact lookups.
    fn native_antecedent_reading(&self, proposition: &Proposition) -> Option<Proposition> {
        let Proposition::ForAll {
            var,
            sort,
            body,
            name,
        } = proposition
        else {
            return None;
        };
        let Proposition::Implies(antecedent, consequent) = body.as_ref() else {
            return None;
        };
        let native = self.native_conjunct_reading(antecedent, *var)?;
        Some(Proposition::ForAll {
            var: *var,
            sort: sort.clone(),
            body: Box::new(Proposition::Implies(Box::new(native), consequent.clone())),
            name: name.clone(),
        })
    }

    /// The native reading of each conjunct of `antecedent` that has one, or
    /// `None` when no conjunct changes.
    fn native_conjunct_reading(
        &self,
        antecedent: &Proposition,
        var: Variable,
    ) -> Option<Proposition> {
        match antecedent {
            Proposition::And(left, right) => {
                let (native_left, native_right) = (
                    self.native_conjunct_reading(left, var),
                    self.native_conjunct_reading(right, var),
                );
                if native_left.is_none() && native_right.is_none() {
                    return None;
                }
                Some(Proposition::And(
                    Box::new(native_left.unwrap_or_else(|| left.as_ref().clone())),
                    Box::new(native_right.unwrap_or_else(|| right.as_ref().clone())),
                ))
            }
            Proposition::ConditionIs(condition, value) => {
                crate::instrumentation::record_deterministic_work(1);
                let (native, truth, bounds) =
                    native_comparison_through_integer_operations(condition, *value)?;
                (native != *condition
                    && bounds.iter().all(|bound| {
                        let facts = bound.stating_facts();
                        let mut variables = std::collections::BTreeSet::new();
                        for fact in &facts {
                            crate::kernel::reasoning::variable_collection::collect_proposition_capture_variables(
                                fact,
                                &mut variables,
                            );
                        }
                        !variables.contains(&var) && facts.iter().any(|fact| self.contains_known(fact))
                    }))
                .then(|| Proposition::ConditionIs(native, truth))
            }
            _ => None,
        }
    }

    /// What [`decided_algebraic_if`] found: the condition at its value and
    /// the remaining branch's equality, with that equality's field equalities
    /// when both sides apply one constructor, as constructor injectivity
    /// gives them.
    fn assume_decided_algebraic_if(
        mut self,
        condition: ConditionTerm,
        value: bool,
        selected: Proposition,
    ) -> Self {
        self.decided_algebraic_ifs = true;
        self = self.assume_condition_uncharged(condition, value);
        let fields = algebraic_constructor_field_equalities(&selected);
        self = self.assume_proposition_uncharged(selected);
        for field in fields.into_iter().flatten() {
            self = self.assume_proposition_uncharged(field);
        }
        self
    }

    /// `proposition` with each conditional whose condition an algebraic
    /// `if` equation decided here replaced by the branch it selects; `None`
    /// when no such equation was assumed or nothing changes. Only the
    /// proposition's own conditions are looked up.
    fn reduce_by_decided_conditions(&self, proposition: &Proposition) -> Option<Proposition> {
        if !self.decided_algebraic_ifs {
            return None;
        }
        let decided =
            crate::kernel::proof::term_rewrite::TermRewrite::conditional_guards(proposition)
                .into_iter()
                .filter_map(|condition| {
                    let value = *self.condition_facts.get(&condition)?;
                    Some((condition, value))
                })
                .collect::<std::collections::HashMap<_, _>>();
        if decided.is_empty() {
            return None;
        }
        let reduced = crate::kernel::proof::term_rewrite::TermRewrite::for_conditions(&decided)
            .proposition(proposition);
        (&reduced != proposition).then_some(reduced)
    }

    pub fn pure_facts(&self) -> Vec<Proposition> {
        let mut facts = self
            .condition_facts
            .scan_for_upkeep()
            .map(|(condition, value)| Proposition::ConditionIs(condition.clone(), *value))
            .collect::<Vec<_>>();
        facts.extend(self.prop_facts.scan_for_upkeep().cloned());
        facts
    }

    fn adjust_atomic_connection_fact(&mut self, proposition: &Proposition, insert: bool) {
        let _timing =
            crate::instrumentation::OperationTiming::new("", "", "atomic dependency indexing");
        let all_keys =
            crate::kernel::reasoning::variable_collection::collect_atomic_connection_keys(
                proposition,
            );
        let mut keys = all_keys.clone();
        let mut covered_variables = 0;
        if let Proposition::ConditionIs(condition, _) = proposition {
            let has_variables = all_keys
                .iter()
                .any(|key| matches!(key, AtomicConnectionKey::Variable(_)));
            let mut indexed_variables = BTreeSet::new();
            let deferred = super::reasoning::variable_collection::collect_condition_index_variables(
                condition,
                &mut indexed_variables,
            );
            let covered = all_keys
                .iter()
                .filter_map(|key| match key {
                    AtomicConnectionKey::Variable(variable)
                        if !deferred && indexed_variables.contains(variable) =>
                    {
                        Some(*variable)
                    }
                    _ => None,
                })
                .collect::<BTreeSet<_>>();
            covered_variables = covered.len();
            keys.retain(|key| match key {
                AtomicConnectionKey::Variable(variable) => !covered.contains(variable),
                // Snapshot equations can define a load named by its address,
                // so retain their reverse address-block adjacency as well.
                // Scalar facts reuse their existing value-variable index.
                AtomicConnectionKey::Block(_) => !has_variables || covered.is_empty(),
            });
        }
        // Filing already charges the first entry. Existing scalar adjacency
        // covers its variables; charge only genuinely additional syntax keys.
        let extra_work = if covered_variables > 0 {
            keys.len()
        } else {
            keys.len().saturating_sub(1)
        };
        crate::instrumentation::record_deterministic_work(extra_work);
        let shared = SharedIndexFact::new(proposition.clone());
        if all_keys.is_empty() {
            self.atomic_ground_facts = if insert {
                self.atomic_ground_facts.with_value(shared.clone())
            } else {
                self.atomic_ground_facts.without_value(&shared)
            };
        }
        for key in keys {
            let mut bucket = self
                .atomic_connection_facts
                .get(&key)
                .cloned()
                .unwrap_or_default();
            let facts = if matches!(proposition, Proposition::ConditionIs(..)) {
                &mut bucket.conditions
            } else {
                &mut bucket.propositions
            };
            *facts = if insert {
                facts.with_value(shared.clone())
            } else {
                facts.without_value(&shared)
            };
            if matches!(proposition, Proposition::Or(..)) {
                bucket.disjunctions = if insert {
                    bucket.disjunctions.with_value(shared.clone())
                } else {
                    bucket.disjunctions.without_value(&shared)
                };
            }
            self.atomic_connection_facts =
                if bucket.conditions.is_empty() && bucket.propositions.is_empty() {
                    self.atomic_connection_facts.without_key(&key)
                } else {
                    self.atomic_connection_facts.with_inserted(key, bucket)
                };
        }
        if matches!(proposition, Proposition::ForAll { .. }) {
            self.atomic_quantified_facts = if insert {
                self.atomic_quantified_facts.with_value(shared.clone())
            } else {
                self.atomic_quantified_facts.without_value(&shared)
            };
            for key in UniversalConclusionKey::of(proposition) {
                crate::instrumentation::record_deterministic_work(1);
                let bucket = self
                    .universals_by_conclusion
                    .get(&key)
                    .cloned()
                    .unwrap_or_default();
                let bucket = if insert {
                    bucket.with_value(shared.clone())
                } else {
                    bucket.without_value(&shared)
                };
                self.universals_by_conclusion = if bucket.is_empty() {
                    self.universals_by_conclusion.without_key(&key)
                } else {
                    self.universals_by_conclusion.with_inserted(key, bucket)
                };
            }
        }
    }

    /// The universal facts whose conclusion takes the shape `key`, in
    /// `atomic_quantified_facts` order, so a `find` picks the fact a scan
    /// of every universal would.
    pub(in crate::kernel) fn universals_concluding(
        &self,
        key: UniversalConclusionKey,
    ) -> impl Iterator<Item = &Proposition> {
        crate::instrumentation::record_deterministic_work(1);
        self.universals_by_conclusion
            .get(&key)
            .into_iter()
            .flat_map(crate::persistent::PersistentSet::iter)
            .map(|fact| {
                crate::instrumentation::record_deterministic_work(1);
                fact.as_ref()
            })
    }

    fn rebuild_atomic_connection_facts(&mut self) {
        self.atomic_connection_facts = crate::persistent::PersistentMap::default();
        self.atomic_ground_facts = crate::kernel::fact_collections::ScanSet::default();
        self.atomic_quantified_facts = crate::kernel::fact_collections::ScanSet::default();
        self.universals_by_conclusion = crate::persistent::PersistentMap::default();
        let conditions = self.condition_facts.clone();
        for (condition, value) in conditions.scan_for_upkeep() {
            self.adjust_atomic_connection_fact(
                &Proposition::ConditionIs(condition.clone(), *value),
                true,
            );
        }
        let propositions = self.prop_facts.clone();
        for proposition in propositions.scan_for_upkeep() {
            self.adjust_atomic_connection_fact(proposition, true);
        }
    }

    pub(crate) fn atomic_facts_connected_to(
        &self,
        key: &AtomicConnectionKey,
        include_propositions: bool,
    ) -> (impl Iterator<Item = AtomicConnectedFact<'_>>, bool) {
        let scalar = match key {
            AtomicConnectionKey::Variable(variable) => {
                self.condition_facts_by_variable.get(variable)
            }
            AtomicConnectionKey::Block(_) => None,
        };
        let scalar = scalar.into_iter().flat_map(|facts| {
            facts.iter().map(|(condition, value)| {
                AtomicConnectedFact::Condition(condition.as_ref(), *value)
            })
        });
        let bucket = self.atomic_connection_facts.get(key);
        let has_propositions = bucket.is_some_and(|bucket| !bucket.propositions.is_empty());
        let conditions = bucket.map(|bucket| &bucket.conditions);
        let propositions = include_propositions
            .then(|| bucket.map(|bucket| &bucket.propositions))
            .flatten();
        (
            scalar.chain(
                conditions
                    .into_iter()
                    .chain(propositions)
                    .flat_map(crate::persistent::PersistentSet::iter)
                    .map(|fact| AtomicConnectedFact::Proposition(fact.as_ref())),
            ),
            has_propositions,
        )
    }

    /// Only stated disjunctions in this operand's existing dependency bucket.
    /// Logical projection does not visit unrelated scalar or predicate facts.
    pub(crate) fn disjunctions_connected_to(
        &self,
        key: &AtomicConnectionKey,
    ) -> impl Iterator<Item = &Proposition> {
        self.atomic_connection_facts
            .get(key)
            .into_iter()
            .flat_map(|bucket| bucket.disjunctions.iter())
            .map(SharedIndexFact::as_ref)
    }

    /// Constant-time cardinalities for a selection drawn from these fact sets.
    pub(crate) fn fact_counts(&self) -> (usize, usize) {
        (self.condition_facts.len(), self.prop_facts.len())
    }

    /// The atomic ground and universal facts, for the planner's premise
    /// search.
    pub(crate) fn atomic_general_facts(
        &self,
        permission: crate::SearchPermission,
    ) -> impl Iterator<Item = &Proposition> {
        self.atomic_ground_facts
            .scan_for_search(&permission)
            .chain(self.atomic_quantified_facts.scan_for_search(&permission))
            .map(SharedIndexFact::as_ref)
    }

    /// The condition facts of this context, in the index's own order.
    ///
    /// This is a read-only view for a planner outside the kernel: it names
    /// what is available without exposing the index that stores it.
    #[cfg(test)]
    pub(crate) fn condition_fact_pairs(
        &self,
        permission: crate::SearchPermission,
    ) -> impl Iterator<Item = (&ConditionTerm, bool)> {
        self.condition_facts
            .scan_for_search(&permission)
            .map(|(condition, value)| (condition, *value))
    }

    /// Read-only variable adjacency for smart premise planning. Snapshot
    /// facts are indexed once on demand; this is necessary because a fact
    /// can connect to the goal through a variable stored in its snapshot,
    /// even when their written syntax shares no variable. The kernel still
    /// checks every retained premise and the resulting atomic evidence.
    pub fn condition_facts_mentioning_variable(
        &self,
        variable: Variable,
    ) -> Option<impl Iterator<Item = (&ConditionTerm, bool)>> {
        let snapshot_index = if let Some(index) = self.snapshot_condition_variables.get() {
            index
        } else {
            let _timing = crate::instrumentation::OperationTiming::new(
                "",
                "",
                "snapshot condition premise indexing",
            );
            let mut index = self.snapshot_condition_variable_base.clone();
            for (condition, value) in self.snapshot_condition_variable_changes.iter() {
                if reasoning_interrupted() {
                    return None;
                }
                let mut variables = BTreeSet::new();
                collect_condition_bitvector_variables(condition, &mut variables);
                let indexed = SharedIndexFact::new(condition.clone());
                for variable in variables {
                    crate::instrumentation::record_deterministic_work(1);
                    let facts = index.get(&variable).cloned().unwrap_or_default();
                    let facts = if let Some(value) = value {
                        facts.with_inserted(indexed.clone(), *value)
                    } else {
                        facts.without_key(&indexed)
                    };
                    index = if facts.is_empty() {
                        index.without_key(&variable)
                    } else {
                        index.with_inserted(variable, facts)
                    };
                }
            }
            if reasoning_interrupted() {
                return None;
            }
            let _ = self.snapshot_condition_variables.set(index);
            self.snapshot_condition_variables.get()?
        };
        Some(
            self.condition_facts_by_variable
                .get(&variable)
                .into_iter()
                .flat_map(|facts| facts.iter())
                .chain(
                    snapshot_index
                        .get(&variable)
                        .into_iter()
                        .flat_map(|facts| facts.iter()),
                )
                .map(|(condition, value)| (condition.as_ref(), *value)),
        )
    }

    /// The proposition facts of this context, in the index's own order.
    pub(crate) fn proposition_facts(
        &self,
        permission: crate::SearchPermission,
    ) -> impl Iterator<Item = &Proposition> {
        self.prop_facts.scan_for_search(&permission)
    }

    /// A bounded sample and the total cardinality, in condition-then-proposition
    /// index order. At most 32 facts are visited or cloned, regardless of the
    /// requested sizes. Entries shared by the prefix and suffix appear once.
    pub(crate) fn diagnostic_fact_sample(
        &self,
        first: usize,
        last: usize,
    ) -> (Vec<Proposition>, usize) {
        let first = first.min(crate::kernel::fact_collections::DIAGNOSTIC_FACT_LIMIT);
        let last = last.min(crate::kernel::fact_collections::DIAGNOSTIC_FACT_LIMIT - first);
        let (conditions, propositions) = self.fact_counts();
        let first_conditions = first.min(conditions);
        let first_propositions = (first - first_conditions).min(propositions);
        let last_propositions = last.min(propositions - first_propositions);
        let last_conditions = (last - last_propositions).min(conditions - first_conditions);
        let facts = self
            .condition_facts
            .diagnostic_sample(first_conditions, last_conditions)
            .into_iter()
            .map(|(condition, value)| Proposition::ConditionIs(condition.clone(), *value))
            .chain(
                self.prop_facts
                    .diagnostic_sample(first_propositions, last_propositions)
                    .into_iter()
                    .cloned(),
            )
            .collect();
        (facts, conditions + propositions)
    }

    /// Answers whether a requirement is already stated in this context.
    /// Accepts explicit facts, conjunctions of them, and implications whose
    /// consequent is already stated. This query never selects a disjunction arm, instantiates a
    /// universal, or invents an existential witness.
    pub(crate) fn states_required_goal(&self, goal: &Proposition) -> bool {
        if let Proposition::And(left, right) = goal {
            return self.states_required_goal(left) && self.states_required_goal(right);
        }
        if let Proposition::Implies(_, consequent) = goal
            && self.states_required_goal(consequent)
        {
            // A proved conclusion also proves any guarded version of it.
            // This is needed when lowering has already discharged a generated
            // arithmetic guard in the surface spelling of a call requirement.
            return true;
        }
        // Loads emitted from a callee contract may retain its entry snapshot
        // while the caller's retained fact uses the registered load variable.
        // Canonicalize a condition leaf through the kernel's load naming law
        // before consulting the exact stated-fact index; this is not logical
        // search and does not apply to memory-loadable/resource predicates.
        let canonical = crate::kernel::canonical_condition_fact(goal);
        if canonical != *goal {
            return self.states_required_goal(&canonical);
        }
        if let Some(key) = crate::kernel::proof::proposition_identity_key(goal)
            && let Some(bucket) = self
                .stated_proposition_index()
                .and_then(|index| index.get(&key))
            && let Some(candidate) = bucket.iter().next()
        {
            // The key narrows the lookup to one identity bucket; retain the
            // relation as the final authority so future key representations
            // cannot silently broaden this query.
            return crate::kernel::proof::propositions_are_alpha_equal(candidate, goal);
        }
        // Unsupported proposition forms retain the old exact route.  This is
        // still a named fact check and never scans for a related proposition.
        self.contains_assumed_exact(goal)
    }

    /// One checked restriction: a context carrying exactly the named
    /// condition facts and proposition facts, with every derived index
    /// rebuilt from them.
    ///
    /// This is the only operation by which a planner outside the kernel
    /// narrows a context to a premise selection, so no caller reaches the
    /// private fact indexes or their rebuild hooks. The non-fact settings of
    /// `self` (transport and deferral flags) are preserved, because a
    /// restricted context must answer under the same regime as the context
    /// it was cut from.
    pub fn restricted_to_facts(
        &self,
        conditions: &[(ConditionTerm, bool)],
        propositions: &[Proposition],
    ) -> Self {
        let _checking = crate::instrumentation::CheckingWorkScope::new(
            "restrict to selected facts",
            conditions.len().saturating_add(propositions.len()),
        );
        // Start from selected input, never withdraw inherited pointer sources.
        // Only retained typing metadata is consulted by selected load-variable key.
        let mut restricted = Self::new();
        restricted.reasoning_policy = self.reasoning_policy;
        restricted.execution_variable_ceiling = self.execution_variable_ceiling.clone();
        restricted.variable_widths = self.variable_widths.clone();
        restricted
            .equality_graph
            .admitted
            .typed_pointer_read_definitions = self
            .equality_graph
            .admitted
            .typed_pointer_read_definitions
            .clone();
        for (condition, _) in conditions {
            restricted
                .execution_variable_ceiling
                .file_condition(condition);
        }
        restricted.condition_facts = conditions.iter().fold(
            crate::kernel::fact_collections::FactMap::default(),
            |facts, (condition, value)| facts.with_inserted(condition.clone(), *value),
        );
        restricted.execution_fact_projection = conditions
            .iter()
            .map(|(condition, value)| {
                (
                    ContextFactKey::Condition(condition.clone()),
                    std::sync::Arc::new(ExecutionPureFact::new(Proposition::ConditionIs(
                        condition.clone(),
                        *value,
                    ))),
                )
            })
            .collect();
        // Condition support is replaced next. Reconstructing the inherited
        // graph here would reconstruct unselected ambient edges, then discard it.
        restricted.clear_proposition_facts_with_graph_rebuild(false);
        restricted.rebuild_signed_order_bounds();
        restricted.rebuild_null_pointer_offsets();
        restricted.rebuild_memory_load_condition_facts();
        restricted.rebuild_condition_match_indexes();
        // File proposition edges and resource indexes only after their
        // condition graph is the selected one, never the inherited graph.
        for proposition in propositions {
            restricted.insert_proposition_fact(proposition.clone());
        }
        restricted.recompute_content_fingerprint();
        restricted
    }

    /// Ambient loadability facts for planner witness selection, charged per visit.
    /// Diagnostics use the block-keyed candidate view instead.
    pub(crate) fn memory_loadable_fact_propositions(
        &self,
        _permission: crate::SearchPermission,
    ) -> impl Iterator<Item = &Proposition> {
        self.memory_loadable_facts
            .values()
            .flat_map(|facts| facts.iter())
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// The disjunction facts of this context, in the index's own order, for
    /// a planner's case search.
    pub(crate) fn disjunction_fact_propositions(
        &self,
        permission: crate::SearchPermission,
    ) -> impl Iterator<Item = &Proposition> {
        self.disjunction_facts.scan_for_search(&permission)
    }

    /// Whether this context holds a disjunction fact.
    pub fn has_disjunction_facts(&self) -> bool {
        !self.disjunction_facts.is_empty()
    }

    /// Whether `proposition` is an exact proposition fact of this context.
    pub fn contains_proposition_fact(&self, proposition: &Proposition) -> bool {
        self.prop_facts.contains(proposition)
    }

    /// Test-only negative control: remove one premise and repair its indexes.
    /// This may rebuild derived indexes or defer rebuilding until a later query.
    /// Production branches retain the parent context and extend a cheap clone.
    #[cfg(test)]
    pub(crate) fn without_exact_fact(&self, proposition: &Proposition) -> Self {
        let mut weakened = self.clone();
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                if weakened.condition_facts.get(condition) == Some(value) {
                    weakened.forget_condition_fact(condition, *value);
                }
                weakened.remove_proposition_fact(proposition);
            }
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(condition, value)
                    if weakened.condition_facts.get(condition) == Some(&!*value) =>
                {
                    weakened.forget_condition_fact(condition, !*value);
                }
                _ => weakened.remove_proposition_fact(proposition),
            },
            _ => weakened.remove_proposition_fact(proposition),
        }
        weakened
    }

    #[cfg(test)]
    fn forget_condition_fact(&mut self, condition: &ConditionTerm, assumed: bool) {
        crate::instrumentation::record_deterministic_work(1);
        let predecessor = self.pointer_value_undo.take().filter(|undo| {
            assumed
                && undo.source.as_ref() == condition
                && undo.conditions.shares_root_with(&self.condition_facts)
                && undo.propositions.ptr_eq(&self.prop_facts)
        });
        self.restoring_pointer_graph = predecessor.map(|undo| undo.graph.clone());
        self.condition_facts = self.condition_facts.without_key(condition);
        if self
            .equality_graph
            .admitted
            .congruence_conditions
            .contains_key(condition)
        {
            self.equality_graph
                .admitted
                .congruence_conditions
                .remove(condition);
            self.rebuild_equality_graph();
        }
        self.adjust_pointer_class_fact(
            &Proposition::ConditionIs(condition.clone(), assumed),
            false,
        );
        self.execution_fact_projection
            .remove(&ContextFactKey::Condition(condition.clone()));
        self.adjust_condition_match_indexes(condition, assumed, false);
        self.adjust_stated_proposition_index(
            &Proposition::ConditionIs(condition.clone(), assumed),
            false,
        );
        self.adjust_signed_order_bound(condition, assumed, false);
        self.adjust_null_pointer_offset(condition, assumed, false);
        self.adjust_pointer_block_alias(condition, assumed, false);
        self.adjust_pointer_offset_alias(condition, assumed, false);
        self.adjust_int32_graph_equality(condition, assumed, false);
        self.adjust_uint64_graph_equality(condition, assumed, false);
        self.adjust_algebraic_graph_equality(
            &Proposition::ConditionIs(condition.clone(), assumed),
            false,
        );
        self.withdraw_typed_pointer_read_definition(condition, assumed);
        self.adjust_scalar_evidence_input(condition, assumed, false);
        self.adjust_bitvector64_equality(condition, assumed, false);
        self.adjust_exact_constant_equality(condition, assumed, false);
        self.adjust_memory_load_condition_index(condition, false);
        if let Some(graph) = self.restoring_pointer_graph.take() {
            self.equality_graph = graph.as_ref().clone();
        }
        self.content_fingerprint ^= Self::fingerprint(1, &(condition.clone(), assumed));
    }

    /// Like [`Self::restricted_to_facts`], but keeping every condition fact
    /// and replacing only the proposition facts.
    pub fn with_only_proposition_facts(&self, propositions: &[Proposition]) -> Self {
        let mut restricted = self.clone();
        restricted.clear_proposition_facts();
        for proposition in propositions {
            restricted.insert_proposition_fact(proposition.clone());
        }
        restricted.recompute_content_fingerprint();
        restricted
    }

    pub(super) fn includes(&self, required: &Self) -> bool {
        required
            .condition_facts
            .scan_explicit_input()
            .all(|(condition, value)| {
                self.contains_assumed_exact(&Proposition::ConditionIs(condition.clone(), *value))
            })
            && required
                .equality_graph
                .admitted
                .typed_pointer_read_definitions
                .iter()
                .all(|(variable, definitions)| {
                    self.equality_graph
                        .admitted
                        .typed_pointer_read_definitions
                        .get(variable)
                        .is_some_and(|held| {
                            definitions
                                .iter()
                                .all(|(key, value)| held.get(key) == Some(value))
                        })
                })
            && required
                .prop_facts
                .scan_explicit_input()
                .all(|proposition| self.contains_assumed_exact(proposition))
            && required
                .resource_compositions
                .scan_explicit_input()
                .all(|resources| self.resource_compositions.contains(resources))
    }
}

pub(crate) fn proposition_derivation(
    conclusion: &Proposition,
    rule: PropositionDerivationRule,
) -> PropositionDerivation {
    PropositionDerivation {
        conclusion: conclusion.clone(),
        rule,
    }
}

impl PropositionDerivation {
    /// Check this proof tree against an available context without searching for
    /// alternate proofs.
    #[inline(never)]
    pub fn check(&self, available: &PureFactContext) -> bool {
        let id_scope = PureFactContextIdScope::enter(available);
        match &self.rule {
            PropositionDerivationRule::ContextFree => solve_builtin_prop(&self.conclusion),
            PropositionDerivationRule::ContextualAtomic {
                premises,
                premises_id,
                extended_rules,
                evidence,
            } => {
                let premises = premises.context();
                (id_scope.id == *premises_id || available.includes(&premises))
                    && premises.checks_atomic_derivation(
                        &self.conclusion,
                        *extended_rules,
                        *premises_id,
                        evidence,
                    )
            }
            PropositionDerivationRule::Explosion { premises } => {
                let premises = premises.context();
                available.includes(&premises) && premises.is_inconsistent()
            }
            PropositionDerivationRule::And { left, right } => {
                let Proposition::And(expected_left, expected_right) = &self.conclusion else {
                    return false;
                };
                left.conclusion == **expected_left
                    && right.conclusion == **expected_right
                    && left.check(available)
                    && right.check(available)
            }
            PropositionDerivationRule::AlgebraicConstructorCongruence { fields } => {
                let Some(expected) = algebraic_constructor_field_equalities(&self.conclusion)
                else {
                    return false;
                };
                !expected.is_empty()
                    && derivations_match_propositions(fields, &expected)
                    && fields.iter().all(|proof| proof.check(available))
            }
            PropositionDerivationRule::AlgebraicConstructorInjectivity {
                source,
                field_index,
            } => {
                let Some(expected) = algebraic_constructor_field_equalities(source)
                    .and_then(|fields| fields.get(*field_index).cloned())
                else {
                    return false;
                };
                expected == self.conclusion && available.prop_facts.contains(source.as_ref())
            }
            PropositionDerivationRule::OrLeft(proof) => {
                let Proposition::Or(expected, _) = &self.conclusion else {
                    return false;
                };
                proof.conclusion == **expected && proof.check(available)
            }
            PropositionDerivationRule::OrRight(proof) => {
                let Proposition::Or(_, expected) = &self.conclusion else {
                    return false;
                };
                proof.conclusion == **expected && proof.check(available)
            }
            PropositionDerivationRule::DoubleNegation(proof) => {
                let Proposition::Not(body) = &self.conclusion else {
                    return false;
                };
                let Proposition::Not(expected) = body.as_ref() else {
                    return false;
                };
                proof.conclusion == **expected && proof.check(available)
            }
            PropositionDerivationRule::Implies { antecedent, body } => {
                let Proposition::Implies(expected_antecedent, expected_body) = &self.conclusion
                else {
                    return false;
                };
                antecedent.as_ref() == expected_antecedent.as_ref()
                    && body.conclusion == **expected_body
                    && body.check(
                        &available
                            .clone()
                            .assume_proposition(antecedent.as_ref().clone()),
                    )
            }
            PropositionDerivationRule::ImpliesFalseAntecedent(proof) => {
                let Proposition::Implies(expected_antecedent, _) = &self.conclusion else {
                    return false;
                };
                proof.conclusion == Proposition::Not(Box::new(expected_antecedent.as_ref().clone()))
                    && proof.check(available)
            }
            PropositionDerivationRule::ForAllBody(proof) => {
                let Proposition::ForAll { var, body, .. } = &self.conclusion else {
                    return false;
                };
                proof.conclusion == **body
                    && (!proposition_has_free_bitvector_variable(body, *var)
                        || proof
                            .context_premises()
                            .iter()
                            .all(|premise| !proposition_has_free_bitvector_variable(premise, *var)))
                    && proof.check(available)
            }
            PropositionDerivationRule::ExistsFromFact { source, body } => {
                let Proposition::Exists {
                    var,
                    sort,
                    body: expected_body,
                    ..
                } = &self.conclusion
                else {
                    return false;
                };
                let Proposition::Exists {
                    var: source_var,
                    sort: source_sort,
                    body: source_body,
                    ..
                } = source.as_ref()
                else {
                    return false;
                };
                if sort != source_sort
                    || !available.proves_exact(source)
                    || body.conclusion != **expected_body
                {
                    return false;
                }
                let Some(renamed_source_body) =
                    crate::kernel::api::substitute_quantified_body_capture_free(
                        source_body,
                        *source_var,
                        *var,
                        sort,
                    )
                else {
                    return false;
                };
                let mut witness_available = available.clone();
                let mut conjuncts = Vec::new();
                collect_proposition_conjuncts(&renamed_source_body, &mut conjuncts);
                for conjunct in conjuncts {
                    witness_available = witness_available.assume_proposition(conjunct);
                }
                body.check(&witness_available)
            }
            PropositionDerivationRule::ExistsFromWitness { witness, body } => {
                let Proposition::Exists {
                    var,
                    body: expected_body,
                    ..
                } = &self.conclusion
                else {
                    return false;
                };
                let mut witness_variables = BTreeSet::new();
                collect_bitvector_variables(witness, &mut witness_variables);
                if witness_variables.contains(var) {
                    return false;
                }
                let instantiated =
                    substitute_bitvector_variable_in_proposition(expected_body, *var, witness);
                body.conclusion == instantiated && body.check(available)
            }
            PropositionDerivationRule::ForAllLoadableRange { source } => {
                available.proves_exact(source)
                    && available.checks_forall_loadable_range(&self.conclusion, source)
            }
            PropositionDerivationRule::ExistsLoadableRange { source, witness } => {
                available.proves_exact(source)
                    && available.checks_exists_loadable_range(&self.conclusion, source, witness)
            }
            PropositionDerivationRule::FiniteForAll { instances } => {
                let mut expected = available.finite_forall_instantiations(&self.conclusion);
                !instances.is_empty()
                    && instances.iter().all(|proof| {
                        expected
                            .next()
                            .is_some_and(|conclusion| proof.conclusion == conclusion)
                            && proof.check(available)
                    })
                    && expected.next().is_none()
            }
            PropositionDerivationRule::SingletonSubstitution {
                variable,
                value,
                equality,
                body,
            } => {
                let variable_term = Bitvector32Term::Variable(*variable);
                let constant = signed_i64_bitvector_constant(*value);
                let Ok(expected) =
                    crate::kernel::reasoning::substitute_machine_constant_in_pure_proposition(
                        &self.conclusion,
                        *variable,
                        *value,
                    )
                else {
                    return false;
                };
                expected != self.conclusion
                    && body.conclusion == expected
                    && equality.checks(&variable_term, &constant, available)
                    && body.check(available)
            }
            PropositionDerivationRule::RefutedDisjunction { disjunction } => {
                let mut cases = Vec::new();
                collect_or_cases(disjunction, &mut cases);
                cases.len() >= 2
                    && available.contains_assumed_exact(disjunction)
                    && cases.iter().all(|case| {
                        available.contains_assumed_exact(&Proposition::Not(Box::new(case.clone())))
                    })
            }
            PropositionDerivationRule::DisjunctionCases { disjunction, cases } => {
                if !available.prop_facts.contains(disjunction.as_ref()) {
                    return false;
                }
                let mut expected_cases = Vec::new();
                collect_or_cases(disjunction, &mut expected_cases);
                if expected_cases.len() < 2 || cases.len() != expected_cases.len() {
                    return false;
                }
                cases.iter().zip(expected_cases).all(|(proof, case)| {
                    proof.conclusion == self.conclusion
                        && proof.check(&available.clone().assume_proposition(case))
                })
            }
        }
    }
}

/// Whether `term`'s arithmetic names a pointer address, the shape the
/// integer-to-pointer cast recovers a pointer from.
fn mentions_pointer_address(term: &Bitvector32Term) -> bool {
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        if matches!(term, Bitvector32Term::PointerAddress(..)) {
            return true;
        }
        if let Some((_, left, right)) = term.as_binary() {
            pending.push(left);
            pending.push(right);
        } else if let Some((_, value)) = term.as_unary() {
            pending.push(value);
        }
    }
    false
}

pub(crate) fn collect_proposition_conjuncts(
    proposition: &Proposition,
    into: &mut Vec<Proposition>,
) {
    match proposition {
        Proposition::And(left, right) => {
            collect_proposition_conjuncts(left, into);
            collect_proposition_conjuncts(right, into);
        }
        other => into.push(other.clone()),
    }
}

fn derivations_match_propositions(
    derivations: &[PropositionDerivation],
    propositions: &[Proposition],
) -> bool {
    derivations.len() == propositions.len()
        && derivations
            .iter()
            .zip(propositions)
            .all(|(derivation, proposition)| derivation.conclusion == *proposition)
}

fn relative_range_offset(value: &Bitvector32Term, origin: &Bitvector32Term) -> Bitvector32Term {
    match (value, origin) {
        (
            binary_term!(Int32, Subtract, value, value_origin),
            binary_term!(Int32, Subtract, origin, origin_origin),
        ) if value_origin == origin_origin => {
            Bitvector32Term::subtract(value.as_ref().clone(), origin.as_ref().clone())
        }
        _ => Bitvector32Term::subtract(value.clone(), origin.clone()),
    }
}

fn signed_int_min_term() -> Bitvector32Term {
    Bitvector32Term::Constant(i32::MIN as u32)
}

fn signed_int_max_term() -> Bitvector32Term {
    Bitvector32Term::Constant(i32::MAX as u32)
}

fn range_intervals_cover_target(target: &CMemoryRange, mut intervals: Vec<(i64, i64)>) -> bool {
    let Some(target_start) = target.signed_constant_start() else {
        return false;
    };
    let Some(target_end) = target.signed_constant_end() else {
        return false;
    };
    if target_end <= target_start {
        return true;
    }

    intervals.sort_unstable();
    let mut covered_until = target_start;
    for (start, end) in intervals {
        let start = start.max(target_start);
        let end = end.min(target_end);
        if end <= covered_until {
            continue;
        }
        if start > covered_until {
            return false;
        }
        covered_until = end;
        if covered_until >= target_end {
            return true;
        }
    }
    false
}

// Called only by memory_ranges_proven_equal after its wide-range branch.
fn memory_range_length_term(range: &CMemoryRange) -> Bitvector32Term {
    match range.end() {
        binary_term!(Int32, Add, base, length) if base.as_ref() == range.start() => {
            length.as_ref().clone()
        }
        binary_term!(Int32, Add, length, base) if base.as_ref() == range.start() => {
            length.as_ref().clone()
        }
        end => Bitvector32Term::subtract(end.clone(), range.start().clone()),
    }
}

/// Whether every cell of `range` is a cell of `parent`, for a caller with no
/// fact context. See [`memory_range_shallowly_contained_with_facts`].
pub(in crate::kernel) fn memory_range_shallowly_contained(
    range: &CMemoryRange,
    parent: &CMemoryRange,
) -> bool {
    memory_range_contained_by_exact_arithmetic(range, parent, None)
}

/// [`memory_range_shallowly_contained`] for a caller that holds a fact context.
///
/// This is `memory_range_covers`'s structural arm, so it gates every `owns` and
/// `views` entailment, contract-effect coverage and `free` extent. It concluded
/// containment from two affine differences of modular terms read as signed
/// orders, and that is the same misreading `bitvector_index_outside_range_shallow`
/// carried, in the direction where it is unsound: a difference of `2^32` is not
/// "at or after", it is "the same element".
///
/// What containment means is an `i64` statement about addresses. `parent` holds
/// `parent_count` elements from the address of its element `parent.start`;
/// `range` holds `range_count` from the address of its own element
/// `range.start`, which sits `offset` elements into the parent. So containment
/// is `0 <= offset` and `offset + range_count <= parent_count`, and each of the
/// three is computed exactly or not at all:
///
/// * `offset` is the base delta plus `sext(range.start) - sext(parent.start)`.
///   The delta comes from [`Pointer::exact_element_delta_from_base`] as an
///   exact `i64` constant beside at most one symbolic index; the subtraction
///   comes from [`exact_affine_index_difference`]. Because only one symbolic
///   index may appear, whichever of the two ranges is rebased must carry a
///   constant start — which is what the shapes that reach here do: a child at
///   the parent's own base, or a child `[0..k]` at a pointer into the parent.
/// * both counts come from [`affine_range_element_count`], which is the count
///   and not a bound on it.
///
/// Ranges with different element widths have a narrower route: all endpoints
/// and the byte delta between their bases must be constant. Checked `i64`
/// multiplication and addition then compare their exact byte intervals. This
/// connects raw construction storage with typed field footprints without
/// treating symbolic or modular endpoint arithmetic as byte arithmetic.
///
/// A parent whose endpoints have no constant difference has no count, and then
/// the only route left compares the two ranges' *ends* — `p[3..n]` inside
/// `p[0..n]`. That reads `end` as `start + count`, so it additionally asks
/// [`range_count_is_nonnegative`] of the parent, which a stated extent guard
/// supplies and a context-free caller cannot.
pub(in crate::kernel) fn memory_range_shallowly_contained_with_facts(
    range: &CMemoryRange,
    parent: &CMemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    memory_range_contained_by_exact_arithmetic(range, parent, Some(assumptions))
}

fn memory_range_contained_by_exact_arithmetic(
    range: &CMemoryRange,
    parent: &CMemoryRange,
    assumptions: Option<&PureFactContext>,
) -> bool {
    if range.wide_bounds().is_some() || parent.wide_bounds().is_some() {
        return assumptions.is_some_and(|assumptions| {
            crate::kernel::primitives::wide_memory_range_covers(parent, range, assumptions)
        });
    }
    if range.element_width() != parent.element_width() {
        // Construction owns raw bytes while a constructor's write footprint
        // names typed fields. Constant bounds can be compared in exact byte
        // coordinates without modular arithmetic or changing either range.
        let Some(delta) = range
            .base()
            .exact_element_delta_from_base(parent.base(), 1, assumptions)
        else {
            return false;
        };
        if !delta.is_constant() {
            return false;
        }
        let byte_endpoint = |endpoint: &Bitvector32Term, width: u32, offset: i64| {
            signed_bitvector_constant(endpoint)?
                .checked_mul(i64::from(width))?
                .checked_add(offset)
        };
        let (Some(start), Some(end), Some(parent_start), Some(parent_end)) = (
            byte_endpoint(range.start(), range.element_width(), delta.constant),
            byte_endpoint(range.end(), range.element_width(), delta.constant),
            byte_endpoint(parent.start(), parent.element_width(), 0),
            byte_endpoint(parent.end(), parent.element_width(), 0),
        ) else {
            return false;
        };
        return parent_start <= start && start <= end && end <= parent_end;
    }
    let Some(base_delta) = range.base().exact_element_delta_from_base(
        parent.base(),
        parent.element_width(),
        assumptions,
    ) else {
        return false;
    };
    // `range`'s endpoints are in its own base's coordinates and `parent`'s are
    // in the parent's, so the base delta joins them. Only one symbolic index
    // may cross that join, since adding two would need the modular add this
    // whole rule exists to stop trusting.
    let translate = |endpoint: &Bitvector32Term| {
        if base_delta.is_constant() {
            Some((endpoint.clone(), base_delta.constant))
        } else {
            signed_bitvector_constant(endpoint)
                .and_then(|endpoint| base_delta.constant.checked_add(endpoint))
                .map(|constant| (base_delta.index.clone(), constant))
        }
    };
    let Some((start_term, start_constant)) = translate(range.start()) else {
        return false;
    };
    let Some(offset) = exact_affine_index_difference(&start_term, parent.start(), assumptions)
        .and_then(|difference| difference.checked_add(start_constant))
    else {
        return false;
    };
    if offset < 0 {
        return false;
    }
    if let (Some(range_count), Some(parent_count)) = (
        affine_range_element_count(range.start(), range.end()),
        affine_range_element_count(parent.start(), parent.end()),
    ) && offset
        .checked_add(range_count)
        .is_some_and(|end| end <= parent_count)
    {
        return true;
    }
    let Some((end_term, end_constant)) = translate(range.end()) else {
        return false;
    };
    let Some(slack) = exact_affine_index_difference(parent.end(), &end_term, assumptions)
        .and_then(|difference| difference.checked_sub(end_constant))
    else {
        return false;
    };
    let Some(reach) = offset.checked_add(slack) else {
        return false;
    };
    slack >= 0
        && reach < (1i64 << 31)
        && (reach == 0 || range_count_is_nonnegative(parent, assumptions))
}

pub(super) fn memory_range_contained_for_memory_resolution(
    range: &CMemoryRange,
    parent: &CMemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    // Exact constant byte intervals cover typed accesses even when one side
    // uses raw bytes or int32 words. Symbolic cross-width containment remains
    // refused; the recursive element-index rules below require equal widths.
    if memory_range_shallowly_contained_with_facts(range, parent, assumptions) {
        return true;
    }
    if range.wide_bounds().is_some() || parent.wide_bounds().is_some() {
        return false;
    }
    if range.element_width() != parent.element_width() {
        return false;
    }
    if super::reasoning::resolution_interrupted() {
        return false;
    }
    let Some(_query) = super::reasoning::ResolutionQueryGuard::enter(
        super::reasoning::ResolutionQuery::RangeContained(range.clone(), parent.clone()),
    ) else {
        return false;
    };

    if super::reasoning::pointers_proven_equal_for_memory_resolution(
        range.base(),
        parent.base(),
        assumptions,
    ) {
        return exact_less_equal_for_memory_resolution(parent.start(), range.start(), assumptions)
            && exact_less_equal_for_memory_resolution(range.end(), parent.end(), assumptions);
    }

    if affine_bitvector_difference_constant(range.end(), range.start()) == Some(1) {
        let pointer = range.base().offset_by_int32_elements(range.start().clone());
        if pointer_in_memory_range_for_memory_resolution(&pointer, parent, assumptions) {
            return true;
        }
    }

    false
}

fn exact_less_equal_for_memory_resolution(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    if let (Some(left), Some(right)) = (
        signed_bitvector_constant(left),
        signed_bitvector_constant(right),
    ) {
        return left <= right;
    }
    if left == right
        // These are signed int32 endpoint *values*, not exact byte offsets.
        // Equal bitpatterns therefore satisfy `<=` in this same-base check.
        || assumptions.int32_values_known_equal(left, right)
        || assumptions.exact_condition_value(&ConditionTerm::signed_less_equal(
            left.clone(),
            right.clone(),
        )) == Some(true)
        || assumptions.has_exact_order_path(left, right, false)
    {
        return true;
    }
    let left_constant = signed_bitvector_constant(left);
    if recorded_less_equal_candidates(left, right, assumptions).any(|(fact_lower, fact_upper)| {
        // The written fact states `fact_lower <= fact_upper` (or `<`, which
        // is stronger). It proves the query when its lower endpoint is the
        // query's lower endpoint, or — for a constant query endpoint — when
        // it is a constant at least as large.
        if crate::kernel::reasoning::int32_values_proven_equal_for_memory_resolution(
            &fact_lower,
            left,
            assumptions,
        ) {
            return true;
        }
        let Some(left_constant) = left_constant else {
            return false;
        };
        let strict = assumptions
            .condition_facts
            .get(&ConditionTerm::signed_less_than(
                fact_lower.clone(),
                fact_upper.clone(),
            ))
            .copied()
            == Some(true);
        signed_bitvector_constant(&fact_lower)
            .is_some_and(|bound| left_constant <= if strict { bound + 1 } else { bound })
    }) {
        return true;
    }
    // Keep broader scalar-resolution rules for forms outside graph closure or
    // the indexed order facts, without building their fact index first.
    bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
}

#[cfg(test)]
mod contained_range_endpoint_graph_tests {
    use super::*;

    fn variable(id: u64) -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(id))
    }

    fn endpoint(id: u64) -> Bitvector32Term {
        Bitvector32Term::add(variable(id), Bitvector32Term::Constant(1))
    }

    #[test]
    fn signed_containment_order_uses_graph_value_equality() {
        let premise = ConditionTerm::equal(variable(9_330_001), variable(9_330_002));
        let parent = PureFactContext::new();
        let branch = parent.clone().assume_condition(premise.clone(), true);
        let _scope = branch.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        assert!(exact_less_equal_for_memory_resolution(
            &endpoint(9_330_001),
            &endpoint(9_330_002),
            &branch,
        ));
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(!exact_less_equal_for_memory_resolution(
            &endpoint(9_330_001),
            &endpoint(9_330_002),
            &parent,
        ));
        let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(premise, true));
        assert!(!exact_less_equal_for_memory_resolution(
            &endpoint(9_330_001),
            &endpoint(9_330_002),
            &withdrawn,
        ));
    }

    #[test]
    fn same_base_range_containment_uses_graph_equal_endpoints() {
        let base = Pointer::symbolic(Variable(9_330_003));
        let parent = CMemoryRange::new(
            base.clone(),
            Bitvector32Term::Constant(0),
            endpoint(9_330_001),
        );
        let child = CMemoryRange::new(
            base.clone(),
            Bitvector32Term::Constant(0),
            endpoint(9_330_002),
        );
        let premise = ConditionTerm::equal(variable(9_330_001), variable(9_330_002));
        let bare = PureFactContext::new();
        let branch = bare.clone().assume_condition(premise.clone(), true);
        let _scope = branch.enter_id_scope();

        assert!(!memory_range_shallowly_contained_with_facts(
            &child, &parent, &branch,
        ));
        assert!(memory_range_contained_for_memory_resolution(
            &child, &parent, &branch,
        ));
        assert!(!memory_range_contained_for_memory_resolution(
            &child, &parent, &bare,
        ));
        let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(premise, true));
        assert!(!memory_range_contained_for_memory_resolution(
            &child, &parent, &withdrawn,
        ));
        let other_base = child.with_bounds(
            Pointer::symbolic(Variable(9_330_004)),
            child.start().clone(),
            child.end().clone(),
        );
        assert!(!memory_range_contained_for_memory_resolution(
            &other_base,
            &parent,
            &branch,
        ));
    }

    #[test]
    fn recorded_order_fact_matches_graph_equal_lower_or_upper_endpoint() {
        let lower = variable(9_330_010);
        let upper = variable(9_330_011);
        let premise = ConditionTerm::equal(variable(9_330_001), variable(9_330_002));
        let lower_fact = ConditionTerm::signed_less_equal(endpoint(9_330_001), upper.clone());
        let upper_fact = ConditionTerm::signed_less_than(lower.clone(), endpoint(9_330_001));
        let bare = PureFactContext::new()
            .assume_condition(lower_fact, true)
            .assume_condition(upper_fact, true);
        let branch = bare.clone().assume_condition(premise.clone(), true);
        let _scope = branch.enter_id_scope();

        PureFactContext::reset_bitvector_equality_index_fact_visits();
        assert!(exact_less_equal_for_memory_resolution(
            &endpoint(9_330_002),
            &upper,
            &branch,
        ));
        assert!(exact_less_equal_for_memory_resolution(
            &lower,
            &endpoint(9_330_002),
            &branch,
        ));
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(!exact_less_equal_for_memory_resolution(
            &endpoint(9_330_002),
            &upper,
            &bare,
        ));
        assert!(!exact_less_equal_for_memory_resolution(
            &lower,
            &endpoint(9_330_002),
            &bare,
        ));
        let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(premise, true));
        assert!(!exact_less_equal_for_memory_resolution(
            &endpoint(9_330_002),
            &upper,
            &withdrawn,
        ));
        assert!(!exact_less_equal_for_memory_resolution(
            &lower,
            &endpoint(9_330_002),
            &withdrawn,
        ));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/assumptions/contained_range_endpoint_graph_tests.rs");
    }
}

/// The recorded `a <= b` and `a < b` facts whose upper endpoint is the named
/// `right`, or whose lower endpoint is the named `left`, as `(a, b)` pairs.
///
/// This replaces two scans of the whole ambient condition-fact set. Every
/// signed-order fact is already indexed at both of its endpoints — under the
/// term the fact wrote and under that term's canonical form — by
/// `PureFactContext::signed_order_bounds`, so the candidates a containment
/// query could use are reachable in work proportional to the bounds recorded
/// at the two endpoints the query itself names. Each candidate is then
/// confirmed against `condition_facts` by exact lookup, so the index's
/// normalization of `>`, `>=`, and negated forms cannot widen the rule: only
/// a written true `<=` or `<` is yielded, exactly as the scans required.
///
/// Narrowing, deliberate and measured: a fact whose relevant endpoint is
/// neither syntactically nor canonically the query's endpoint, and is only
/// *provably* equal to it, is no longer found. Reaching it needed a
/// proof-aware comparison against every ambient condition fact, which is the
/// scan this removes. `satisfies_fact_miss_ignores_unrelated_facts` is the
/// scaling regression.
fn recorded_less_equal_candidates<'a>(
    left: &'a Bitvector32Term,
    right: &'a Bitvector32Term,
    assumptions: &'a PureFactContext,
) -> impl Iterator<Item = (Bitvector32Term, Bitvector32Term)> + 'a {
    let endpoint_keys = |term: &Bitvector32Term| {
        let canonical = crate::kernel::eval::canonical_term(term);
        if canonical == *term {
            vec![term.clone()]
        } else {
            vec![term.clone(), canonical]
        }
    };
    // `signed_order_bounds` entries are `(own endpoint, other endpoint,
    // strict, own endpoint is the lower one)`. A lookup at `right` yields
    // the facts bounding it from below; a lookup at `left` yields the facts
    // bounding it from above.
    let upper_side = endpoint_keys(right).into_iter().flat_map(move |key| {
        assumptions
            .signed_order_bounds
            .get(&key)
            .into_iter()
            .flat_map(|bounds| bounds.keys().cloned().collect::<Vec<_>>())
            .filter(|(_, _, _, own_is_lower)| !*own_is_lower)
            .map(|(own, other, _, _)| (other, own))
    });
    let lower_side = endpoint_keys(left).into_iter().flat_map(move |key| {
        assumptions
            .signed_order_bounds
            .get(&key)
            .into_iter()
            .flat_map(|bounds| bounds.keys().cloned().collect::<Vec<_>>())
            .filter(|(_, _, _, own_is_lower)| *own_is_lower)
            .map(|(own, other, _, _)| (own, other))
    });
    upper_side
        .chain(lower_side)
        .filter(move |(fact_lower, fact_upper)| {
            // Confirm the written form. The index normalizes every order
            // shape into one direction; only a true `<=` or `<` fact may
            // discharge this rule, as the replaced scans required.
            let written = |condition| assumptions.condition_facts.get(&condition).copied();
            written(ConditionTerm::signed_less_equal(
                fact_lower.clone(),
                fact_upper.clone(),
            )) == Some(true)
                || written(ConditionTerm::signed_less_than(
                    fact_lower.clone(),
                    fact_upper.clone(),
                )) == Some(true)
        })
        .filter(move |(_, fact_upper)| {
            fact_upper == right
                || crate::kernel::reasoning::int32_values_proven_equal_for_memory_resolution(
                    fact_upper,
                    right,
                    assumptions,
                )
        })
}

/// [`pointer_in_range_shallow`] over a range, for a caller with no fact
/// context: a structural or memoized walk that cannot consult one. It answers
/// only what arithmetic settles on its own — a pointer at the range's own start
/// term, or wholly constant endpoints and delta — and refuses the rest rather
/// than reading a residue as an offset.
pub(in crate::kernel) fn pointer_in_memory_range_shallow(
    pointer: &Pointer,
    range: &CMemoryRange,
) -> bool {
    // A wide range's bounds are 64-bit terms, which nothing decides without
    // a fact context.
    if range.wide_bounds().is_some() {
        return false;
    }
    pointer_in_range_shallow(
        pointer,
        range.base(),
        range.start(),
        range.end(),
        range.element_width(),
        None,
    )
}

/// [`pointer_in_memory_range_shallow`] for a caller that does hold a fact
/// context, so a range whose start is only provably nonnegative still answers.
pub(in crate::kernel) fn pointer_in_memory_range_shallow_with_facts(
    pointer: &Pointer,
    range: &CMemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    // A wide range has one membership rule: the pointer addresses a whole
    // element at an unsigned 64-bit index inside the bounds.
    if range.wide_bounds().is_some() {
        return assumptions.pointer_access_in_wide_range(pointer, range.element_width(), range);
    }
    pointer_in_range_shallow(
        pointer,
        range.base(),
        range.start(),
        range.end(),
        range.element_width(),
        Some(assumptions),
    )
}

fn pointer_offsets_match_by_shallow_fact_graph(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) => {
            pointer_offsets_match_by_shallow_fact_graph(left_a, right_a, assumptions)
                && pointer_offsets_match_by_shallow_fact_graph(left_b, right_b, assumptions)
        }
        (
            PointerOffsetTerm::Int32Scaled {
                value: left,
                byte_width: left_width,
            },
            PointerOffsetTerm::Int32Scaled {
                value: right,
                byte_width: right_width,
            },
        ) => left_width == right_width && assumptions.int32_values_known_equal(left, right),
        _ => false,
    }
}

fn pointer_in_memory_range_for_memory_resolution(
    pointer: &Pointer,
    range: &CMemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    // A wide range has its one membership rule.
    if range.wide_bounds().is_some() {
        return assumptions.pointer_access_in_wide_range(pointer, range.element_width(), range);
    }
    pointer_in_range_for_memory_resolution(
        pointer,
        range.base(),
        range.start(),
        range.end(),
        range.element_width(),
        assumptions,
    )
}

fn pointer_in_range_for_memory_resolution(
    pointer: &Pointer,
    base: &Pointer,
    start: &Bitvector32Term,
    end: &Bitvector32Term,
    element_width: u32,
    assumptions: &PureFactContext,
) -> bool {
    if super::reasoning::resolution_interrupted() {
        return false;
    }
    let Some(pointer) =
        super::reasoning::pointer_in_block_for_memory_resolution(pointer, &base.block, assumptions)
    else {
        return false;
    };
    let pointer = &pointer;
    let Some(_query) = super::reasoning::ResolutionQueryGuard::enter(
        super::reasoning::ResolutionQuery::PointerInRange(
            pointer.clone(),
            base.clone(),
            start.clone(),
            end.clone(),
            element_width,
        ),
    ) else {
        return false;
    };
    // Every index collected here ends in a membership conclusion, so each is
    // the pointer's element delta exactly or not at all: `element_index_from_offset`
    // folds an exact `i64` byte offset into a wrapping 32-bit add, and a
    // residue read as an index is the wrap this rule cannot see.
    let mut indexes = pointer
        .exact_element_delta_from_base(base, element_width, Some(assumptions))
        .and_then(|delta| delta.as_index_term())
        .into_iter()
        .collect::<Vec<_>>();
    if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
        crate::instrumentation::measure_operation(
            "kernel",
            "explicit range arms",
            "range membership: offset equality",
            || {
                if super::reasoning::pointer_offsets_proven_equal_for_memory_resolution(
                    left,
                    &base.offset,
                    assumptions,
                ) && let Some(index) = exact_element_delta_from_offset(right, element_width)
                    .and_then(|delta| delta.as_index_term())
                    && !indexes.contains(&index)
                {
                    indexes.push(index);
                }
                if super::reasoning::pointer_offsets_proven_equal_for_memory_resolution(
                    right,
                    &base.offset,
                    assumptions,
                ) && let Some(index) = exact_element_delta_from_offset(left, element_width)
                    .and_then(|delta| delta.as_index_term())
                    && !indexes.contains(&index)
                {
                    indexes.push(index);
                }
            },
        );
    }
    crate::instrumentation::measure_operation(
        "kernel",
        "explicit range arms",
        "range membership: index in range",
        || {
            indexes
                .iter()
                .any(|index| bitvector_index_in_range_shallow(index, start, end, assumptions))
        },
    )
}

/// Pins a term to a signed constant using EXACT facts only: either the term
/// is itself constant, or one recorded exact equality names its value. Exact
/// condition facts are pinned verbatim into certificates, so both smart
/// execution and check see the same set and the answer is deterministic.
/// One hop, no recursion: a value-dependent range endpoint like
/// `owner->len` is separated from its constant by exactly the recorded
/// resource fact, never by a rewrite chain.
pub(in crate::kernel) fn exact_signed_constant(
    term: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> Option<i64> {
    if let Some(value) = signed_bitvector_constant(term) {
        return Some(value);
    }
    // The first true equality, in fact order, that pins `term` to a
    // constant: one keyed lookup instead of a scan of every condition fact.
    crate::instrumentation::record_deterministic_work(1);
    let (_, constant) = assumptions
        .equality_graph
        .exact_literal_sources(term)?
        .iter()
        .next()?;
    #[cfg(test)]
    EXACT_CONSTANT_FACT_VISITS.with(|visits| visits.set(visits.get() + 1));
    Some(*constant)
}

/// The constant an exact equality's other side names, read the way
/// [`exact_signed_constant`] reads it: signed 32-bit, then 64-bit signed,
/// then 64-bit unsigned when it fits.
fn exact_equality_constant(candidate: &Bitvector32Term) -> Option<i64> {
    signed_bitvector_constant(candidate).or_else(|| {
        candidate.int64_as_const().or_else(|| {
            candidate
                .uint64_as_const()
                .and_then(|value| i64::try_from(value).ok())
        })
    })
}

/// [`exact_signed_constant`] for a term whose *sixty-four-bit* value is the
/// question — the value an `Int64Scaled` displacement scales.
///
/// A thirty-two-bit fact names a thirty-two-bit value and says nothing about
/// the other word, so it may not answer here: a low word of `0xFFFFFFFF` is
/// `-1`, and is equally `4294967295`, and is equally `2^32 + 4294967295`.
/// `exact_signed_constant` accepts one, which is right for the thirty-two-bit
/// quantities it was written for and wrong for this one. Only a sixty-four-bit
/// constant term, or arithmetic established through recorded exact
/// sixty-four-bit equalities, pins a value here.
///
/// `unsigned` says how the scaling reads it, and the two readings are
/// different numbers: `size_t` `4294967295` displaces forwards by that many
/// elements, while the same word read signed is the element below the base.
pub(in crate::kernel) fn exact_sixty_four_bit_constant(
    term: &Bitvector32Term,
    unsigned: bool,
    assumptions: &PureFactContext,
) -> Option<i64> {
    let constant = |candidate: &Bitvector32Term| {
        if unsigned {
            candidate
                .uint64_as_const()
                .and_then(|value| i64::try_from(value).ok())
        } else {
            candidate.int64_as_const()
        }
    };
    if let Some(value) = constant(term) {
        return Some(value);
    }
    // Follow the selected term's indexed 64-bit equality component and
    // evaluate only its bounded arithmetic. A low-word equality is not
    // evidence about the full address displacement.
    let bits = assumptions.wide_constant_from_equalities(term)?;
    if unsigned {
        i64::try_from(bits).ok()
    } else {
        Some(bits as i64)
    }
}

/// Exact constants for the two offset forms admitted by wide constant
/// congruence. Scaling must fit the offset's signed 64-bit representation.
pub(in crate::kernel) fn exact_wide_scaled_offset_constant(
    offset: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> Option<i64> {
    match offset {
        PointerOffsetTerm::Constant(value) => Some(*value),
        PointerOffsetTerm::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } => exact_sixty_four_bit_constant(value, *unsigned, assumptions)?.checked_mul(*byte_width),
        _ => None,
    }
}

pub(in crate::kernel) fn bitvector_index_in_range_shallow(
    index: &Bitvector32Term,
    start: &Bitvector32Term,
    end: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    let recorded_exact_order_path = |left: &Bitvector32Term,
                                     right: &Bitvector32Term,
                                     strict: bool| {
        let Some(path) = assumptions.exact_signed_order_path_evidence(left, right, strict) else {
            return false;
        };
        for step in path {
            record_implicit_reasoning_provenance(assumptions, &step.premise);
        }
        true
    };
    if let (Some(index), Some(start), Some(end)) = (
        signed_bitvector_constant(index),
        signed_bitvector_constant(start),
        signed_bitvector_constant(end),
    ) {
        return start <= index && index < end;
    }
    // Value-dependent endpoints pinned by exact facts (e.g. a range end of
    // `owner->len` with the recorded exact fact `owner->len == 1`) resolve
    // to constants without any non-exact condition reasoning. Success only:
    // an unresolved or unsatisfied triple falls through to the other arms.
    if let (Some(index), Some(start), Some(end)) = (
        exact_signed_constant(index, assumptions),
        exact_signed_constant(start, assumptions),
        exact_signed_constant(end, assumptions),
    ) && start <= index
        && index < end
    {
        return true;
    }
    let lower_bound_is_exact = assumptions.exact_condition_value(
        &ConditionTerm::signed_less_equal(start.clone(), index.clone()),
    ) == Some(true)
        // Canonical-keyed bound lookup before any searching arm: indexed
        // and deterministic, so check sees the same answer.
        || assumptions.canonical_bound_holds(start, index, false)
        || recorded_exact_order_path(start, index, false)
        || assumptions.should_defer_non_exact_condition_reasoning()
            && assumptions.difference_graph_proves_order(start, index, false)
        || start == &Bitvector32Term::Constant(0)
            && index.add_const_parts().is_some_and(|(base, increment)| {
                (increment as i32) > 0
                    && (recorded_exact_order_path(start, &base, false)
                        || assumptions.should_defer_non_exact_condition_reasoning()
                            && assumptions
                                .difference_graph_proves_order(start, &base, false))
                    && (assumptions.exact_condition_value(&ConditionTerm::signed_add_overflows(
                        base.clone(),
                        Bitvector32Term::Constant(increment),
                    )) == Some(false)
                        || assumptions.exact_condition_value(&ConditionTerm::signed_add_overflows(
                            Bitvector32Term::Constant(increment),
                            base.clone(),
                        )) == Some(false)
                        // A recorded strict signed upper bound (`base < y`)
                        // pins `base < INT_MAX`, so `base + 1` cannot
                        // overflow. Exact facts only; extended-bridging
                        // scope only, to keep every other phase's range
                        // answers byte-identical to the pre-arc path.
                        || increment == 1
                            && super::api::extended_dag_bridging_active()
                            && assumptions.has_exact_strict_upper_bound(&base))
            });
    let upper_bound_is_exact = assumptions
        .exact_condition_value(&ConditionTerm::signed_less_than(index.clone(), end.clone()))
        == Some(true)
        || assumptions.canonical_bound_holds(index, end, true)
        || recorded_exact_order_path(index, end, true)
        || assumptions.should_defer_non_exact_condition_reasoning()
            && assumptions.difference_graph_proves_order(index, end, true);
    if lower_bound_is_exact && upper_bound_is_exact {
        // The bounds were read off exact facts along some indexed path; a
        // provenance collection wants the facts behind them, whichever arm
        // found them.
        record_implicit_reasoning_provenance(
            assumptions,
            &Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(start.clone(), index.clone()),
                true,
            ),
        );
        record_implicit_reasoning_provenance(
            assumptions,
            &Proposition::ConditionIs(
                ConditionTerm::signed_less_than(index.clone(), end.clone()),
                true,
            ),
        );
        return true;
    }

    element_delta_in_range_by_affine_arithmetic(
        &ExactElementDelta {
            index: index.clone(),
            constant: 0,
        },
        start,
        end,
        assumptions,
    )
}

/// Whether an exact element delta lands inside `[start, end)`, by affine
/// arithmetic over the range's own endpoints.
///
/// This is the tail of [`bitvector_index_in_range_shallow`], over a delta
/// rather than one index term, because a pointer's delta is an `i64` constant
/// beside a symbolic index and joining the two would need the modular add this
/// rule must not trust. The arms above that tail state the index as a term, so
/// they answer only for a delta that *is* one term
/// ([`ExactElementDelta::as_index_term`]); this one answers for both.
///
/// The affine routes read a constant difference as a signed order, and a
/// difference of modular terms is the true one only modulo `2^32`. An
/// "outside" conclusion survives that reduction — a residue past the count is
/// outside whichever way the terms wrapped — and "inside" does not, so the
/// offset here is the real one ([`exact_affine_index_difference`]) and the
/// length is the real element count ([`affine_range_element_count`]), or this
/// concludes nothing. The remaining arm compares the offset against the
/// range's length as a *term*, which is a signed order over that term's value
/// and needs no count.
pub(in crate::kernel) fn element_delta_in_range_by_affine_arithmetic(
    delta: &ExactElementDelta,
    start: &Bitvector32Term,
    end: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    let recorded_exact_order_path = |left: &Bitvector32Term,
                                     right: &Bitvector32Term,
                                     strict: bool| {
        let Some(path) = assumptions.exact_signed_order_path_evidence(left, right, strict) else {
            return false;
        };
        for step in path {
            record_implicit_reasoning_provenance(assumptions, &step.premise);
        }
        true
    };
    let Some(offset) = exact_affine_index_difference(&delta.index, start, Some(assumptions))
        .and_then(|difference| difference.checked_add(delta.constant))
    else {
        return false;
    };
    if offset < 0 {
        return false;
    }
    if let Some(count) = affine_range_element_count(start, end) {
        return offset < count;
    }
    i32::try_from(offset).is_ok_and(|offset| {
        affine_bitvector_difference_atom(end, start).is_some_and(|length| {
            recorded_exact_order_path(&Bitvector32Term::Constant(offset as u32), &length, true)
                || assumptions.should_defer_non_exact_condition_reasoning()
                    && assumptions.difference_graph_proves_order(
                        &Bitvector32Term::Constant(offset as u32),
                        &length,
                        true,
                    )
        })
    })
}

/// An upper bound on the number of elements `start..end` can really span, for
/// a rule about to read an affine constant difference as an order.
///
/// [`affine_bitvector_difference_constant`] computes in `i64` while its
/// arguments are modular 32-bit terms, so what it returns is the true
/// difference only *modulo* `2^32`. That is enough for a disequality — the
/// residue is nonzero — and not enough for an order: `i + 1` is one above `i`
/// only while the 32-bit add does not wrap. What an order conclusion can still
/// get from a residue is membership, because an index whose residue from the
/// range's start is at least the range's element count is outside the range
/// whichever way the terms wrapped. That needs the count bounded, and this is
/// the bound.
///
/// Two sources, in order of cost. A constant affine element count *is* the
/// count when it sits in `0..=i32::MAX`, so the ordinary shapes — `p[i..i + 1]`,
/// `p[0..3]` — carry their own bound and consult nothing. Otherwise the range's
/// own valid-byte-extent facts supply it, which is the condition a stated
/// `owns`/`views` range already brings. A range with neither is refused:
/// default-deny, since an unbounded span admits a residue that wrapped all the
/// way around.
pub(in crate::kernel) fn affine_range_element_count_bound(
    start: &Bitvector32Term,
    end: &Bitvector32Term,
    element_width: u32,
    assumptions: &PureFactContext,
) -> Option<i64> {
    if let Some(count) = affine_bitvector_difference_constant(end, start)
        && (0..=i64::from(i32::MAX)).contains(&count)
    {
        return Some(count);
    }
    assumptions.established_range_element_count_bound(start, end, element_width)
}

/// The number of elements a range spans, when its endpoints' affine difference
/// determines it. This is the count itself, not a bound.
///
/// A range `p[start..end)` denotes `memory_range_byte_count` bytes from the
/// address of element `start`, and that byte count is the modular term
/// `(end - start) * width`. So the element count is the *signed* value of the
/// 32-bit term `end - start`, which is the residue of an affine constant
/// difference read as `int32` — exactly, with nothing assumed: the affine walk
/// is faithful modulo `2^32`, and modulo `2^32` is all the count is. A residue
/// in the upper half is a negative count, a reversed range that holds no cells
/// and fails its own valid-extent guard, and this answers `None` for it rather
/// than a count no conclusion should use.
///
/// Contrast [`affine_range_element_count_bound`], which answers for a range
/// whose endpoints have *no* constant difference by consulting its extent
/// facts. A bound is all an "outside" conclusion needs; a membership
/// conclusion needs the count.
pub(in crate::kernel) fn affine_range_element_count(
    start: &Bitvector32Term,
    end: &Bitvector32Term,
) -> Option<i64> {
    let residue = affine_bitvector_difference_constant(end, start)?.rem_euclid(1i64 << 32);
    (residue < (1i64 << 31)).then_some(residue)
}

/// Whether an affine constant difference between two element-index terms is
/// their true difference in `i64`, and not merely that difference modulo
/// `2^32`.
///
/// This is the premise every *positive* membership conclusion needs and no
/// negative one does, and it is the whole difference between the two. Write
/// `D = sext(index) - sext(start)` for the true difference and `r` for the
/// residue the affine walk yields. Both terms are `int32`, so `D` lies in
/// `(-2^32, 2^32)`, and `D ≡ r (mod 2^32)` pins it to `D ∈ {r, r - 2^32}`.
///
/// "Outside" needs no more: `r - 2^32` is negative, so below the start, and `r`
/// above the count is past the end — outside under either reading, which is
/// what [`affine_offset_from_start_is_outside`] uses. "Inside" needs `D = r`
/// outright, because `D = r - 2^32` is *outside*. `i + 1` is one element above
/// `i` only while the add does not wrap; at `i == i32::MAX` it is `2^32 - 1`
/// elements below.
///
/// Three routes rule the wrapped reading out, and each is checked before any
/// fact lookup.
///
/// * `r == 0`. Then `D` is `0` or `-2^32`, and `-2^32` is out of reach, so the
///   two terms name the same element. This is the route that carries the
///   ordinary shapes — a child range starting where its parent does, a pointer
///   at a range's own start — with no context at all.
/// * `r` in the upper half is refused. `D = r >= 2^31` would need the index
///   `2^31` elements above the start, and a range that reaches that far fails
///   its valid-extent guard, so a membership caller cannot want it; refusing
///   costs nothing and keeps the argument below to the low half.
/// * Otherwise `D = r - 2^32 <= -2^31 - 1`, which forces `sext(index) < 0` and
///   `sext(start) > 0` together: with `sext(index) >= 0` the difference is at
///   least `-sext(start) > -2^31`, and with `sext(start) <= 0` it is at least
///   `sext(index) >= -2^31`. So *either* `0 <= index` *or* `start <= 0`
///   excludes it. A constant endpoint settles its own side without consulting
///   anything, which is why a range over `p[0..n]` and a constant index need no
///   facts; otherwise the order comes from the same exact routes a stated
///   extent guard is checked by.
///
/// Default-deny: a caller with no context gets the fact-free routes only.
/// Whether an element-index term is known nonnegative, by exact routes only:
/// its own constant value, or the same order routes a stated extent guard is
/// checked by. This is the premise that keeps a 32-bit subtraction of two
/// indices inside `int32`, which several conclusions below need and none may
/// assume.
pub(in crate::kernel) fn element_index_is_nonnegative(
    term: &Bitvector32Term,
    assumptions: Option<&PureFactContext>,
) -> bool {
    signed_bitvector_constant(term).is_some_and(|value| 0 <= value)
        || assumptions.is_some_and(|assumptions| {
            assumptions.proves_element_endpoint_order(&Bitvector32Term::Constant(0), term)
        })
}

fn affine_index_difference_is_exact(
    index: &Bitvector32Term,
    start: &Bitvector32Term,
    difference: i64,
    assumptions: Option<&PureFactContext>,
) -> bool {
    let residue = difference.rem_euclid(1i64 << 32);
    if residue == 0 {
        return true;
    }
    if residue >= (1i64 << 31) {
        return false;
    }
    if element_index_is_nonnegative(index, assumptions) {
        return true;
    }
    signed_bitvector_constant(start).is_some_and(|start| start <= 0)
        || assumptions.is_some_and(|assumptions| {
            assumptions.proves_element_endpoint_order(start, &Bitvector32Term::Constant(0))
        })
}

/// The true `i64` difference `sext(index) - sext(start)` of two element-index
/// terms, when an affine constant difference determines it.
///
/// Two constants answer outright, difference and sign included. Otherwise the
/// answer is the residue, and only once [`affine_index_difference_is_exact`]
/// has ruled out the wrapped reading of it — so a symbolic answer is always in
/// `0..2^31`, and a caller that needs a *negative* difference between symbolic
/// terms gets `None` rather than a residue standing in for one.
pub(in crate::kernel) fn exact_affine_index_difference(
    index: &Bitvector32Term,
    start: &Bitvector32Term,
    assumptions: Option<&PureFactContext>,
) -> Option<i64> {
    if let (Some(index), Some(start)) = (
        signed_bitvector_constant(index),
        signed_bitvector_constant(start),
    ) {
        return Some(index - start);
    }
    let difference = affine_bitvector_difference_constant(index, start)?;
    affine_index_difference_is_exact(index, start, difference, assumptions)
        .then(|| difference.rem_euclid(1i64 << 32))
}

/// Whether a range's element count is a real count and not a residue standing
/// for a negative span — `0 <= end - start`, the forward half of the one
/// valid-byte-extent condition, which is all this needs and the width limit is
/// not part of.
///
/// This is the premise for comparing two ranges' *ends* rather than their
/// counts. Write `offset` for how far the child starts into the parent and
/// `slack` for how far the parent's end reaches past the child's; both are
/// exact `i64`, and whatever the endpoints did,
/// `parent_count - child_count ≡ offset + slack (mod 2^32)`. Both counts are
/// residues read as `int32`, so they lie in `[-2^31, 2^31)`; a *nonnegative*
/// parent count puts their difference in `(-2^31, 2^32)`, and `offset + slack`
/// in `[0, 2^31)` is then the only value in that window congruent to it. So
/// the difference *is* `offset + slack`, and `slack >= 0` is exactly
/// `offset + child_count <= parent_count`.
///
/// Without it a range may be forward and valid with its endpoints nowhere near
/// each other: `p[i32::MAX..i32::MIN]` holds exactly one element, and reading
/// its `end` as `start + count` would place that element `2^32` away.
///
/// A reach of zero needs nothing at all: the two ranges then start at one
/// address and end at one address, so their counts are residues of the same
/// value and are equal.
// Exact-arithmetic containment handles wide ranges before calling this helper.
fn range_count_is_nonnegative(range: &CMemoryRange, assumptions: Option<&PureFactContext>) -> bool {
    if affine_range_element_count(range.start(), range.end()).is_some() {
        return true;
    }
    assumptions.is_some_and(|assumptions| {
        assumptions.proves_element_endpoint_order(
            &Bitvector32Term::Constant(0),
            &crate::kernel::memory_range_element_count(range),
        )
    })
}

/// Whether an affine constant difference from a range's start places the index
/// outside a range spanning at most `count_bound` elements.
///
/// The difference is the true one modulo `2^32`; taking its residue, the index
/// sits `residue` elements above the start or `residue - 2^32` below it. The
/// second is negative, so below the start either way; the first is outside once
/// it reaches the element count. A residue above any bound on that count is
/// therefore outside the range under both readings, with no no-overflow fact
/// needed.
fn affine_offset_from_start_is_outside(difference: i64, count_bound: i64) -> bool {
    difference.rem_euclid(1i64 << 32) > count_bound
}

/// Whether an affine constant difference from a range's *end* places the index
/// at or above the range, for a range spanning at most `count_bound` elements.
///
/// The index sits `residue` elements above the end, so its offset from the
/// start is `residue + count`. That stays at or above the count — outside —
/// unless it wraps, which it cannot while `residue + count` is below `2^32`.
fn affine_offset_from_end_is_outside(difference: i64, count_bound: i64) -> bool {
    difference.rem_euclid(1i64 << 32) < (1i64 << 32) - count_bound
}

fn bitvector_index_outside_range_shallow(
    index: &Bitvector32Term,
    start: &Bitvector32Term,
    end: &Bitvector32Term,
    element_width: u32,
    assumptions: &PureFactContext,
) -> bool {
    if let (Some(index), Some(start), Some(end)) = (
        signed_bitvector_constant(index),
        signed_bitvector_constant(start),
        signed_bitvector_constant(end),
    ) {
        return index < start || end <= index;
    }
    if assumptions.exact_condition_value(&ConditionTerm::signed_less_than(
        index.clone(),
        start.clone(),
    )) == Some(true)
        || assumptions.has_exact_order_path(index, start, true)
        || assumptions.exact_condition_value(&ConditionTerm::signed_less_equal(
            end.clone(),
            index.clone(),
        )) == Some(true)
        || assumptions.has_exact_order_path(end, index, false)
    {
        return true;
    }
    // The affine routes read a constant difference as a signed order, which it
    // is not: the terms are modular, so the difference is the true one only
    // modulo 2^32. What survives is membership, against a bound on how far the
    // range reaches; without such a bound this concludes nothing.
    let Some(count_bound) =
        affine_range_element_count_bound(start, end, element_width, assumptions)
    else {
        return false;
    };
    affine_bitvector_difference_constant(index, start)
        .is_some_and(|offset| affine_offset_from_start_is_outside(offset, count_bound))
        || affine_bitvector_difference_constant(index, end)
            .is_some_and(|offset| affine_offset_from_end_is_outside(offset, count_bound))
}

/// Whether a pointer addresses one of the cells of `base[start..end)`, from
/// arithmetic alone, plus `assumptions` when the caller holds a context.
///
/// This is a membership conclusion, so every quantity it compares has to be the
/// real one. A range denotes `count` elements from the address of element
/// `start`, and the pointer names the address `base + delta * width`, so what
/// membership means is the `i64` statement `0 <= delta - sext(start) < count`.
/// Each of the three pieces is read exactly:
/// [`Pointer::exact_element_delta_from_base`] for `delta`, so a folded sum of
/// byte offsets cannot pass off a residue as one;
/// [`exact_affine_index_difference`] for the subtraction, which is where the
/// wrap that `p[i..i + 1]` hides at `i == i32::MAX` would be; and
/// [`affine_range_element_count`] for the count.
fn pointer_in_range_shallow(
    pointer: &Pointer,
    base: &Pointer,
    start: &Bitvector32Term,
    end: &Bitvector32Term,
    element_width: u32,
    assumptions: Option<&PureFactContext>,
) -> bool {
    let Some(delta) = pointer.exact_element_delta_from_base(base, element_width, assumptions)
    else {
        return false;
    };
    // A zero-based symbolic range needs no affine constant count: its
    // signed endpoint is its count. Exact bounds put the unshifted index
    // inside it, and the extent guard prevents byte scaling from wrapping.
    // Keep nonzero starts and displacements on the exact-affine route below;
    // turning their modular sums into signed offsets would need more evidence.
    if start == &Bitvector32Term::Constant(0)
        && delta.constant == 0
        && let Some(assumptions) = assumptions
        && assumptions
            .established_range_element_count_bound(start, end, element_width)
            .is_some()
        && let Some(lower) = assumptions.exact_direct_order_step(start, &delta.index, false)
        && let Some(upper) = assumptions.exact_direct_order_step(&delta.index, end, true)
    {
        record_implicit_reasoning_provenance(assumptions, &lower.premise);
        record_implicit_reasoning_provenance(assumptions, &upper.premise);
        return true;
    }
    let Some(count) = affine_range_element_count(start, end) else {
        return false;
    };
    let Some(offset) = exact_affine_index_difference(&delta.index, start, assumptions)
        .and_then(|difference| difference.checked_add(delta.constant))
    else {
        return false;
    };
    0 <= offset && offset < count
}

pub(in crate::kernel) fn affine_bitvector_difference_constant(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> Option<i64> {
    let mut terms = BTreeMap::new();
    let mut constant = 0i64;
    collect_affine_bitvector_terms(left, 1, &mut terms, &mut constant)?;
    collect_affine_bitvector_terms(right, -1, &mut terms, &mut constant)?;
    terms.retain(|_, coefficient| *coefficient != 0);
    terms.is_empty().then_some(constant)
}

/// `term` as `coefficient * atom + constant` over one atom, by its affine
/// form, when it has exactly one atom with a nonzero coefficient.
pub(in crate::kernel) fn affine_bitvector_single_atom(
    term: &Bitvector32Term,
) -> Option<(Bitvector32Term, i64, i64)> {
    let mut terms = BTreeMap::new();
    let mut constant = 0i64;
    collect_affine_bitvector_terms(term, 1, &mut terms, &mut constant)?;
    terms.retain(|_, coefficient| *coefficient != 0);
    if terms.len() != 1 {
        return None;
    }
    let (atom, coefficient) = terms.into_iter().next()?;
    Some((atom, coefficient, constant))
}

fn affine_bitvector_difference_atom(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> Option<Bitvector32Term> {
    let mut terms = BTreeMap::new();
    let mut constant = 0i64;
    collect_affine_bitvector_terms(left, 1, &mut terms, &mut constant)?;
    collect_affine_bitvector_terms(right, -1, &mut terms, &mut constant)?;
    terms.retain(|_, coefficient| *coefficient != 0);
    if constant != 0 || terms.len() != 1 {
        return None;
    }
    let (term, coefficient) = terms.into_iter().next()?;
    (coefficient == 1).then_some(term)
}

fn collect_affine_bitvector_terms(
    term: &Bitvector32Term,
    coefficient: i64,
    terms: &mut BTreeMap<Bitvector32Term, i64>,
    constant: &mut i64,
) -> Option<()> {
    match term {
        Bitvector32Term::Constant(value) | Bitvector32Term::UInt32Constant(value) => {
            *constant = constant.checked_add(coefficient.checked_mul(i64::from(*value as i32))?)?;
        }
        binary_term!(Int32, Add, left, right) => {
            collect_affine_bitvector_terms(left, coefficient, terms, constant)?;
            collect_affine_bitvector_terms(right, coefficient, terms, constant)?;
        }
        binary_term!(Int32, Subtract, left, right) => {
            collect_affine_bitvector_terms(left, coefficient, terms, constant)?;
            collect_affine_bitvector_terms(right, coefficient.checked_neg()?, terms, constant)?;
        }
        binary_term!(Int32, Multiply, left, right) => {
            if let Some(value) = left.as_const() {
                collect_affine_bitvector_terms(
                    right,
                    coefficient.checked_mul(i64::from(value as i32))?,
                    terms,
                    constant,
                )?;
            } else {
                let value = right.as_const()?;
                collect_affine_bitvector_terms(
                    left,
                    coefficient.checked_mul(i64::from(value as i32))?,
                    terms,
                    constant,
                )?;
            }
        }
        atom => {
            // Atoms are keyed by their canonical form, so a load term and
            // its load variable cancel affinely; the verdict
            // stays assumption-free and check-identical because the
            // canonical form is deterministic.
            let current = terms
                .entry(crate::kernel::eval::canonical_term(atom))
                .or_default();
            *current = current.checked_add(coefficient)?;
        }
    }
    Some(())
}

impl ProofObligation {
    /// The ordinary indexed check for an evaluation requirement. Scoped
    /// quantifiers are discharged by proof operations, never by searching
    /// ambient quantified premises here.
    pub(crate) fn evaluation_requirement_is_established(
        assumptions: &PureFactContext,
        goal: &Proposition,
    ) -> bool {
        // Lowering can guard a native int32 universal's partial operation
        // with its own domain. Preserve only that existing reflexive route:
        // other binder sorts have distinct obligations, and logical
        // reflexivity must not erase a partial free expression's domain.
        fn reflexive_guard(goal: &Proposition) -> bool {
            let mut pending = vec![goal];
            while let Some(goal) = pending.pop() {
                crate::instrumentation::record_deterministic_work(1);
                match goal {
                    Proposition::ForAll {
                        sort: Sort::CInt32,
                        body,
                        ..
                    } => pending.push(body),
                    Proposition::And(left, right) => {
                        pending.extend([left.as_ref(), right.as_ref()])
                    }
                    Proposition::Implies(left, right) if left == right => {}
                    _ => return false,
                }
            }
            true
        }
        fn established(assumptions: &PureFactContext, goal: &Proposition) -> bool {
            if assumptions.states_required_goal(goal) || reflexive_guard(goal) {
                return true;
            }
            match goal {
                Proposition::And(left, right) => {
                    established(assumptions, left) && established(assumptions, right)
                }
                Proposition::ForAll { .. } | Proposition::Exists { .. } => false,
                _ => assumptions.proves_atomic_without_search(goal),
            }
        }
        established(assumptions, goal)
    }

    pub fn new(proposition: Proposition) -> Self {
        Self {
            proposition,
            context: None,
            assumable: true,
            evaluation_domain: false,
            call_requirement_site: None,
            introductions: None,
        }
    }

    pub fn verification_condition(proposition: Proposition) -> Self {
        Self {
            // A condition the kernel builds, such as a ranking decrease over
            // an Integer measure, is stated in the same one form as written
            // ones.
            proposition: canonical_observation_form(&proposition),
            context: None,
            assumable: false,
            evaluation_domain: false,
            call_requirement_site: None,
            introductions: None,
        }
    }

    pub(in crate::kernel) fn evaluation_domain(proposition: Proposition) -> Self {
        let mut obligation = Self::verification_condition(proposition);
        obligation.evaluation_domain = true;
        obligation
    }

    pub fn with_context(mut self, context: impl Into<String>) -> Self {
        self.context = Some(context.into());
        self
    }

    /// Attaches the head chain the lowering that produced this obligation's
    /// proposition recorded for it. One `Arc` clone per obligation copy; the
    /// chain itself is never rebuilt or scanned here.
    pub(super) fn with_introductions(
        mut self,
        introductions: crate::kernel::LoweringIntroductions,
    ) -> Self {
        self.introductions = Some(std::sync::Arc::new(introductions));
        self
    }

    /// The same chain, shared. Used when one obligation's record is carried
    /// onto the copy another collector keeps.
    pub(super) fn with_shared_introductions(
        mut self,
        introductions: Option<&std::sync::Arc<crate::kernel::LoweringIntroductions>>,
    ) -> Self {
        self.introductions = introductions.cloned();
        self
    }

    /// What lowering recorded about this obligation's outermost nodes, when
    /// a lowering built it. Indexed access by the consumer; no scan here.
    pub fn introductions(&self) -> Option<&crate::kernel::LoweringIntroductions> {
        self.introductions.as_deref()
    }

    /// The exact source-side identity for a required call precondition, when
    /// this obligation came from a selected callee contract.
    pub(crate) fn call_requirement_site(&self) -> Option<&std::sync::Arc<CallRequirementSource>> {
        self.call_requirement_site.as_ref()
    }

    /// Attach source-side call identity without changing the checked
    /// proposition identity used by obligation indexes.
    pub(crate) fn with_call_requirement_site(
        mut self,
        site: std::sync::Arc<CallRequirementSource>,
    ) -> Self {
        self.call_requirement_site = Some(site);
        self
    }

    pub(super) fn shared_introductions(
        &self,
    ) -> Option<&std::sync::Arc<crate::kernel::LoweringIntroductions>> {
        self.introductions.as_ref()
    }

    /// Whether this obligation is the impossible goal `false = true` the
    /// kernel owes where something is already refused. Its context is then
    /// the whole reason, and a caller whose proof of it failed reports that
    /// context instead of the attempt.
    pub fn is_impossible_goal(&self) -> bool {
        self.proposition == crate::kernel::loops::false_equals_true_proposition()
    }

    pub fn is_assumable(&self) -> bool {
        self.assumable
    }

    pub fn condition(condition: ConditionTerm, value: bool) -> Self {
        Self::new(Proposition::ConditionIs(condition, value))
    }

    pub fn memory_loadable_bytes(memory: CMemory, pointer: Pointer, byte_width: u32) -> Self {
        Self::new(Proposition::CMemoryLoadable {
            memory,
            base: pointer,
            bytes: Bitvector32Term::Constant(byte_width),
            wide: false,
        })
    }

    pub fn memory_can_store_bytes(memory: CMemory, pointer: Pointer, byte_width: u32) -> Self {
        Self::new(Proposition::CMemoryCanStore {
            memory,
            pointer,
            byte_width,
        })
    }

    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }

    pub fn context(&self) -> Option<&str> {
        self.context.as_deref()
    }

    pub(super) fn map_proposition(self, f: impl FnOnce(Proposition) -> Proposition) -> Self {
        Self {
            proposition: f(self.proposition),
            context: self.context,
            assumable: self.assumable,
            evaluation_domain: self.evaluation_domain,
            call_requirement_site: None,
            // The chain describes the head nodes of the proposition it was
            // recorded for. A rewrite adds or removes head nodes, so the
            // record is dropped rather than left describing another shape.
            introductions: None,
        }
    }
}

impl ExecutionPureFact {
    /// Retain the exact typed producer's definition and checked cached value.
    /// Used when a checked expression's value outlives its temporary fact
    /// stream (for example, an owned recursive child index). Definitions are
    /// unconditional; a cached value reached through an alias stays local to
    /// this proof context. Neither grants permission to read the cell.
    pub(in crate::kernel) fn retain_pointer_read_definition(&self, context: &PureFactContext) {
        if !self.is_certified() {
            return;
        }
        if self.is_logical_read_equation() {
            match self.proposition() {
                Proposition::ConditionIs(ConditionTerm::PointerValueEqual(left, right), true) => {
                    context
                        .equality_graph
                        .add_checked_pointer_value_equality(left, right);
                    return;
                }
                // A complete value equation simplifies to address equality
                // when its designation and bounds already match. Retain that
                // exact producer conclusion without adding object authority.
                Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) => {
                    context
                        .equality_graph
                        .add_checked_read_equality(left, right);
                    return;
                }
                _ => {}
            }
        }
        let Some(
            binding @ GeneratedLoadBinding::Exact {
                variable,
                pointer: address,
                load: Bitvector32Term::MemoryLoad(memory, _, _),
                typed_pointer_value: Some(value),
                observed_pointer_read,
                ..
            },
        ) = self.generated_load_binding()
        else {
            return;
        };
        if generated_load_binding_matches_proposition(binding, self.proposition())
            && crate::kernel::eval::typed_pointer_read_variable(value) == Some(*variable)
        {
            context.register_checked_pointer_read(value, memory, address);
            if let Some((observed_memory, observed_address)) = observed_pointer_read {
                context.equality_graph.add_checked_read_equality(
                    value,
                    &Pointer::loaded_value(observed_memory, observed_address),
                );
            }
        }
    }

    pub fn new(proposition: Proposition) -> Self {
        Self {
            proposition,
            public: true,
            certified: false,
            logical_read_equation: false,
            join_summary: false,
            certified_store: None,
            transport: None,
            generated_load_binding: None,
            generated_load_source_events: Default::default(),
            reference_observation: Default::default(),
        }
    }

    pub(super) fn internal(proposition: Proposition) -> Self {
        Self {
            proposition,
            public: false,
            certified: false,
            logical_read_equation: false,
            join_summary: false,
            certified_store: None,
            transport: None,
            generated_load_binding: None,
            generated_load_source_events: Default::default(),
            reference_observation: Default::default(),
        }
    }

    /// The memory summary of a checked interface join: what the arms'
    /// effects, each already checked against its own chain, may have
    /// written between the split and the joined memory.
    ///
    /// A join's memory is its arms' abstraction, which also forgets values
    /// no arm wrote, so the summary cannot be derived again from its two
    /// endpoints the way a store's or a call's can. An enclosing join takes
    /// it as the checked fact it is.
    pub(super) fn certified_join_summary(proposition: Proposition) -> Self {
        Self {
            join_summary: true,
            ..Self::certified(proposition)
        }
    }

    pub(crate) fn is_join_summary(&self) -> bool {
        self.certified && self.join_summary
    }

    pub(super) fn certified(proposition: Proposition) -> Self {
        Self {
            proposition,
            public: true,
            certified: true,
            logical_read_equation: false,
            join_summary: false,
            certified_store: None,
            transport: None,
            generated_load_binding: None,
            generated_load_source_events: Default::default(),
            reference_observation: Default::default(),
        }
    }

    pub(in crate::kernel) fn logical_read_equation(value: CPointerValue, read: Pointer) -> Self {
        let read = CPointerValue::new(read, value.c_type());
        Self::logical_pointer_value_equation(value, read)
    }

    pub(in crate::kernel) fn logical_pointer_value_equation(
        left: CPointerValue,
        right: CPointerValue,
    ) -> Self {
        Self {
            logical_read_equation: true,
            ..Self::certified(Proposition::ConditionIs(
                ConditionTerm::pointer_value_equal(left, right),
                true,
            ))
        }
    }

    pub(in crate::kernel) fn is_logical_read_equation(&self) -> bool {
        self.certified && self.logical_read_equation
    }

    pub(super) fn certified_store(
        before: CMemory,
        after: CMemory,
        pointer: Pointer,
        value: CValue,
        authorized_range: Option<CMemoryRange>,
    ) -> Self {
        Self {
            proposition: Proposition::CMemoryMutatesOnly {
                before: before.clone(),
                after: after.clone(),
                writes: vec![(pointer.clone(), value.byte_width())],
            },
            public: false,
            certified: true,
            logical_read_equation: false,
            join_summary: false,
            certified_store: Some(Box::new(CertifiedMemoryStore {
                before,
                after,
                pointer,
                value,
                authorized_range,
                source: Default::default(),
            })),
            transport: None,
            generated_load_binding: None,
            generated_load_source_events: Default::default(),
            reference_observation: Default::default(),
        }
    }

    pub(super) fn into_certified(mut self) -> Self {
        self.certified = true;
        self
    }

    pub(crate) fn with_proposition(mut self, proposition: Proposition) -> Self {
        if self.proposition != proposition
            || self.generated_load_binding.as_ref().is_some_and(|binding| {
                !generated_load_binding_matches_proposition(binding, &proposition)
            })
            || !self.reference_observation.matches_proposition(&proposition)
        {
            // A transported or rewritten fact no longer denotes the exact
            // producer equation.  Retaining its binding would let a later
            // surface consumer infer an epoch or pointer from a different
            // proposition.
            self.logical_read_equation = false;
            self.generated_load_binding = None;
            self.generated_load_source_events = Default::default();
            self.reference_observation = Default::default();
            if let Some(store) = &mut self.certified_store {
                store.source = Default::default();
            }
        }
        self.proposition = proposition;
        self
    }

    pub(crate) fn with_generated_load_binding(mut self, binding: GeneratedLoadBinding) -> Self {
        self.generated_load_binding = Some(Box::new(binding));
        self
    }

    pub(crate) fn with_generated_load_source_event(
        mut self,
        event: GeneratedLoadSourceEvent,
    ) -> Self {
        self.generated_load_source_events.push(event);
        self
    }

    pub(crate) fn generated_load_source_events(&self) -> &[GeneratedLoadSourceEvent] {
        self.generated_load_source_events.as_slice()
    }

    pub(crate) fn certified_transport(
        source: Proposition,
        target: Proposition,
        theorem: Theorem,
    ) -> Self {
        Self {
            proposition: target,
            public: false,
            certified: true,
            logical_read_equation: false,
            join_summary: false,
            certified_store: None,
            transport: Some(Box::new(CertifiedExecutionFactTransport {
                source,
                theorem,
            })),
            generated_load_binding: None,
            generated_load_source_events: Default::default(),
            reference_observation: Default::default(),
        }
    }

    pub(crate) fn transport_source(&self) -> Option<&Proposition> {
        self.transport.as_ref().map(|transport| &transport.source)
    }

    pub(crate) fn transport_theorem(&self) -> Option<&Theorem> {
        self.transport.as_ref().map(|transport| &transport.theorem)
    }

    pub(crate) fn generated_load_binding(&self) -> Option<&GeneratedLoadBinding> {
        self.generated_load_binding.as_deref()
    }

    pub fn condition(condition: ConditionTerm, value: bool) -> Self {
        Self::new(Proposition::ConditionIs(condition, value))
    }

    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }

    pub(crate) fn is_public(&self) -> bool {
        self.public
    }

    pub(crate) fn is_certified(&self) -> bool {
        self.certified
    }

    pub(super) fn certified_store_data(&self) -> Option<&CertifiedMemoryStore> {
        self.certified_store.as_deref()
    }
}

/// A generated-load binding is valid only while its exact defining equation
/// still embeds the producer's memory snapshot and pointer.  Structural
/// proposition equality intentionally ignores this distinction for some
/// memory values, so it cannot be the authority for retaining the binding.
fn generated_load_binding_matches_proposition(
    binding: &GeneratedLoadBinding,
    proposition: &Proposition,
) -> bool {
    let GeneratedLoadBinding::Exact {
        variable,
        snapshot,
        pointer,
        load,
        ..
    } = binding
    else {
        return true;
    };
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        },
        true,
    ) = proposition
    else {
        return false;
    };
    let (
        Bitvector32Term::Variable(proposition_variable),
        Bitvector32Term::MemoryLoad(memory, proposition_pointer, _),
    ) = (left.as_ref(), right.as_ref())
    else {
        return false;
    };
    proposition_variable == variable
        && snapshot == &CMemorySnapshotIdentity::of(memory.memory())
        && proposition_pointer.as_ref() == pointer
        && load == right.as_ref()
}

impl SymbolicCExecution {
    pub fn paths(&self) -> &[SymbolicCExecutionPath] {
        &self.paths
    }

    pub fn limit(&self) -> Option<ExecutionLimit> {
        self.limit
    }
}

impl SymbolicCExecutionPath {
    /// The entry premises this path was checked under.
    pub fn assumptions(&self) -> &PureFactContext {
        &self.assumptions
    }

    pub fn facts(&self) -> &ExecutionFacts {
        &self.facts
    }

    pub fn effect_facts(&self) -> &ExecutionFacts {
        &self.effect_facts
    }

    pub fn execution_facts(&self) -> ExecutionFacts {
        let mut facts = self.facts.clone();
        let effects = self.effect_facts.filtered(|fact| !facts.contains(fact));
        facts.extend_shared(&effects);
        facts
    }

    pub fn obligations(&self) -> &[ProofObligation] {
        &self.obligations
    }

    pub(crate) fn loan_evidence(&self) -> &crate::kernel::loans::CheckedLoanCallEvidenceSequence {
        &self.loan_evidence
    }

    pub fn theorem(&self) -> &Theorem {
        &self.theorem
    }
}

impl CFunctionExecutionCandidates {
    pub fn state(&self) -> &CState {
        &self.data.state
    }

    pub fn function(&self) -> &CFunction {
        &self.data.function
    }

    pub fn arguments(&self) -> &[CExpression] {
        &self.data.arguments
    }

    pub(crate) fn candidate_at(&self, index: usize) -> Option<&CFunctionExecutionCandidate> {
        self.data.paths.get(index)
    }
    pub(crate) fn path_count(&self) -> usize {
        self.data.paths.len()
    }
    pub(crate) fn common_facts_contain(&self, fact: &ExecutionPureFact) -> bool {
        self.data
            .common_facts
            .as_ref()
            .is_some_and(|facts| facts.contains(fact))
    }

    pub fn paths(&self) -> &[CFunctionExecutionCandidate] {
        self.data.paths.as_slice_with(|paths| {
            #[cfg(test)]
            ExecutionFacts::record_published_storage(
                false,
                paths.len(),
                paths
                    .iter()
                    .flat_map(|path| [path.facts(), path.effect_facts()]),
            );
            #[cfg(not(test))]
            let _ = paths;
        })
    }
}

#[cfg(test)]
thread_local! {
    static MATERIALIZED_EXECUTION_FACTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// How many facts [`CFunctionExecutionCandidate::execution_facts`] has
/// merged into fresh streams on this thread.
#[cfg(test)]
pub(crate) fn materialized_execution_facts() -> usize {
    MATERIALIZED_EXECUTION_FACTS.with(std::cell::Cell::get)
}

#[cfg(test)]
pub(crate) fn count_materialized_execution_facts(count: usize) {
    MATERIALIZED_EXECUTION_FACTS.with(|counter| counter.set(counter.get() + count));
}

impl CFunctionExecutionCandidate {
    pub(crate) fn shares_record_with(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.data, &other.data)
    }
    pub fn outcome(&self) -> &CFunctionOutcome {
        &self.data.outcome
    }

    pub fn facts(&self) -> &ExecutionFacts {
        &self.data.facts
    }

    pub fn effect_facts(&self) -> &ExecutionFacts {
        &self.data.effect_facts
    }

    pub fn execution_facts(&self) -> ExecutionFacts {
        #[cfg(test)]
        count_materialized_execution_facts(self.data.facts.len() + self.data.effect_facts.len());
        let mut facts = self.data.facts.clone();
        let effects = self
            .data
            .effect_facts
            .filtered(|fact| !facts.contains(fact));
        facts.extend_shared(&effects);
        facts
    }

    pub fn obligations(&self) -> &[ProofObligation] {
        &self.data.obligations
    }

    pub(crate) fn loan_evidence(&self) -> &crate::kernel::loans::CheckedLoanCallEvidenceSequence {
        &self.data.loan_evidence
    }
}

impl SymbolicCConditionEvaluation {
    pub fn paths(&self) -> &[SymbolicCConditionEvaluationPath] {
        &self.paths
    }

    pub fn limit(&self) -> Option<ExecutionLimit> {
        self.limit
    }
}

impl SymbolicCConditionEvaluationPath {
    pub fn facts(&self) -> &ExecutionFacts {
        &self.facts
    }

    pub fn obligations(&self) -> &[ProofObligation] {
        &self.obligations
    }

    pub fn theorem(&self) -> &Theorem {
        &self.theorem
    }
}

#[cfg(test)]
mod stated_requirement_tests {
    use super::*;

    fn requirement(var: u64, name: &str) -> Proposition {
        Proposition::Exists {
            name: name.into(),
            var: Variable(var),
            sort: Sort::Bitvector32,
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(Bitvector32Term::Variable(Variable(var))),
                    right: Box::new(Bitvector32Term::Constant(4)),
                },
                true,
            )),
        }
    }

    #[test]
    fn stated_quantified_requirement_survives_alpha_renaming_and_restriction() {
        let fact = requirement(100, "fact");
        let renamed = requirement(200, "goal");
        let context = PureFactContext::new().assume_proposition(fact);
        assert!(context.states_required_goal(&renamed));
        assert!(
            !context
                .restricted_to_facts(&[], &[])
                .states_required_goal(&renamed)
        );
        assert!(
            !context
                .without_exact_fact(&requirement(100, "fact"))
                .states_required_goal(&renamed)
        );

        let sibling = PureFactContext::new();
        assert!(!sibling.states_required_goal(&renamed));
        assert!(context.states_required_goal(&renamed));
    }

    #[test]
    fn stated_query_assembles_conjunction_but_not_disjunction() {
        let left = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
        let right = Proposition::ConditionIs(ConditionTerm::Constant(false), false);
        let context = PureFactContext::new()
            .assume_proposition(left.clone())
            .assume_proposition(right.clone());
        let conjunction = Proposition::And(Box::new(left.clone()), Box::new(right.clone()));
        let disjunction = Proposition::Or(Box::new(left.clone()), Box::new(right.clone()));
        assert!(context.states_required_goal(&conjunction));
        assert!(!context.states_required_goal(&disjunction));
        let guarded = Proposition::Implies(Box::new(disjunction), Box::new(conjunction));
        assert!(context.states_required_goal(&guarded));
        assert!(!PureFactContext::new().states_required_goal(&guarded));
    }

    #[test]
    fn exhausted_identity_maintenance_fails_closed_after_fact_removal() {
        let fact = requirement(60_000, "fact");
        let renamed = requirement(60_001, "goal");
        let context = PureFactContext::new().assume_proposition(fact.clone());
        assert!(context.states_required_goal(&renamed));
        let tactic = crate::instrumentation::TacticEvent {
            source_tactic_path: None,
            claim: "stated_requirement_index_budget".into(),
            tactic_index: 0,
            tactic_name: "stated_requirement_index_budget".into(),
            class: "simple".into(),
            statement_index: 0,
            source_index: 0,
        };
        let limits = crate::instrumentation::TacticWorkLimits {
            simple: 1,
            smart: 1,
            control: 1,
        };
        let (weakened, _) = crate::instrumentation::with_tactic_work_limits(limits, || {
            crate::instrumentation::collect(|| {
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticStarted(tactic.clone()),
                );
                let weakened = context.without_exact_fact(&fact);
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticFailed(tactic.clone()),
                );
                weakened
            })
        });
        assert!(!weakened.states_required_goal(&renamed));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/assumptions/stated_requirement_tests.rs");
    }
}

#[cfg(test)]
mod dynamic_current_load_tests {
    use super::*;

    fn pointer() -> Pointer {
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    #[test]
    fn records_unmaterialized_loads_and_integer_machine_carriers() {
        let pointer = pointer();
        let memory = CMemory::new();
        let snapshot = crate::kernel::intern_c_memory_ref(&memory);
        let load = Bitvector32Term::MemoryLoad(
            snapshot,
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Int32,
        );
        let value = Term::CValue(CValue::Int64(load.clone()));
        assert_eq!(
            current_memory_loads_in_term(&value, &memory).unwrap(),
            vec![(pointer.clone(), 8)]
        );

        let integer = SharedIntegerTerm::intern(IntegerTerm::Machine(
            SharedMachineIntegerTerm::intern(MachineIntegerType::Int64, load),
        ));
        let condition = Term::Condition(ConditionTerm::IntegerEqual(
            integer,
            SharedIntegerTerm::intern(IntegerTerm::constant_i64(0)),
        ));
        assert_eq!(
            current_memory_loads_in_term(&condition, &memory).unwrap(),
            vec![(pointer, 8)]
        );
    }

    #[test]
    fn opaque_click_function_carrier_is_rejected() {
        let memory = CMemory::new();
        let term = Term::Bitvector32(Bitvector32Term::ClickFunctionApplication {
            name: "opaque".into(),
            arguments: Vec::new(),
        });
        assert!(current_memory_loads_in_term(&term, &memory).is_err());
    }
}

/// An arithmetic overflow question whose two operands are load variables
/// reading one cell, as `a -= a` reads `this->size` and `other.size` when
/// `other` is `*this`: the operands are one value, so the question is asked
/// of that value with itself. Two registry lookups, one pointer decision in
/// the graph, and exact cell lookups; nothing is searched.
fn aliased_operands(
    graph: &super::difference_graph::DifferenceGraph,
    condition: &ConditionTerm,
) -> Option<bool> {
    use ConditionTerm as C;
    let (ty, operation, a, b) =
        super::machine_integer::representation::overflow_operation(condition)?;
    let (Bitvector32Term::Variable(left), Bitvector32Term::Variable(right)) = (a, b) else {
        return None;
    };
    if left == right
        || !crate::kernel::eval::is_load_variable(left)
        || !crate::kernel::eval::is_load_variable(right)
        || crate::kernel::registered_load_kind_for_variable(left)?
            != crate::kernel::registered_load_kind_for_variable(right)?
    {
        return None;
    }
    let (left_memory, left_pointer) = crate::kernel::registered_load_for_variable(left)?;
    let (right_memory, right_pointer) = crate::kernel::registered_load_for_variable(right)?;
    let same_cell = graph.decide(&C::PointerEqual(
        Box::new(left_pointer.clone()),
        Box::new(right_pointer.clone()),
    )) == Some(true)
        || (left_pointer.block == right_pointer.block
            && graph.decide(&C::PointerOffsetEqual(
                Box::new(left_pointer.offset.clone()),
                Box::new(right_pointer.offset.clone()),
            )) == Some(true));
    // The two snapshots agree at the cell when they are one snapshot, or
    // when one materialized the other's read there (`this->size` read
    // first, then `other.size` from a snapshot that records it): an exact
    // cell lookup each way.
    let holds = |memory: &SharedCMemory, pointer: &Pointer, variable: &Variable| {
        matches!(
            memory.known_value(pointer),
            Some(CValue::Int32(Bitvector32Term::Variable(held))
                | CValue::Int64(Bitvector32Term::Variable(held))
                | CValue::UInt64(Bitvector32Term::Variable(held))) if held == *variable
        )
    };
    if !same_cell
        || !(left_memory == right_memory
            || holds(&right_memory, &left_pointer, left)
            || holds(&left_memory, &right_pointer, right))
    {
        return None;
    }
    let itself = super::machine_integer::representation::overflow_condition(
        ty,
        operation,
        Box::new(a.clone()),
        Box::new(a.clone()),
    )?;
    graph.decide(&itself)
}

/// `proposition` with each Integer comparison of exact observations replaced
/// by the native comparison it holds exactly when, as specification lowering
/// writes it: one fact, one form. A comparison whose native form folds to a
/// constant, such as a type-range bound, keeps its Integer form. The walk
/// visits each connective once.
pub(crate) fn canonical_observation_form(proposition: &Proposition) -> Proposition {
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            match native_comparison_of_integer_observation(condition, *value) {
                Some((ConditionTerm::Constant(_), _)) | None => proposition.clone(),
                Some((native, truth)) => Proposition::ConditionIs(native, truth),
            }
        }
        Proposition::Not(inner) => Proposition::Not(Box::new(canonical_observation_form(inner))),
        Proposition::And(left, right) => Proposition::And(
            Box::new(canonical_observation_form(left)),
            Box::new(canonical_observation_form(right)),
        ),
        Proposition::Or(left, right) => Proposition::Or(
            Box::new(canonical_observation_form(left)),
            Box::new(canonical_observation_form(right)),
        ),
        Proposition::Implies(left, right) => Proposition::Implies(
            Box::new(canonical_observation_form(left)),
            Box::new(canonical_observation_form(right)),
        ),
        other => other.clone(),
    }
}

/// The native comparison fact that an Integer comparison fact of exact
/// observations of one machine type holds exactly when it does
/// (`native_comparison_of_integer_observation`), or `None` for any other fact.
pub(crate) fn native_reading_of_integer_observation_fact(
    proposition: &Proposition,
) -> Option<Proposition> {
    let Proposition::ConditionIs(condition, value) = proposition else {
        return None;
    };
    let (native, truth) = native_comparison_of_integer_observation(condition, *value)?;
    Some(Proposition::ConditionIs(native, truth))
}

/// `condition`, an Integer order with a constant on one side, spelled with
/// the constant on the right (`c <= x` as `x >= c`); any other condition
/// as it is.
pub(crate) fn canonical_integer_bound_spelling(condition: &ConditionTerm) -> ConditionTerm {
    match condition {
        ConditionTerm::IntegerLessEqual(constant, exact) if constant.as_const().is_some() => {
            ConditionTerm::IntegerGreaterEqual(exact.clone(), constant.clone())
        }
        ConditionTerm::IntegerGreaterEqual(constant, exact) if constant.as_const().is_some() => {
            ConditionTerm::IntegerLessEqual(exact.clone(), constant.clone())
        }
        other => other.clone(),
    }
}

/// The two spellings of one non-strict Integer order, `a <= b` and
/// `b >= a`; any other condition alone.
fn integer_order_spellings(condition: &ConditionTerm) -> Vec<ConditionTerm> {
    match condition {
        ConditionTerm::IntegerLessEqual(left, right) => vec![
            condition.clone(),
            ConditionTerm::IntegerGreaterEqual(right.clone(), left.clone()),
        ],
        ConditionTerm::IntegerGreaterEqual(left, right) => vec![
            condition.clone(),
            ConditionTerm::IntegerLessEqual(right.clone(), left.clone()),
        ],
        other => vec![other.clone()],
    }
}

#[cfg(test)]
mod integer_observation_tests {
    use super::*;
    use crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison;
    use crate::kernel::primitives::IntegerTerm;
    use num_bigint::BigInt;

    fn observe(ty: MachineIntegerType, variable: u64) -> SharedIntegerTerm {
        IntegerTerm::from_machine(ty, Bitvector32Term::Variable(Variable(variable)))
            .expect("a machine variable has an exact observation")
            .into()
    }

    fn constant(value: i64) -> SharedIntegerTerm {
        IntegerTerm::Constant(BigInt::from(value)).into()
    }

    #[test]
    fn native_facts_close_exact_integer_observation_queries_in_the_same_scope() {
        let comparisons: [fn(SharedIntegerTerm, SharedIntegerTerm) -> ConditionTerm; 6] = [
            ConditionTerm::IntegerEqual,
            ConditionTerm::IntegerNotEqual,
            ConditionTerm::IntegerLessThan,
            ConditionTerm::IntegerLessEqual,
            ConditionTerm::IntegerGreaterThan,
            ConditionTerm::IntegerGreaterEqual,
        ];
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            for comparison in comparisons {
                for truth in [false, true] {
                    let condition = comparison(observe(ty, 801), observe(ty, 803));
                    let goal = Proposition::ConditionIs(condition.clone(), truth);
                    let (native, native_truth) =
                        native_comparison_of_integer_observation(&condition, truth).unwrap();
                    let parent = PureFactContext::new();
                    let child = parent.clone().assume_condition(native, native_truth);
                    assert!(child.contains_known(&goal));
                    assert!(child.contains_known(&Proposition::Not(Box::new(
                        Proposition::ConditionIs(condition.clone(), !truth),
                    ))));
                    assert!(!child.contains_assumed_exact(&goal));
                    assert!(!parent.contains_known(&goal));
                    assert!(!child.contains_known(&Proposition::ConditionIs(condition, !truth)));
                    assert!(!child.contains_known(&Proposition::ConditionIs(
                        comparison(observe(ty, 802), observe(ty, 803)),
                        truth,
                    )));
                }
            }
        }
    }

    #[test]
    fn a_definedness_bound_over_a_promoted_byte_reads_back_to_its_fact() {
        // `total + (int32)byte`: the byte's `int32` observation is the
        // byte's own, and the bound still names the `int32` overflow fact.
        // The byte is a C narrowing; its promotion names its word (rule K8),
        // so the overflow test reads the byte's word.
        let byte = Bitvector32Term::MachineIntegerCast {
            value: Box::new(Bitvector32Term::Variable(Variable(821))),
            source: MachineIntegerType::Int32,
            destination: MachineIntegerType::UInt8,
        };
        let promoted = Bitvector32Term::machine_integer_cast(
            MachineIntegerType::UInt8,
            MachineIntegerType::Int32,
            byte.clone(),
        );
        let condition = ConditionTerm::machine_overflows(
            MachineIntegerType::Int32,
            OverflowOperation::Add,
            Bitvector32Term::Variable(Variable(822)),
            promoted,
        );
        assert!(matches!(&condition, ConditionTerm::Overflows { right, .. } if **right == byte));
        let fact = Proposition::ConditionIs(condition, false);
        let bounds = integer_bounds_of_definedness(&fact);
        assert_eq!(bounds.len(), 2);
        for bound in &bounds {
            assert_eq!(definedness_of_integer_bound(bound).as_ref(), Some(&fact));
        }
    }

    #[test]
    fn a_narrow_observation_is_native_only_for_an_extended_word() {
        // A conversion's word is its value's extension, so its observation
        // compares as the signed 32-bit word and reads back exactly.
        let byte = Bitvector32Term::MachineIntegerCast {
            value: Box::new(Bitvector32Term::Variable(Variable(811))),
            source: MachineIntegerType::Int32,
            destination: MachineIntegerType::UInt8,
        };
        let observed: SharedIntegerTerm =
            IntegerTerm::from_machine(MachineIntegerType::UInt8, byte.clone())
                .unwrap()
                .into();
        let condition = ConditionTerm::IntegerLessThan(observed, constant(255));
        let (native, truth) = native_comparison_of_integer_observation(&condition, true).unwrap();
        assert_eq!(
            native,
            ConditionTerm::signed_less_than(byte, Bitvector32Term::Constant(255))
        );
        assert_eq!(
            integer_observations_of_native_comparison(&Proposition::ConditionIs(native, truth)),
            vec![Proposition::ConditionIs(condition, true)]
        );
        // An arbitrary word's byte is not the word: 256 is not below 255,
        // but its byte, 0, is.
        let sum = IntegerTerm::from_machine(
            MachineIntegerType::UInt8,
            binary_node!(
                Int32,
                Add,
                Box::new(Bitvector32Term::Variable(Variable(812))),
                Box::new(Bitvector32Term::Constant(1)),
            ),
        )
        .unwrap();
        let condition = ConditionTerm::IntegerLessThan(sum.into(), constant(255));
        assert!(native_comparison_of_integer_observation(&condition, true).is_none());
    }

    fn uint32_difference_from(value: i64, variable: u64) -> SharedIntegerTerm {
        IntegerTerm::Subtract(
            constant(value),
            observe(MachineIntegerType::UInt32, variable),
        )
        .into()
    }

    fn uint32_guard(value: u32, left: u64, right: u64) -> ConditionTerm {
        ConditionTerm::unsigned_less_equal(
            word(left),
            Bitvector32Term::subtract(Bitvector32Term::Constant(value), word(right)),
        )
    }

    fn uint64_max() -> SharedIntegerTerm {
        IntegerTerm::Constant(BigInt::from(u64::MAX)).into()
    }

    /// `forall (k: uint64) { antecedent implies word(832) == 0 }`.
    fn quantified_over_k(antecedent: Proposition) -> Proposition {
        Proposition::ForAll {
            var: Variable(830),
            sort: Sort::CMachineInteger(MachineIntegerType::UInt64),
            body: Box::new(Proposition::Implies(
                Box::new(antecedent),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::equal(word(832), Bitvector32Term::Constant(0)),
                    true,
                )),
            )),
            name: BinderName::written("k"),
        }
    }

    #[test]
    fn a_quantified_integer_antecedent_through_an_in_range_sum_files_its_native_reading() {
        // forall k { to_integer(k) < to_integer(len) + 1 implies ... } is
        // forall k { k < len + 1u64 implies ... } once len + 1 cannot wrap.
        let sum: SharedIntegerTerm =
            IntegerTerm::Add(observe(MachineIntegerType::UInt64, 831), constant(1)).into();
        let reading =
            ConditionTerm::IntegerLessThan(observe(MachineIntegerType::UInt64, 830), sum.clone());
        let (native, truth, _) = native_comparison_through_integer_operations(&reading, true)
            .expect("the sum has a native reading");
        let integer_fact = quantified_over_k(Proposition::ConditionIs(reading, true));
        let native_fact = quantified_over_k(Proposition::ConditionIs(native, truth));
        let unbounded = PureFactContext::new().assume_proposition(integer_fact.clone());
        assert!(!unbounded.contains_known(&native_fact));
        let bounded = PureFactContext::new()
            .assume_condition(ConditionTerm::IntegerLessEqual(sum, uint64_max()), true)
            .assume_proposition(integer_fact);
        assert!(bounded.contains_known(&native_fact));
    }

    #[test]
    fn a_quantified_antecedent_bound_that_names_the_binder_files_nothing() {
        // to_integer(k) + 1 <= to_integer(len) needs a bound on k + 1, which
        // differs for each k, so no fact about the context supplies it.
        let sum: SharedIntegerTerm =
            IntegerTerm::Add(observe(MachineIntegerType::UInt64, 830), constant(1)).into();
        let reading =
            ConditionTerm::IntegerLessEqual(sum.clone(), observe(MachineIntegerType::UInt64, 831));
        let (native, truth, _) = native_comparison_through_integer_operations(&reading, true)
            .expect("the sum has a native reading");
        let context = PureFactContext::new()
            .assume_condition(ConditionTerm::IntegerLessEqual(sum, uint64_max()), true)
            .assume_proposition(quantified_over_k(Proposition::ConditionIs(reading, true)));
        assert!(
            !context.contains_known(&quantified_over_k(Proposition::ConditionIs(native, truth)))
        );
    }

    #[test]
    fn an_integer_bound_through_an_in_range_difference_files_the_native_guard() {
        // to_integer(a) <= 4294967295 - to_integer(b) is a <= 4294967295u32 - b:
        // the difference cannot wrap, so no bound is needed.
        let reading = ConditionTerm::IntegerLessEqual(
            observe(MachineIntegerType::UInt32, 1),
            uint32_difference_from(4_294_967_295, 2),
        );
        let (_, _, bounds) = native_comparison_through_integer_operations(&reading, true).unwrap();
        assert!(bounds.is_empty());
        let context = PureFactContext::new().assume_condition(reading, true);
        assert_eq!(context.decide(&uint32_guard(u32::MAX, 1, 2)), Some(true));
    }

    #[test]
    fn a_difference_that_may_wrap_files_the_native_guard_only_with_its_bound() {
        // 4294967294 - to_integer(b) is below zero for b == 4294967295.
        let reading = ConditionTerm::IntegerLessEqual(
            observe(MachineIntegerType::UInt32, 1),
            uint32_difference_from(4_294_967_294, 2),
        );
        let (_, _, bounds) = native_comparison_through_integer_operations(&reading, true).unwrap();
        assert_eq!(bounds.len(), 1);
        assert!(bounds[0].lower);
        let unbounded = PureFactContext::new().assume_condition(reading.clone(), true);
        assert_ne!(
            unbounded.decide(&uint32_guard(u32::MAX - 1, 1, 2)),
            Some(true)
        );
        // The bound itself, in either spelling, then supplies the reading.
        for bound in [
            ConditionTerm::IntegerGreaterEqual(
                uint32_difference_from(4_294_967_294, 2),
                constant(0),
            ),
            ConditionTerm::IntegerLessEqual(constant(0), uint32_difference_from(4_294_967_294, 2)),
        ] {
            let bounded = PureFactContext::new()
                .assume_condition(bound, true)
                .assume_condition(reading.clone(), true);
            assert_eq!(
                bounded.decide(&uint32_guard(u32::MAX - 1, 1, 2)),
                Some(true)
            );
        }
        // A guard with a different constant is not this reading.
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::IntegerLessEqual(
                observe(MachineIntegerType::UInt32, 1),
                uint32_difference_from(4_294_967_295, 2),
            ),
            true,
        );
        assert_ne!(
            context.decide(&uint32_guard(u32::MAX - 1, 1, 2)),
            Some(true)
        );
    }

    #[test]
    fn a_sum_side_needs_its_upper_bound() {
        // to_integer(a) + to_integer(b) <= to_integer(c) reads as the native
        // a + b <= c only once the sum stays in uint32.
        let sum = || -> SharedIntegerTerm {
            IntegerTerm::Add(
                observe(MachineIntegerType::UInt32, 1),
                observe(MachineIntegerType::UInt32, 2),
            )
            .into()
        };
        let reading =
            ConditionTerm::IntegerLessEqual(sum(), observe(MachineIntegerType::UInt32, 3));
        let native =
            ConditionTerm::unsigned_less_equal(Bitvector32Term::add(word(1), word(2)), word(3));
        let unbounded = PureFactContext::new().assume_condition(reading.clone(), true);
        assert_ne!(unbounded.decide(&native), Some(true));
        let bounded = PureFactContext::new()
            .assume_condition(
                ConditionTerm::IntegerLessEqual(sum(), constant(4_294_967_295)),
                true,
            )
            .assume_condition(reading, true);
        assert_eq!(bounded.decide(&native), Some(true));
    }

    #[test]
    fn both_integer_bounds_of_a_signed_difference_file_its_definedness() {
        let overflow = ConditionTerm::signed_subtract_overflows(word(1), word(2));
        let upper = ConditionTerm::IntegerLessEqual(difference(1, 2), constant(2_147_483_647));
        let lowers = [
            ConditionTerm::IntegerGreaterEqual(difference(1, 2), constant(-2_147_483_648)),
            ConditionTerm::IntegerLessEqual(constant(-2_147_483_648), difference(1, 2)),
        ];
        let one = PureFactContext::new().assume_condition(upper.clone(), true);
        assert_ne!(one.decide(&overflow), Some(false));
        for lower in lowers {
            let one = PureFactContext::new().assume_condition(lower.clone(), true);
            assert_ne!(one.decide(&overflow), Some(false));
            for (first, second) in [(&upper, &lower), (&lower, &upper)] {
                let both = PureFactContext::new()
                    .assume_condition(first.clone(), true)
                    .assume_condition(second.clone(), true);
                assert_eq!(both.decide(&overflow), Some(false));
            }
        }
        // A bound one past the range is not the definedness bound.
        let wide = PureFactContext::new()
            .assume_condition(
                ConditionTerm::IntegerLessEqual(difference(1, 2), constant(2_147_483_648)),
                true,
            )
            .assume_condition(
                ConditionTerm::IntegerGreaterEqual(difference(1, 2), constant(-2_147_483_648)),
                true,
            );
        assert_ne!(wide.decide(&overflow), Some(false));
    }

    mod scaling_tests {
        use super::*;
        include!("../scaling_tests/kernel/assumptions/integer_observation_tests.rs");
    }

    fn word(variable: u64) -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(variable))
    }

    fn difference(left: u64, right: u64) -> SharedIntegerTerm {
        IntegerTerm::Subtract(
            observe(MachineIntegerType::Int32, left),
            observe(MachineIntegerType::Int32, right),
        )
        .into()
    }

    #[test]
    fn an_integer_equality_files_its_wrapped_word_equality() {
        // to_integer(a) - to_integer(b) == 0 implies the word a - b is 0.
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::IntegerEqual(difference(1, 2), constant(0)),
            true,
        );
        assert_eq!(
            context.decide(&ConditionTerm::equal(
                Bitvector32Term::subtract(word(1), word(2)),
                Bitvector32Term::Constant(0)
            )),
            Some(true)
        );
    }

    #[test]
    fn a_wrapped_word_equality_does_not_decide_its_integer_equality() {
        // The word a - b can be 0 when the Integer difference is 2^32.
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::equal(
                Bitvector32Term::subtract(word(1), word(2)),
                Bitvector32Term::Constant(0),
            ),
            true,
        );
        assert_ne!(
            context.decide(&ConditionTerm::IntegerEqual(difference(1, 2), constant(0))),
            Some(true)
        );
    }

    #[test]
    fn an_integer_order_over_arithmetic_files_no_word_fact() {
        let order = ConditionTerm::IntegerLessEqual(difference(1, 2), constant(0));
        assert_eq!(wrapped_equality_of_integer_equality(&order, true), None);
        let equality = ConditionTerm::IntegerEqual(difference(1, 2), constant(0));
        assert_eq!(wrapped_equality_of_integer_equality(&equality, false), None);
    }

    #[test]
    fn an_integer_bound_files_its_native_comparison() {
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::IntegerLessEqual(constant(0), observe(MachineIntegerType::Int32, 1)),
            true,
        );
        assert_eq!(
            context.decide(&ConditionTerm::signed_less_equal(
                Bitvector32Term::Constant(0),
                word(1)
            )),
            Some(true)
        );
    }

    #[test]
    fn an_unsigned_bound_files_the_unsigned_comparison() {
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::IntegerLessThan(observe(MachineIntegerType::UInt32, 1), constant(10)),
            true,
        );
        assert_eq!(
            context.decide(&ConditionTerm::unsigned_less_than(
                word(1),
                Bitvector32Term::Constant(10)
            )),
            Some(true)
        );
    }

    #[test]
    fn a_false_comparison_files_its_negation() {
        // not (to_integer(x) < 5) is 5 <= x.
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::IntegerLessThan(observe(MachineIntegerType::Int32, 1), constant(5)),
            false,
        );
        assert_eq!(
            context.decide(&ConditionTerm::signed_less_equal(
                Bitvector32Term::Constant(5),
                word(1)
            )),
            Some(true)
        );
    }

    #[test]
    fn an_integer_disequality_files_a_false_native_equality() {
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::IntegerNotEqual(
                observe(MachineIntegerType::Int32, 1),
                observe(MachineIntegerType::Int32, 2),
            ),
            true,
        );
        assert_eq!(
            context.decide(&ConditionTerm::equal(word(1), word(2))),
            Some(false)
        );
    }

    #[test]
    fn a_native_comparison_reads_back_as_its_integer_observation() {
        for (condition, truth) in [
            (
                ConditionTerm::IntegerLessEqual(
                    constant(1),
                    observe(MachineIntegerType::UInt32, 1),
                ),
                true,
            ),
            (
                ConditionTerm::IntegerLessThan(
                    observe(MachineIntegerType::Int32, 1),
                    observe(MachineIntegerType::Int32, 2),
                ),
                true,
            ),
            (
                ConditionTerm::IntegerLessEqual(
                    observe(MachineIntegerType::UInt64, 1),
                    constant(7),
                ),
                true,
            ),
            (
                ConditionTerm::IntegerEqual(observe(MachineIntegerType::Int64, 1), constant(-3)),
                false,
            ),
        ] {
            let (native, native_truth) =
                native_comparison_of_integer_observation(&condition, truth).unwrap();
            let fact = Proposition::ConditionIs(native.clone(), native_truth);
            let lifted = integer_observations_of_native_comparison(&fact);
            assert!(!lifted.is_empty(), "{condition:?}");
            for reading in lifted {
                let Proposition::ConditionIs(reading, reading_truth) = reading else {
                    unreachable!()
                };
                // Each reading files exactly the native fact it came from.
                assert_eq!(
                    native_comparison_of_integer_observation(&reading, reading_truth),
                    Some((native.clone(), native_truth))
                );
            }
        }
        // A native order the forward map spells the other way round, as
        // `x >= 1` is stated beside `1 <= x`, reads back as the same bound.
        let mirrored = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: Box::new(word(1)),
                right: Box::new(Bitvector32Term::Constant(1)),
            },
            true,
        );
        assert!(
            integer_observations_of_native_comparison(&mirrored).contains(
                &Proposition::ConditionIs(
                    ConditionTerm::IntegerLessEqual(
                        constant(1),
                        observe(MachineIntegerType::Int32, 1)
                    ),
                    true,
                )
            )
        );
        // The same holds in the 64-bit unsigned family, at either polarity:
        // `x >= 32u64` and a false `0u64 < x` read as their bounds.
        for (fact, reading) in [
            (
                ConditionTerm::Compare {
                    format: MachineIntegerType::UInt64,
                    relation: CompareRelation::GreaterEqual,
                    left: Box::new(word(1)),
                    right: Box::new(Bitvector32Term::UInt64Constant(32)),
                },
                ConditionTerm::IntegerLessEqual(
                    constant(32),
                    observe(MachineIntegerType::UInt64, 1),
                ),
            ),
            (
                ConditionTerm::Compare {
                    format: MachineIntegerType::UInt64,
                    relation: CompareRelation::LessThan,
                    left: Box::new(Bitvector32Term::UInt64Constant(0)),
                    right: Box::new(word(1)),
                },
                ConditionTerm::IntegerLessEqual(
                    observe(MachineIntegerType::UInt64, 1),
                    constant(0),
                ),
            ),
        ] {
            let truth = matches!(
                fact,
                ConditionTerm::Compare {
                    format: MachineIntegerType::UInt64,
                    relation: CompareRelation::GreaterEqual,
                    ..
                }
            );
            assert_eq!(
                integer_observations_of_native_comparison(&Proposition::ConditionIs(fact, truth)),
                vec![Proposition::ConditionIs(reading, true)]
            );
        }
        // Facts other than native comparisons read as nothing.
        assert!(
            integer_observations_of_native_comparison(&Proposition::ConditionIs(
                ConditionTerm::IntegerLessEqual(constant(1), observe(MachineIntegerType::Int32, 1)),
                true,
            ))
            .is_empty()
        );
    }

    #[test]
    fn a_native_fact_decides_its_integer_observation() {
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::signed_less_equal(word(1), Bitvector32Term::Constant(3)),
            true,
        );
        assert_eq!(
            context.decide(&ConditionTerm::IntegerLessEqual(
                observe(MachineIntegerType::Int32, 1),
                constant(3)
            )),
            Some(true)
        );
        assert_eq!(
            context.decide(&ConditionTerm::IntegerGreaterThan(
                observe(MachineIntegerType::Int32, 1),
                constant(3)
            )),
            Some(false)
        );
    }

    #[test]
    fn an_out_of_range_constant_files_nothing() {
        let condition = ConditionTerm::IntegerLessThan(
            observe(MachineIntegerType::Int32, 1),
            constant(i64::from(i32::MAX) + 1),
        );
        assert_eq!(
            native_comparison_of_integer_observation(&condition, true),
            None
        );
    }

    #[test]
    fn observations_of_different_types_file_nothing() {
        let condition = ConditionTerm::IntegerLessEqual(
            observe(MachineIntegerType::Int32, 1),
            observe(MachineIntegerType::UInt32, 2),
        );
        assert_eq!(
            native_comparison_of_integer_observation(&condition, true),
            None
        );
    }
}

/// An upper bound on the execution-range variables a context's facts
/// mention, kept as facts are filed without reading a snapshot's contents.
/// Filing a fact takes the ceiling of its written syntax into `base`; a fact
/// that names a snapshot is also queued in `pending`. The first execution
/// that asks takes each queued fact's whole ceiling, snapshots included,
/// and caches the result for this context version; the next fact filed
/// rebases on that result, so each queued fact is taken whole once along a
/// path. Forks share `pending` and the cache until one of them files a fact.
#[derive(Clone, Default)]
pub(super) struct ExecutionVariableCeiling {
    base: Option<Variable>,
    pending: crate::kernel::proof::PersistentSequence<ExecutionVariableCeilingFact>,
    cached: std::sync::Arc<std::sync::OnceLock<Option<Variable>>>,
}

#[derive(Clone)]
pub(super) enum ExecutionVariableCeilingFact {
    Condition(ConditionTerm),
    Proposition(Proposition),
}

impl std::fmt::Debug for ExecutionVariableCeiling {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ExecutionVariableCeiling")
            .field("base", &self.base)
            .field("pending", &self.pending.len())
            .finish()
    }
}

impl ExecutionVariableCeiling {
    fn file_condition(&mut self, condition: &ConditionTerm) {
        let (syntax, names_snapshot) =
            crate::kernel::reasoning::variable_collection::condition_syntax_execution_variable_ceiling(
                condition,
            );
        self.file(
            syntax,
            names_snapshot.then(|| ExecutionVariableCeilingFact::Condition(condition.clone())),
        );
    }

    fn file_proposition(&mut self, proposition: &Proposition) {
        let (syntax, names_snapshot) =
            crate::kernel::reasoning::variable_collection::proposition_syntax_execution_variable_ceiling(
                proposition,
            );
        self.file(
            syntax,
            names_snapshot.then(|| ExecutionVariableCeilingFact::Proposition(proposition.clone())),
        );
    }

    fn file(&mut self, syntax: Option<Variable>, deferred: Option<ExecutionVariableCeilingFact>) {
        if let Some(ceiling) = self.cached.get() {
            self.base = self.base.max(*ceiling);
            self.pending = Default::default();
        }
        self.base = self.base.max(syntax);
        if let Some(fact) = deferred {
            self.pending.push(fact);
        }
        self.cached = std::sync::Arc::new(std::sync::OnceLock::new());
    }

    fn get(&self) -> Option<Variable> {
        use crate::kernel::reasoning::variable_collection::{
            condition_execution_variable_ceiling, proposition_execution_variable_ceiling,
        };
        *self.cached.get_or_init(|| {
            self.pending
                .iter()
                .map(|fact| {
                    #[cfg(test)]
                    WHOLE_CEILING_FACTS.with(|count| count.set(count.get() + 1));
                    match fact {
                        ExecutionVariableCeilingFact::Condition(condition) => {
                            condition_execution_variable_ceiling(condition)
                        }
                        ExecutionVariableCeilingFact::Proposition(proposition) => {
                            proposition_execution_variable_ceiling(proposition)
                        }
                    }
                })
                .fold(self.base, Option::max)
        })
    }
}

#[cfg(test)]
mod execution_variable_ceiling_tests {
    use super::*;

    fn word(offset: i64) -> Pointer {
        Pointer {
            block: PointerBlock::Concrete("a".into()),
            offset: PointerOffsetTerm::Constant(offset),
        }
    }

    fn execution_variable(offset: u64) -> Variable {
        Variable(ExecutionBudget::KERNEL_VARIABLE_BASE + offset)
    }

    /// A fact naming a snapshot whose stored value holds `variable`, though
    /// the fact's own syntax names no variable.
    fn fact_over_snapshot_holding(variable: Variable) -> ConditionTerm {
        let memory = CMemory::new()
            .with_block("a", 8)
            .store(word(0), CValue::Int32(Bitvector32Term::Variable(variable)));
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory_ref(&memory),
                Box::new(word(4)),
                crate::kernel::LoadKind::Int32,
            )),
            right: Box::new(Bitvector32Term::Constant(0)),
        }
    }

    #[test]
    fn the_ceiling_covers_variables_only_a_named_snapshot_holds() {
        let context = PureFactContext::new();
        assert_eq!(context.execution_variable_ceiling(), None);
        let context = context
            .assume_condition(fact_over_snapshot_holding(execution_variable(7)), true)
            .assume_proposition(Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(Bitvector32Term::Variable(execution_variable(3))),
                    right: Box::new(Bitvector32Term::Constant(1)),
                },
                true,
            ));
        assert!(context.execution_variable_ceiling() >= Some(execution_variable(7)));
    }

    /// A composition fact's syntax ceiling is read from its context's cached
    /// canonical fact set: it agrees with walking every held fact, and the
    /// context one more fact derives computes only that insertion's path.
    #[test]
    fn composition_ceiling_reads_the_cached_fact_set() {
        let owned = |index: u64| {
            CResourceFact::own_memory(CMemoryRange::new(
                Pointer::symbolic(execution_variable(index)),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            ))
        };
        use crate::kernel::reasoning::variable_collection::{
            COLLECTED_RESOURCE_FACTS, collect_proposition_bitvector_variables,
            execution_variable_ceiling, proposition_syntax_execution_variable_ceiling,
        };
        let walked = |proposition: &Proposition| {
            execution_variable_ceiling(Some(false), |variables| {
                collect_proposition_bitvector_variables(proposition, variables)
            })
        };
        for size in [16u64, 64, 256] {
            let resources = (0..size).fold(ResourceContext::new(), |resources, index| {
                resources.unchecked_with_fact(owned(index))
            });
            let composition = Proposition::CResourceComposition(resources.clone());
            let ceiling = proposition_syntax_execution_variable_ceiling(&composition);
            assert_eq!(ceiling, walked(&composition), "size {size}");
            assert_eq!(ceiling, (Some(execution_variable(size - 1)), false));
            let next =
                Proposition::CResourceComposition(resources.unchecked_with_fact(owned(size)));
            COLLECTED_RESOURCE_FACTS.with(|count| count.set(0));
            let ceiling = proposition_syntax_execution_variable_ceiling(&next);
            assert_eq!(ceiling, (Some(execution_variable(size)), false));
            // A treap path: logarithmic in the held facts, where walking
            // the composition visits all `size + 1` of them.
            let visits = COLLECTED_RESOURCE_FACTS.with(Cell::get);
            assert!(
                visits <= 4 * size.ilog2() as usize,
                "size {size}: {visits} facts visited"
            );
        }
    }

    #[test]
    fn asking_after_every_fact_takes_each_snapshot_fact_whole_once() {
        for size in [8, 32] {
            WHOLE_CEILING_FACTS.with(|count| count.set(0));
            let mut context = PureFactContext::new();
            for index in 0..size {
                context = context.assume_condition(
                    fact_over_snapshot_holding(execution_variable(index as u64)),
                    true,
                );
                assert_eq!(
                    context.execution_variable_ceiling(),
                    Some(execution_variable(index as u64))
                );
            }
            assert_eq!(WHOLE_CEILING_FACTS.with(Cell::get), size, "size {size}");
        }
    }
}

#[cfg(test)]
mod framed_opaque_pointer_entry_tests {
    use super::*;
    mod scaling_tests {
        include!("../scaling_tests/kernel/assumptions/framed_opaque_pointer_entry_tests.rs");
    }
}

#[cfg(test)]
mod annotated_numeric_pointer_condition_tests {
    use super::*;

    #[test]
    fn address_conditions_ignore_annotations_without_equating_pointer_domains() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let _session = crate::kernel::VerificationSession::enter();
        let p = Pointer::symbolic(Variable(995_100));
        let q = Pointer::symbolic(Variable(995_101));
        let address = |p: Pointer| {
            Bitvector32Term::object_pointer_address(
                p,
                Some(CAccessClass::Scalar(CScalarClass::Int)),
            )
        };
        let source = ConditionTerm::uint64_equal(address(p.clone()), address(q.clone()));
        let target = crate::kernel::eval::c_pointer_comparison_condition(p.clone(), q.clone());
        for value in [false, true] {
            let context = PureFactContext::new().assume_condition(source.clone(), value);
            assert_eq!(context.fast_leaf_decision(&target, &[]), Some(value));
            assert!(!context.pointer_designations_match(
                &CPointerValue::new(p.clone(), CType::Int32Pointer),
                &CPointerValue::new(q.clone(), CType::Int32Pointer)
            ));
            let withdrawn =
                context.without_exact_fact(&Proposition::ConditionIs(source.clone(), value));
            assert_eq!(withdrawn.fast_leaf_decision(&target, &[]), None);
        }
    }
}

#[cfg(test)]
mod decided_algebraic_if_tests;

#[cfg(test)]
mod bool_sort_tests;

/// The order facts of a context, each filed as its own condition under the
/// lower end an order walk follows it from. The exact order walks
/// (`has_exact_order_path`, `exact_signed_order_path_evidence`,
/// `exact_wide_order_path_evidence`) read only the edges a node can take
/// from here, instead of every order fact at every node.
///
/// An `int32` fact `lower < upper` (or `<=`, after
/// [`condition_as_order_fact`]'s normalization) is filed under its written
/// `lower` and its canonical form; when `lower` is a constant also under
/// its value, so a constant
/// node finds every edge whose lower end is a constant at least as large by
/// one range read; and when `lower` is a load also under its pointer and
/// kind, the only loads memory-derivation bridging relates to it. A 64-bit
/// or `uint32` fact is filed under its canonical lower end, per format
/// (`WIDE_ORDER_FORMATS`), as the format-indexed walk matches.
#[derive(Clone, Debug, Default)]
pub(crate) struct OrderFactsByLower {
    written: crate::persistent::PersistentMap<
        Bitvector32Term,
        crate::persistent::PersistentSet<ConditionTerm>,
    >,
    canonical: crate::persistent::PersistentMap<
        Bitvector32Term,
        crate::persistent::PersistentSet<ConditionTerm>,
    >,
    constant: imbl::OrdMap<i64, imbl::OrdSet<ConditionTerm>>,
    load: crate::persistent::PersistentMap<
        (Pointer, LoadKind),
        crate::persistent::PersistentSet<ConditionTerm>,
    >,
    wide: [crate::persistent::PersistentMap<
        Bitvector32Term,
        crate::persistent::PersistentSet<ConditionTerm>,
    >; 3],
}

impl OrderFactsByLower {
    fn adjust(&mut self, condition: &ConditionTerm, value: bool, insert: bool) {
        fn file<K: Ord + Clone>(
            index: &mut crate::persistent::PersistentMap<
                K,
                crate::persistent::PersistentSet<ConditionTerm>,
            >,
            key: K,
            condition: &ConditionTerm,
            insert: bool,
        ) {
            let filed = index.get(&key).cloned().unwrap_or_default();
            let filed = if insert {
                filed.with_value(condition.clone())
            } else {
                filed.without_value(condition)
            };
            *index = if filed.is_empty() {
                index.without_key(&key)
            } else {
                index.with_inserted(key, filed)
            };
        }
        if let Some((lower, _, _)) = condition_as_order_fact(condition, value) {
            if let Some(constant) = signed_bitvector_constant(&lower) {
                let mut filed = self.constant.get(&constant).cloned().unwrap_or_default();
                if insert {
                    filed.insert(condition.clone());
                } else {
                    filed.remove(condition);
                }
                if filed.is_empty() {
                    self.constant.remove(&constant);
                } else {
                    self.constant.insert(constant, filed);
                }
            }
            if let Bitvector32Term::MemoryLoad(_, pointer, kind) = &lower {
                file(
                    &mut self.load,
                    (pointer.as_ref().clone(), *kind),
                    condition,
                    insert,
                );
            }
            file(
                &mut self.canonical,
                crate::kernel::eval::canonical_term(&lower),
                condition,
                insert,
            );
            file(&mut self.written, lower, condition, insert);
            return;
        }
        for (kind, format) in condition_reasoning::WIDE_ORDER_FORMATS
            .into_iter()
            .enumerate()
        {
            if let Some((lower, _, _)) =
                condition_reasoning::wide_order_fact(condition, value, format)
            {
                file(
                    &mut self.wide[kind],
                    crate::kernel::eval::canonical_term(&lower),
                    condition,
                    insert,
                );
                return;
            }
        }
    }

    /// The `int32` order facts written with lower end `lower`.
    pub(crate) fn written_from<'a>(
        &'a self,
        lower: &Bitvector32Term,
    ) -> impl Iterator<Item = &'a ConditionTerm> + 'a {
        self.written
            .get(lower)
            .into_iter()
            .flat_map(crate::persistent::PersistentSet::iter)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// The `int32` order facts whose lower end has canonical form
    /// `canonical`.
    pub(crate) fn canonical_from<'a>(
        &'a self,
        canonical: &Bitvector32Term,
    ) -> impl Iterator<Item = &'a ConditionTerm> + 'a {
        self.canonical
            .get(canonical)
            .into_iter()
            .flat_map(crate::persistent::PersistentSet::iter)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// The `int32` order facts whose lower end is a constant at least
    /// `constant`.
    pub(crate) fn constant_at_least(&self, constant: i64) -> impl Iterator<Item = &ConditionTerm> {
        self.constant
            .range(constant..)
            .flat_map(|(_, filed)| filed.iter())
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// The `int32` order facts whose lower end is a load of `pointer` as
    /// `kind`, at any snapshot.
    pub(crate) fn loads_of<'a>(
        &'a self,
        pointer: &Pointer,
        kind: LoadKind,
    ) -> impl Iterator<Item = &'a ConditionTerm> + 'a {
        self.load
            .get(&(pointer.clone(), kind))
            .into_iter()
            .flat_map(crate::persistent::PersistentSet::iter)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// The order facts at `format`, one of
    /// [`condition_reasoning::WIDE_ORDER_FORMATS`], whose lower end has
    /// canonical form `lower`.
    pub(crate) fn wide_from<'a>(
        &'a self,
        format: MachineIntegerType,
        lower: &Bitvector32Term,
    ) -> impl Iterator<Item = &'a ConditionTerm> + 'a {
        let kind = condition_reasoning::WIDE_ORDER_FORMATS
            .iter()
            .position(|wide| *wide == format);
        kind.and_then(|kind| self.wide[kind].get(lower))
            .into_iter()
            .flat_map(crate::persistent::PersistentSet::iter)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }
}

/// A hash of an offset's structure that two snapshot-equivalent offsets
/// (`pointer_offset_terms_snapshot_equivalent`) always share: every
/// literal load stands for its kind alone, since two loads of one kind at
/// proven-equal addresses may match whatever their pointers and snapshots,
/// and a sum's operands are taken in either order. Unequal offsets may
/// share one too; the shape only narrows the facts to check.
pub(in crate::kernel) fn offset_snapshot_shape(offset: &PointerOffsetTerm) -> u64 {
    use std::hash::{Hash, Hasher};
    fn term_shape(term: &Bitvector32Term) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        match term {
            Bitvector32Term::MemoryLoad(_, _, kind) => (0u8, kind).hash(&mut hasher),
            binary_term!(Int32, Add, left, right) => {
                (1u8, term_shape(left), term_shape(right)).hash(&mut hasher)
            }
            binary_term!(Int32, Subtract, left, right) => {
                (2u8, term_shape(left), term_shape(right)).hash(&mut hasher)
            }
            binary_term!(Int32, Multiply, left, right) => {
                (3u8, term_shape(left), term_shape(right)).hash(&mut hasher)
            }
            other => (4u8, other).hash(&mut hasher),
        }
        hasher.finish()
    }
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    match offset {
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            (0u8, byte_width, term_shape(value)).hash(&mut hasher)
        }
        PointerOffsetTerm::Add(left, right) => {
            let (left, right) = (offset_snapshot_shape(left), offset_snapshot_shape(right));
            (1u8, left.min(right), left.max(right)).hash(&mut hasher)
        }
        other => (2u8, other).hash(&mut hasher),
    }
    hasher.finish()
}

/// A shape a universal fact's conclusion takes, read through its binders,
/// implications and conjunctions. Two conditions `condition_matches` can
/// relate share one, and so do two propositions that are alpha-equivalent
/// or equal up to proven terms, so an instantiation or a match against a
/// goal reads only the universals filed under the goal's shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(in crate::kernel) enum UniversalConclusionKey {
    /// An `int32` equality.
    Equal,
    /// A strict `int32` order, either way round.
    StrictOrder,
    /// A non-strict `int32` order, either way round.
    Order,
    /// Signed `int32` addition overflow.
    OverflowAdd,
    /// A mathematical integer equality.
    IntegerEqual,
    /// A pointer value equality.
    PointerValueEqual,
    /// A pointer offset equality.
    OffsetEqual,
    /// Any other condition, which matches only itself.
    OtherCondition,
    /// A loadability fact.
    Loadable,
    /// A universal with none of the shapes above.
    Other,
}

impl UniversalConclusionKey {
    /// The shape `condition_matches` relates `condition` within.
    pub(in crate::kernel) fn of_condition(condition: &ConditionTerm) -> Self {
        match condition {
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                ..
            } => Self::Equal,
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation,
                ..
            } => match relation {
                CompareRelation::Equal => Self::Equal,
                CompareRelation::LessThan | CompareRelation::GreaterThan => Self::StrictOrder,
                CompareRelation::LessEqual | CompareRelation::GreaterEqual => Self::Order,
            },
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Add,
                ..
            } => Self::OverflowAdd,
            ConditionTerm::IntegerEqual(_, _) => Self::IntegerEqual,
            ConditionTerm::PointerValueEqual(_, _) => Self::PointerValueEqual,
            ConditionTerm::PointerOffsetEqual(_, _) => Self::OffsetEqual,
            _ => Self::OtherCondition,
        }
    }

    /// Every shape the conclusion of `proposition` takes, or `Other` when
    /// it takes none. The walk follows a universal's body, an implication's
    /// consequent and both conjuncts, as instantiation and condition
    /// matching do.
    pub(in crate::kernel) fn of(proposition: &Proposition) -> BTreeSet<Self> {
        fn collect(proposition: &Proposition, keys: &mut BTreeSet<UniversalConclusionKey>) {
            match proposition {
                Proposition::ForAll { body, .. } => collect(body, keys),
                Proposition::Implies(_, conclusion) => collect(conclusion, keys),
                Proposition::And(left, right) => {
                    collect(left, keys);
                    collect(right, keys);
                }
                Proposition::ConditionIs(condition, _) => {
                    keys.insert(UniversalConclusionKey::of_condition(condition));
                }
                Proposition::CMemoryLoadable { .. } => {
                    keys.insert(UniversalConclusionKey::Loadable);
                }
                _ => {}
            }
        }
        let mut keys = BTreeSet::new();
        collect(proposition, &mut keys);
        if keys.is_empty() {
            keys.insert(Self::Other);
        }
        keys
    }
}

/// `map` with `member` added to or withdrawn from the set under `key`, the
/// key dropped when its set empties.
fn with_adjusted_member<K: Ord + Clone, V: Ord + Clone>(
    map: &crate::persistent::PersistentMap<K, crate::persistent::PersistentSet<V>>,
    key: &K,
    member: &V,
    insert: bool,
) -> crate::persistent::PersistentMap<K, crate::persistent::PersistentSet<V>> {
    let bucket = map.get(key).cloned().unwrap_or_default();
    let bucket = if insert {
        bucket.with_value(member.clone())
    } else {
        bucket.without_value(member)
    };
    if bucket.is_empty() {
        map.without_key(key)
    } else {
        map.with_inserted(key.clone(), bucket)
    }
}

mod selected_facts;
pub(crate) use selected_facts::SelectedFacts;

#[cfg(test)]
mod diagnostic_sample_tests {
    use super::*;

    #[test]
    fn diagnostic_samples_preserve_order_counts_and_overlap_without_unbounded_limits() {
        for (conditions, propositions) in
            [(0, 0), (0, 40), (40, 0), (5, 40), (40, 5), (5, 5), (20, 20)]
        {
            let mut context = PureFactContext::new();
            for index in 0..conditions {
                context = context.assume_condition(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(Variable(660_000 + index)),
                        Bitvector32Term::Constant(1000),
                    ),
                    true,
                );
            }
            for index in 0..propositions {
                context = context.assume_proposition(Proposition::Predicate {
                    name: format!("sample_{index:03}"),
                    arguments: Vec::new(),
                });
            }
            let all = context.pure_facts();
            for (first, last) in [
                (0, 0),
                (12, 0),
                (8, 24),
                (0, 32),
                (usize::MAX, usize::MAX),
                (4, usize::MAX),
            ] {
                let prefix = first.min(32);
                let suffix = last.min(32 - prefix);
                let end = prefix.min(all.len());
                let start = all.len().saturating_sub(suffix).max(end);
                let expected: Vec<_> = all[..end]
                    .iter()
                    .chain(all[start..].iter())
                    .cloned()
                    .collect();
                let ((sample, count), work) =
                    crate::instrumentation::measure_deterministic_work(|| {
                        context.diagnostic_fact_sample(first, last)
                    });
                assert_eq!(
                    sample, expected,
                    "{conditions}/{propositions}, {first}/{last}"
                );
                assert_eq!(count, all.len());
                assert!(
                    work <= 32,
                    "unbounded diagnostic request visited {work} facts"
                );
            }
        }
    }
}

#[cfg(test)]
mod contradictory_branch_scaling_tests {
    use super::*;
    include!("../scaling_tests/kernel/assumptions/contradictory_branches.rs");
}

#[cfg(test)]
mod context_restriction_scaling_tests {
    use super::*;
    include!("../scaling_tests/kernel/assumptions/context_restriction.rs");
}

#[cfg(test)]
mod root_extent_tests;

#[cfg(test)]
mod view_alias_scaling_tests {
    use super::*;
    include!("../scaling_tests/kernel/assumptions/view_aliases.rs");
}

#[cfg(test)]
mod resource_alias_scaling_tests {
    use super::*;
    include!("../scaling_tests/kernel/assumptions/resource_aliases.rs");
}

#[cfg(test)]
mod condition_bucket_scaling_tests {
    use super::*;
    include!("../scaling_tests/kernel/assumptions/condition_buckets.rs");
}

/// A 32-bit order comparison stated in the other direction: `b > a` for
/// `a < b`, `b >= a` for `a <= b`, and back. One match on the root.
fn mirrored_order32(condition: &ConditionTerm) -> Option<ConditionTerm> {
    let ConditionTerm::Compare {
        format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
        relation,
        left,
        right,
    } = condition
    else {
        return None;
    };
    let relation = match relation {
        CompareRelation::LessThan => CompareRelation::GreaterThan,
        CompareRelation::LessEqual => CompareRelation::GreaterEqual,
        CompareRelation::GreaterThan => CompareRelation::LessThan,
        CompareRelation::GreaterEqual => CompareRelation::LessEqual,
        CompareRelation::Equal => return None,
    };
    Some(ConditionTerm::Compare {
        format: *format,
        relation,
        left: right.clone(),
        right: left.clone(),
    })
}
