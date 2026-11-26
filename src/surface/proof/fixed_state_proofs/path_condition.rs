use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType, binary_node, binary_term};
use crate::kernel::{OffsetTree, OffsetView};

/// Erases every embedded memory state from a comparison proposition so
/// two forms of the same comparison at different states compare
/// equal when comparing a written branch condition to the program test.
fn memory_erased_comparison(proposition: &Proposition) -> Option<Proposition> {
    fn erase_term(term: &OldMachineTerm) -> OldMachineTerm {
        match term {
            OldMachineTerm::MemoryLoad(_, pointer, kind) => {
                crate::kernel::OldMachineTerm::read_named(
                    crate::kernel::ProgramPoint::unplaced(
                        &(crate::kernel::intern_memory(SymbolicMemory::default())),
                    ),
                    OldAddress {
                        base: pointer.base.clone(),
                        offset: erase_offset(&pointer.offset),
                    },
                    *kind,
                )
            }
            binary_term!(Bits32 @ format32, Add, left, right) => {
                binary_node!(
                @ *format32,
                Add,
                    Box::new(erase_term(left)),
                    Box::new(erase_term(right))
                )
            }
            binary_term!(Bits32 @ format32, Subtract, left, right) => {
                binary_node!(
                @ *format32,
                Subtract,
                    Box::new(erase_term(left)),
                    Box::new(erase_term(right))
                )
            }
            binary_term!(Bits32 @ format32, Multiply, left, right) => {
                binary_node!(
                @ *format32,
                Multiply,
                    Box::new(erase_term(left)),
                    Box::new(erase_term(right))
                )
            }
            other => other.clone(),
        }
    }
    fn erase_offset(offset: &OldAddressOffset) -> OldAddressOffset {
        match offset.view() {
            OffsetView::Add(left, right) => {
                OldAddressOffset::raw_add(erase_offset(left), erase_offset(right))
            }
            OffsetView::Int32Scaled { index, byte_width } => OldAddressOffset::scaled_int32_node(
                erase_term(index.structural_value()),
                byte_width,
            ),
            _ => offset.clone(),
        }
    }
    let Proposition::ConditionIs(condition, value) = proposition else {
        return None;
    };
    let erased = match condition.old_form() {
        // A 32-bit comparison, signed or `uint32` (equality is filed at
        // `int32`).
        OldConditionTerm::Compare {
            format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
            relation,
            left,
            right,
        } => OldConditionTerm::Compare {
            format: *format,
            relation: *relation,
            left: Box::new(erase_term(left)),
            right: Box::new(erase_term(right)),
        },
        _ => return None,
    };
    Some(Proposition::condition_is(erased, *value))
}

/// Compares branch facts after erasing the memory state captured at the
/// branch split. In addition to the kernel's canonical forms, accept the
/// ordinary complementary and operand-reversed forms of 32-bit order
/// comparisons, signed or `uint32` (for example, `!(a < b)` and `a >= b`).
pub(in crate::surface::proof) fn path_condition_equivalent(
    left: &Proposition,
    right: &Proposition,
) -> bool {
    fn signed_order_equivalent(left: &Proposition, right: &Proposition) -> bool {
        let (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) = (left, right)
        else {
            return false;
        };
        use CompareRelation::{
            GreaterEqual as Ge, GreaterThan as Gt, LessEqual as Le, LessThan as Lt,
        };
        let (
            OldConditionTerm::Compare {
                format: left_format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
                relation: left_relation,
                left,
                right,
            },
            OldConditionTerm::Compare {
                format: right_format,
                relation: right_relation,
                left: other_left,
                right: other_right,
            },
        ) = (left_condition.old_form(), right_condition.old_form())
        else {
            return false;
        };
        // An order compares in one signedness: a `uint32` order is never a
        // signed one.
        if left_format != right_format {
            return false;
        }
        match (left_relation, right_relation) {
            (Lt, Ge) | (Ge, Lt) | (Le, Gt) | (Gt, Le) => {
                left == other_left && right == other_right && left_value != right_value
            }
            (Lt, Gt) | (Gt, Lt) | (Le, Ge) | (Ge, Le) => {
                left == other_right && right == other_left && left_value == right_value
            }
            _ => false,
        }
    }

    fn symmetric_equality_equivalent(left: &Proposition, right: &Proposition) -> bool {
        let (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) = (left, right)
        else {
            return false;
        };
        if left_value != right_value {
            return false;
        }
        match (left_condition.old_form(), right_condition.old_form()) {
            (
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    left: other_left,
                    right: other_right,
                },
            ) => left == other_right && right == other_left,
            (
                OldConditionTerm::AddressOffsetEqual(left, right),
                OldConditionTerm::AddressOffsetEqual(other_left, other_right),
            ) => left == other_right && right == other_left,
            (
                OldConditionTerm::AddressEqual(left, right),
                OldConditionTerm::AddressEqual(other_left, other_right),
            ) => left == other_right && right == other_left,
            _ => false,
        }
    }

    if condition_polarity_equivalent(left, right)
        || signed_order_equivalent(left, right)
        || symmetric_equality_equivalent(left, right)
    {
        return true;
    }
    let (Some(left), Some(right)) = (
        memory_erased_comparison(left),
        memory_erased_comparison(right),
    ) else {
        return false;
    };
    condition_polarity_equivalent(&left, &right)
        || signed_order_equivalent(&left, &right)
        || symmetric_equality_equivalent(&left, &right)
}
