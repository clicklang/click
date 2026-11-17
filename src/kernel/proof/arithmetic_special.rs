//! Local arithmetic rules used by selected-input normalization, and internal
//! plans selecting those rules for ordinary proof expansion.
use super::super::{
    Address, AddressBase, AddressOffset, ComparisonOperator, ConditionTerm, FloatClassification,
    FloatCondition, MachineTerm, PointerValue, Proposition, SignedDefinedWidth,
};

use crate::kernel::binary_term;
use crate::kernel::{CompareRelation, OverflowOperation};
use crate::kernel::{IntegerTerm, MachineIntegerType};
use crate::kernel::{MachineBinaryOp, MachineUnaryOp};
use crate::kernel::{MachineCastSpelling, cast_term};
use crate::kernel::{
    bits32_constant, constant_i64, constant_u32, constant_u64, int32_constant, int64_constant,
    native_constant, uint64_constant,
};
use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

mod word_view;
use word_view::{Key as WordKey, Node as WordNode, Word};

const SIGNED_MIN: i64 = i32::MIN as i64;
const SIGNED_MAX: i64 = i32::MAX as i64;
const MAX_TERM_PAYLOAD: usize = 256;

fn charge_payload(payload: usize) -> bool {
    payload <= MAX_TERM_PAYLOAD
        && !crate::instrumentation::deadline_exceeded_with_work(payload.max(1))
}

fn address_base_payload(block: &AddressBase) -> Option<usize> {
    let payload = match block {
        AddressBase::ContractResult
        | AddressBase::ContractException
        | AddressBase::AggregateReturn { .. }
        | AddressBase::StaticObject { .. }
        | AddressBase::AutomaticLocal { .. }
        | AddressBase::ReferenceCarrier { .. } => 1,
        AddressBase::Concrete(name) | AddressBase::Function(name) => {
            1usize.checked_add(name.len())?
        }
        AddressBase::StringLiteral { identity, bytes } => 1usize
            .checked_add(identity.payload_bytes())?
            .checked_add(bytes.len())?,
        AddressBase::PureFunctionApplication(_)
        | AddressBase::FunctionSymbolic(_)
        | AddressBase::ExternalArgument
        | AddressBase::ExternalObject(_)
        | AddressBase::Symbolic(_)
        | AddressBase::LoadedPointer(_)
        | AddressBase::Heap(_)
        | AddressBase::Temporary(_) => 1,
    };
    (payload <= MAX_TERM_PAYLOAD).then_some(payload)
}

fn pointer_payload(pointer: &Address) -> Option<usize> {
    address_base_payload(&pointer.base)?.checked_add(pointer_offset_payload(&pointer.offset)?)
}

fn pointer_offset_payload(root: &AddressOffset) -> Option<usize> {
    let mut pending = vec![root];
    let mut payload = 0usize;
    while let Some(offset) = pending.pop() {
        payload = payload.checked_add(1)?;
        if payload > MAX_TERM_PAYLOAD {
            return None;
        }
        match offset {
            AddressOffset::Constant(_) | AddressOffset::Variable(_) => {}
            AddressOffset::Add(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            AddressOffset::Int32Scaled { value, .. } | AddressOffset::Int64Scaled { value, .. } => {
                payload = payload.checked_add(pointer_index_payload(value.operand_view())?)?;
            }
        }
        if payload > MAX_TERM_PAYLOAD {
            return None;
        }
    }
    Some(payload)
}

// Preserve the certificate's occurrence budget and supported native syntax.
// The bounded walk never materializes the potentially much larger native tree.
fn pointer_index_payload(root: crate::kernel::MachineOperandView<'_>) -> Option<usize> {
    use crate::kernel::{MachineCastSpelling as E, MachineOperandView as V};
    let mut pending = vec![root];
    let mut total = 0usize;
    while let Some(view) = pending.pop() {
        if let Some(leaf) = view
            .literal()
            .map(std::borrow::Cow::Owned)
            .or_else(|| view.read_source())
        {
            total = total.checked_add(bitvector_payload(&leaf)?)?;
        } else if let Some((format, op, operands)) = view.binary() {
            if !operand_identity::binary_supported(format, op) {
                return None;
            }
            total = total.checked_add(1)?;
            pending.extend(operands);
        } else if let Some((encoding, _, _, operand)) = view.cast() {
            if !matches!(
                encoding,
                E::Generic | E::Int64FromUInt32 | E::UInt64From32 | E::UInt32From64
            ) {
                return None;
            }
            total = total.checked_add(1)?;
            pending.push(operand);
        } else if let V::Legacy(term) = view {
            total = total.checked_add(bitvector_payload(term)?)?;
        } else {
            return None;
        }
        if total > MAX_TERM_PAYLOAD {
            return None;
        }
    }
    Some(total)
}

fn bitvector_payload(root: &MachineTerm) -> Option<usize> {
    let mut pending = vec![root];
    let mut payload = 0usize;
    while let Some(term) = pending.pop() {
        payload = payload.checked_add(1)?;
        if payload > MAX_TERM_PAYLOAD {
            return None;
        }
        match term {
            MachineTerm::Constant { .. } | MachineTerm::Variable(_) => {}
            // Integer operands are already interned by shallow identity.
            MachineTerm::IntegerToMachine { .. } => {}
            MachineTerm::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::Add,
                left,
                right,
            }
            | binary_term!(Int32, BitwiseXor, left, right)
            | binary_term!(Int32, Add, left, right)
            | binary_term!(Int32, Subtract, left, right)
            | MachineTerm::Float32Binary { left, right, .. }
            | MachineTerm::Float64Binary { left, right, .. }
            | MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op:
                    MachineBinaryOp::Add
                    | MachineBinaryOp::Subtract
                    | MachineBinaryOp::Multiply
                    | MachineBinaryOp::Divide
                    | MachineBinaryOp::Remainder
                    | MachineBinaryOp::BitwiseAnd
                    | MachineBinaryOp::BitwiseOr,
                left,
                right,
            }
            | binary_term!(Int32, BitwiseAnd, left, right)
            | binary_term!(Int32, BitwiseOr, left, right) => {
                pending.push(left);
                pending.push(right);
            }
            cast_term!(Int64FromUInt32, value)
            | cast_term!(UInt64From32, value)
            | cast_term!(UInt32From64, value)
            | MachineTerm::Float32Negate(value)
            | MachineTerm::Float64Negate(value) => pending.push(value),
            MachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                value,
                ..
            } => pending.push(value),
            MachineTerm::PureFunctionApplication { name, arguments } => {
                payload = payload.checked_add(name.len())?;
                pending.extend(arguments.iter());
            }
            MachineTerm::PointerAddress(pointer, _) | MachineTerm::MemoryLoad(_, pointer, _) => {
                // A read owns an interned state; only its written address
                // contributes syntax payload, never the state contents.
                payload = payload.checked_add(pointer_payload(pointer)?)?;
            }
            _ => return None,
        }
        if payload > MAX_TERM_PAYLOAD {
            return None;
        }
    }
    Some(payload)
}

fn charge_pointer_offset(offset: &AddressOffset) -> bool {
    pointer_offset_payload(offset).is_some_and(charge_payload)
}

fn charge_pointer(pointer: &Address) -> bool {
    pointer_payload(pointer).is_some_and(charge_payload)
}

fn charge_address_base(block: &AddressBase) -> bool {
    address_base_payload(block).is_some_and(charge_payload)
}

fn charge_bitvector(term: &MachineTerm) -> bool {
    bitvector_payload(term).is_some_and(charge_payload)
}

fn charge_map_insert(offset: &AddressOffset, map_len: usize) -> bool {
    let comparisons = (usize::BITS - map_len.max(1).leading_zeros()) as usize;
    pointer_offset_payload(offset).is_some_and(|payload| {
        !crate::instrumentation::deadline_exceeded_with_work(
            payload.saturating_mul(comparisons).max(1),
        )
    })
}

/// Charges a 32-bit order premise, signed or `uint32`, and refuses any other
/// premise.
fn charge_signed_bound(proposition: &Proposition) -> bool {
    // A native 8- or 16-bit order is the same fact as the `int32` order of
    // its widenings (rule K8), which the bound context files with it.
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format:
                MachineIntegerType::Int32
                | MachineIntegerType::UInt32
                | MachineIntegerType::Int8
                | MachineIntegerType::UInt8
                | MachineIntegerType::Int16
                | MachineIntegerType::UInt16,
            relation:
                CompareRelation::LessThan
                | CompareRelation::LessEqual
                | CompareRelation::GreaterThan
                | CompareRelation::GreaterEqual,
            left,
            right,
        },
        true,
    ) = proposition
    else {
        return false;
    };
    charge_bitvector(left) && charge_bitvector(right)
}

fn address_base_equal(left: &AddressBase, right: &AddressBase) -> bool {
    match (left, right) {
        (AddressBase::Concrete(left), AddressBase::Concrete(right))
        | (AddressBase::Function(left), AddressBase::Function(right)) => left == right,
        (
            AddressBase::StringLiteral {
                identity: left_identity,
                bytes: left_bytes,
            },
            AddressBase::StringLiteral {
                identity: right_identity,
                bytes: right_bytes,
            },
        ) => left_identity == right_identity && left_bytes == right_bytes,
        (AddressBase::FunctionSymbolic(left), AddressBase::FunctionSymbolic(right))
        | (AddressBase::Symbolic(left), AddressBase::Symbolic(right)) => left == right,
        (AddressBase::ExternalArgument, AddressBase::ExternalArgument)
        | (AddressBase::Heap(_), AddressBase::Heap(_))
        | (AddressBase::Temporary(_), AddressBase::Temporary(_))
        | (
            AddressBase::ContractResult
            | AddressBase::ContractException
            | AddressBase::AggregateReturn { .. }
            | AddressBase::StaticObject { .. }
            | AddressBase::AutomaticLocal { .. }
            | AddressBase::ReferenceCarrier { .. },
            AddressBase::ContractResult
            | AddressBase::ContractException
            | AddressBase::AggregateReturn { .. }
            | AddressBase::StaticObject { .. }
            | AddressBase::AutomaticLocal { .. }
            | AddressBase::ReferenceCarrier { .. },
        ) => left == right,
        _ => false,
    }
}

fn pointer_index_equal(
    left: crate::kernel::MachineOperandView<'_>,
    right: crate::kernel::MachineOperandView<'_>,
) -> bool {
    if !pointer_index_payload(left).is_some_and(charge_payload)
        || !pointer_index_payload(right).is_some_and(charge_payload)
    {
        return false;
    }
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        let a = left
            .literal()
            .map(std::borrow::Cow::Owned)
            .or_else(|| left.read_source());
        let b = right
            .literal()
            .map(std::borrow::Cow::Owned)
            .or_else(|| right.read_source());
        if let (Some(a), Some(b)) = (a, b) {
            if !legacy_bitvector_equal_after_payload_check(&a, &b) {
                return false;
            }
        } else if let (Some((af, ao, [al, ar])), Some((bf, bo, [bl, br]))) =
            (left.binary(), right.binary())
        {
            if (af, ao) != (bf, bo) || !operand_identity::binary_supported(af, ao) {
                return false;
            }
            pending.push((al, bl));
            pending.push((ar, br));
        } else if let (Some((ae, af, at, av)), Some((be, bf, bt, bv))) = (left.cast(), right.cast())
        {
            if (ae, af, at) != (be, bf, bt) {
                return false;
            }
            pending.push((av, bv));
        } else {
            return false;
        }
    }
    true
}

fn pointer_offset_equal(left: &AddressOffset, right: &AddressOffset) -> bool {
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        match (left, right) {
            (AddressOffset::Constant(left), AddressOffset::Constant(right)) => {
                if left != right {
                    return false;
                }
            }
            (AddressOffset::Variable(left), AddressOffset::Variable(right)) => {
                if left != right {
                    return false;
                }
            }
            (
                AddressOffset::Add(left_first, left_second),
                AddressOffset::Add(right_first, right_second),
            ) => {
                pending.push((left_first, right_first));
                pending.push((left_second, right_second));
            }
            (
                AddressOffset::Int32Scaled {
                    value: left,
                    byte_width: left_width,
                },
                AddressOffset::Int32Scaled {
                    value: right,
                    byte_width: right_width,
                },
            ) if left_width == right_width => {
                if !pointer_index_equal(left.operand_view(), right.operand_view()) {
                    return false;
                }
            }
            (
                AddressOffset::Int64Scaled {
                    value: left,
                    byte_width: left_width,
                    unsigned: left_unsigned,
                },
                AddressOffset::Int64Scaled {
                    value: right,
                    byte_width: right_width,
                    unsigned: right_unsigned,
                },
            ) if left_width == right_width && left_unsigned == right_unsigned => {
                if !pointer_index_equal(left.operand_view(), right.operand_view()) {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}

fn pointer_equal(left: &Address, right: &Address) -> bool {
    charge_pointer(left)
        && charge_pointer(right)
        && address_base_equal(&left.base, &right.base)
        && pointer_offset_equal(&left.offset, &right.offset)
}

mod operand_identity;

/// Compare only the bounded structural fragment accepted by `bitvector_payload`.
/// This avoids recursive equality on attacker-controlled expression depth after
/// the payload has already been charged.
fn bitvector_equal(left: &MachineTerm, right: &MachineTerm) -> bool {
    operand_identity::equal(
        crate::kernel::MachineOperandView::Legacy(left),
        crate::kernel::MachineOperandView::Legacy(right),
    )
}

fn legacy_bitvector_equal(left: &MachineTerm, right: &MachineTerm) -> bool {
    if !charge_bitvector(left) || !charge_bitvector(right) {
        return false;
    }
    legacy_bitvector_equal_after_payload_check(left, right)
}

fn legacy_bitvector_equal_after_payload_check(left: &MachineTerm, right: &MachineTerm) -> bool {
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        match (left, right) {
            (cast_term!(Int64FromUInt32, left), cast_term!(Int64FromUInt32, right))
            | (cast_term!(UInt64From32, left), cast_term!(UInt64From32, right))
            | (cast_term!(UInt32From64, left), cast_term!(UInt32From64, right)) => {
                pending.push((left, right));
            }
            (bits32_constant!(left), bits32_constant!(right)) => {
                if constant_u32(*left) != constant_u32(*right) {
                    return false;
                }
            }
            (int64_constant!(left), int64_constant!(right)) => {
                if constant_i64(*left) != constant_i64(*right) {
                    return false;
                }
            }
            (uint64_constant!(left), uint64_constant!(right)) => {
                if constant_u64(*left) != constant_u64(*right) {
                    return false;
                }
            }
            (MachineTerm::Variable(left), MachineTerm::Variable(right)) => {
                if left != right {
                    return false;
                }
            }
            (MachineTerm::MemoryLoad(lm, lp, lk), MachineTerm::MemoryLoad(rm, rp, rk)) => {
                if lm != rm || lk != rk || !pointer_equal(lp, rp) {
                    return false;
                }
            }
            (native_constant!(left_format, left), native_constant!(right_format, right)) => {
                if (left_format, left) != (right_format, right) {
                    return false;
                }
            }
            (
                MachineTerm::IntegerToMachine {
                    value: left,
                    destination: left_destination,
                },
                MachineTerm::IntegerToMachine {
                    value: right,
                    destination: right_destination,
                },
            ) => {
                if left_destination != right_destination || left != right {
                    return false;
                }
            }
            (
                MachineTerm::Cast {
                    spelling: MachineCastSpelling::Generic,
                    value: left,
                    from: left_source,
                    to: left_destination,
                },
                MachineTerm::Cast {
                    spelling: MachineCastSpelling::Generic,
                    value: right,
                    from: right_source,
                    to: right_destination,
                },
            ) => {
                if left_source != right_source || left_destination != right_destination {
                    return false;
                }
                pending.push((left, right));
            }
            (
                MachineTerm::PureFunctionApplication {
                    name: left_name,
                    arguments: left_arguments,
                },
                MachineTerm::PureFunctionApplication {
                    name: right_name,
                    arguments: right_arguments,
                },
            ) if left_name == right_name && left_arguments.len() == right_arguments.len() => {
                pending.extend(left_arguments.iter().zip(right_arguments.iter()));
            }
            (MachineTerm::PointerAddress(left, _), MachineTerm::PointerAddress(right, _)) => {
                if !pointer_equal(left, right) {
                    return false;
                }
            }
            _ => {
                use crate::kernel::BitvectorBinaryOp as Op;
                let (
                    Some((operator, left_first, left_second)),
                    Some((other, right_first, right_second)),
                ) = (left.as_binary(), right.as_binary())
                else {
                    return false;
                };
                let compared = matches!(
                    operator,
                    Op::Machine(
                        crate::kernel::MachineIntegerType::Int32,
                        crate::kernel::MachineBinaryOp::Add
                    ) | Op::Machine(
                        crate::kernel::MachineIntegerType::Int32,
                        crate::kernel::MachineBinaryOp::Subtract
                    ) | Op::Machine(
                        crate::kernel::MachineIntegerType::Int32,
                        crate::kernel::MachineBinaryOp::BitwiseAnd
                    ) | Op::Machine(
                        crate::kernel::MachineIntegerType::Int32,
                        crate::kernel::MachineBinaryOp::BitwiseOr
                    ) | Op::Machine(
                        crate::kernel::MachineIntegerType::Int32,
                        crate::kernel::MachineBinaryOp::BitwiseXor
                    ) | Op::Machine(MachineIntegerType::Int64, MachineBinaryOp::Add)
                        | Op::Machine(
                            MachineIntegerType::UInt64,
                            MachineBinaryOp::Add
                                | MachineBinaryOp::Subtract
                                | MachineBinaryOp::Multiply
                                | MachineBinaryOp::Divide
                                | MachineBinaryOp::Remainder
                                | MachineBinaryOp::BitwiseAnd
                                | MachineBinaryOp::BitwiseOr
                        )
                        | Op::Float32(_)
                        | Op::Float64(_)
                );
                if operator != other || !compared {
                    return false;
                }
                pending.push((left_first, right_first));
                pending.push((left_second, right_second));
            }
        }
    }
    true
}

/// Recognize the kernel's alignment proposition only after its complete
/// bitvector payload has been walked and charged.  `as_pointer_alignment`
/// uses the convenience `uint64_as_const` recognizer, whose implementation is
/// recursive for constant expressions; keeping it behind this bounded walk
/// makes attacker-controlled depth fail before that helper is reached.
pub(crate) fn checked_pointer_alignment(condition: &ConditionTerm) -> Option<(&Address, u64)> {
    match condition {
        ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        } => {
            if !charge_bitvector(left) || !charge_bitvector(right) {
                return None;
            }
        }
        ConditionTerm::IntegerEqual(left, right) => {
            for side in [left, right] {
                match side.as_ref() {
                    IntegerTerm::Machine(word) if word_view::charge(Word(word.operand_view())) => {}
                    IntegerTerm::Constant(_) => {}
                    _ => return None,
                }
            }
        }
        _ => return None,
    }
    condition.as_pointer_alignment()
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SpecialArithmeticNode {
    IntegerCastIdentity {
        bounds: Vec<usize>,
        result: Proposition,
    },

    UnsignedSumBound {
        bounds: Vec<usize>,
        result: Proposition,
    },
    /// Translate one exact pointer equality using explicitly listed scalar
    /// bounds.  The relation premise is one of `premises`; every bound index
    /// must name a scalar signed comparison in that same premise slice.
    PointerTranslation {
        relation: usize,
        bounds: Vec<usize>,
        result: Proposition,
    },
    /// Establish one alignment proposition from one exact alignment premise.
    /// `None` is reserved for intrinsic allocator/static alignment and is
    /// checked structurally, never by searching a context.
    PointerAlignment {
        premise: Option<usize>,
        result: Proposition,
    },
    /// Establish a tagged pointer-word equality from one exact recorded word
    /// equality and any exact alignment premises needed by tag operations.
    PointerWordEquality {
        relation: usize,
        alignments: Vec<usize>,
        result: Proposition,
    },
    /// Establish a tagged pointer-word equality directly from exact
    /// alignment facts.  Unlike `PointerWordEquality`, this rule is for a
    /// word expression produced by the current execution rather than an
    /// explicitly recorded word-equality relation.
    PointerWordFromAlignment {
        alignments: Vec<usize>,
        result: Proposition,
    },
    /// Prove a reflexive IEEE comparison from one exact finite classification.
    FloatReflexive { finite: usize, result: Proposition },
    /// Establish `defined(left + right)` or `defined(left - right)` over
    /// `width` (`int32` or `int64`) from each operand's range: the width
    /// range of its root constructor (a constant, or for `int64` a value
    /// widened from 32 bits), narrowed by the listed premises. Each listed
    /// premise is a constant order or equality fact of that width on one
    /// operand; the checker reads it directly, so its work is one lookup per
    /// listed bound and never a context scan.
    SignedDefined {
        width: SignedDefinedWidth,
        bounds: Vec<usize>,
        result: Proposition,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SpecialArithmeticPlan {
    pub(crate) nodes: Vec<SpecialArithmeticNode>,
    pub(crate) conclusion: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ArithmeticRuleError {
    InvalidIntegerProductBounds(usize),
    InvalidIntegerDivisionBounds(usize),
    InvalidIntegerMultiplyOrder(usize),
    InvalidIntegerQuotientBound(usize),
    InvalidIntegerBoundExclusion(usize),
    InvalidIntegerRelationTransport(usize),
    InvalidIntegerQuotientShift(usize),
    InvalidIntegerCastIdentity(usize),
    InvalidIntegerOperationIdentity(usize),
    InvalidPremise(usize),
    InvalidOperator(usize),
    NodeResultMismatch(usize),
    WorkLimitExceeded,
}

/// The operation a `defined` claim over `int32` or `int64` addition or
/// subtraction names: its width, its two operands, and whether it subtracts.
pub(crate) fn signed_definedness_operands(
    proposition: &Proposition,
) -> Option<(SignedDefinedWidth, &MachineTerm, &MachineTerm, bool)> {
    let Proposition::ConditionIs(condition, false) = proposition else {
        return None;
    };
    match condition {
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Add,
            left,
            right,
        } => Some((SignedDefinedWidth::Int32, left, right, false)),
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Subtract,
            left,
            right,
        } => Some((SignedDefinedWidth::Int32, left, right, true)),
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int64,
            op: OverflowOperation::Add,
            left,
            right,
        } => Some((SignedDefinedWidth::Int64, left, right, false)),
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int64,
            op: OverflowOperation::Subtract,
            left,
            right,
        } => Some((SignedDefinedWidth::Int64, left, right, true)),
        _ => None,
    }
}

/// The signed value of `term` when it is a constant of `width`.
pub(crate) fn signed_width_constant(width: SignedDefinedWidth, term: &MachineTerm) -> Option<i64> {
    match width {
        SignedDefinedWidth::Int32 => term.as_const().map(|bits| i64::from(bits as i32)),
        SignedDefinedWidth::Int64 => term.int64_as_const(),
    }
}

fn signed_width_constant_view(
    width: SignedDefinedWidth,
    term: crate::kernel::MachineOperandView<'_>,
) -> Option<i64> {
    match width {
        SignedDefinedWidth::Int32 => term.word32_constant().map(|bits| i64::from(bits as i32)),
        SignedDefinedWidth::Int64 => term.int64_constant(),
    }
}

/// What one explicitly supplied constant fact says about an operand.
/// The source fact remains the witness; matching reads only its two endpoints.
pub(crate) fn signed_constant_bound_on_view(
    width: SignedDefinedWidth,
    premise: &Proposition,
    term: crate::kernel::MachineOperandView<'_>,
) -> Option<(Option<i64>, Option<i64>)> {
    let format = match width {
        SignedDefinedWidth::Int32 => MachineIntegerType::Int32,
        SignedDefinedWidth::Int64 => MachineIntegerType::Int64,
    };
    let key = crate::kernel::equality_graph::MachineAtom::from_operand(format, term);
    signed_constant_bound_on_key(width, premise, &key)
}

fn signed_constant_bound_on_key(
    width: SignedDefinedWidth,
    premise: &Proposition,
    key: &crate::kernel::equality_graph::MachineAtom,
) -> Option<(Option<i64>, Option<i64>)> {
    use crate::kernel::equality_graph::MachineAtom;
    use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
    let Proposition::ConditionIs(condition, value) = premise else {
        return None;
    };
    let view = comparison_view(condition, *value)?;
    let format = match width {
        SignedDefinedWidth::Int32 => MachineIntegerType::Int32,
        SignedDefinedWidth::Int64 => MachineIntegerType::Int64,
    };
    if view.format != format
        && !(format == MachineIntegerType::Int32
            && view.format == MachineIntegerType::UInt32
            && view.relation == Relation::Equal)
    {
        return None;
    }
    let [left, right] =
        [&view.operands[0], &view.operands[1]].map(|operand| operand.operand_view());
    let same = |operand| &MachineAtom::from_operand(format, operand) == key;
    if view.relation == Relation::Equal {
        let constant = if same(left) {
            signed_width_constant_view(width, right)?
        } else if same(right) {
            signed_width_constant_view(width, left)?
        } else {
            return None;
        };
        return Some((Some(constant), Some(constant)));
    }
    let strict = match view.relation {
        Relation::Less => true,
        Relation::LessEqual => false,
        _ => return None,
    };
    let step = i64::from(strict);
    let (minimum, maximum) = width.range();
    if same(left)
        && let Some(constant) = signed_width_constant_view(width, right)
    {
        let bound = constant
            .checked_sub(step)
            .filter(|bound| *bound >= minimum)?;
        return Some((None, Some(bound)));
    }
    if same(right)
        && let Some(constant) = signed_width_constant_view(width, left)
    {
        let bound = constant
            .checked_add(step)
            .filter(|bound| *bound <= maximum)?;
        return Some((Some(bound), None));
    }
    None
}

/// The range `term` has from its width and the listed bounds on it.
/// The operation a `defined(a + b)` or `defined(a - b)` result checks. A
/// result whose operands carry definedness of their own, such as a read
/// through a resource view or an inner sum, lowers to a conjunction: its
/// operation is the one overflow conjunct no other conjunct takes as an
/// operand, and every other conjunct must be a conjunct of a cited premise,
/// which marks that premise used.
pub(crate) type SignedDefinedOperation<'a> = (
    SignedDefinedWidth,
    [crate::kernel::machine_integer::comparison::ComparisonOperand<'a>; 2],
    bool,
);

enum IntervalLeaf<'a> {
    Written(&'a Proposition),
    Arithmetic(crate::kernel::machine_integer::definedness::OverflowQueryView),
}

impl<'a> IntervalLeaf<'a> {
    fn operation(&self) -> Option<SignedDefinedOperation<'a>> {
        use crate::kernel::machine_integer::{Operation, comparison::ComparisonOperand};
        match self {
            Self::Arithmetic(query) => {
                let width = match query.format {
                    MachineIntegerType::Int32 => SignedDefinedWidth::Int32,
                    MachineIntegerType::Int64 => SignedDefinedWidth::Int64,
                    _ => return None,
                };
                let subtract = match query.operation {
                    Operation::Add => false,
                    Operation::Subtract => true,
                    Operation::Multiply => return None,
                };
                Some((width, query.operands.clone(), subtract))
            }
            Self::Written(proposition) => {
                let (width, left, right, subtract) = signed_definedness_operands(proposition)?;
                Some((
                    width,
                    [
                        ComparisonOperand::Written(left),
                        ComparisonOperand::Written(right),
                    ],
                    subtract,
                ))
            }
        }
    }
}

/// Read one complete signed addition/subtraction domain without constructing
/// an overflow proposition or exporting its shared operands. Compound domains
/// remain the responsibility of the certificate's outer-operation selection.
pub(crate) fn signed_definedness_query(
    proposition: &Proposition,
) -> Option<SignedDefinedOperation<'_>> {
    if let Some(query) =
        crate::kernel::machine_integer::definedness::ordinary_arithmetic_guard_view(proposition)
    {
        IntervalLeaf::Arithmetic(query).operation()
    } else {
        IntervalLeaf::Written(proposition).operation()
    }
}

impl SpecialArithmeticNode {}

fn pointer_sides(
    proposition: &Proposition,
) -> Option<(
    &AddressOffset,
    &AddressOffset,
    Option<(&AddressBase, &AddressBase)>,
)> {
    match proposition {
        Proposition::ConditionIs(ConditionTerm::PointerValueEqual(left, right), true) => {
            Some((&left.offset, &right.offset, Some((&left.base, &right.base))))
        }
        Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) => {
            Some((&left.offset, &right.offset, Some((&left.base, &right.base))))
        }
        Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) => {
            Some((left, right, None))
        }
        _ => None,
    }
}

fn scalar(value: &MachineTerm) -> Option<i64> {
    value.as_const().map(|value| i64::from(value as i32))
}

fn scalar_bounds(premises: &[&Proposition]) -> Option<BTreeMap<MachineTerm, (i64, i64)>> {
    let mut bounds = BTreeMap::new();
    for premise in premises {
        if !charge_signed_bound(premise) {
            return None;
        }
        let Proposition::ConditionIs(condition, true) = premise else {
            return None;
        };
        let (left, right, strict) = match condition {
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            } => (left.as_ref(), right.as_ref(), true),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            } => (left.as_ref(), right.as_ref(), false),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left,
                right,
            } => (right.as_ref(), left.as_ref(), true),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            } => (right.as_ref(), left.as_ref(), false),
            // A `uint32` order bounds no signed word.
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt32,
                relation:
                    CompareRelation::LessThan
                    | CompareRelation::LessEqual
                    | CompareRelation::GreaterThan
                    | CompareRelation::GreaterEqual,
                ..
            } => continue,
            _ => return None,
        };
        // These bounds are over signed words. A native-width or floating
        // operation cannot supply a signed-word interval merely by being
        // embedded in a syntactically signed comparison.
        if super::signed_arithmetic::SignedArithmeticAtom::from_term(left).is_none()
            || super::signed_arithmetic::SignedArithmeticAtom::from_term(right).is_none()
        {
            return None;
        }
        let left_constant = scalar(left);
        let right_constant = scalar(right);
        let key_payload = bitvector_payload(left)?.max(bitvector_payload(right)?);
        let comparisons = (usize::BITS - bounds.len().max(1).leading_zeros()) as usize;
        if crate::instrumentation::deadline_exceeded_with_work(
            key_payload.saturating_mul(comparisons).max(1),
        ) {
            return None;
        }
        match (left_constant, right_constant) {
            (None, Some(right)) => {
                let entry = bounds
                    .entry(left.clone())
                    .or_insert((SIGNED_MIN, SIGNED_MAX));
                entry.1 = entry.1.min(right - i64::from(strict));
            }
            (Some(left), None) => {
                let entry = bounds
                    .entry(right.clone())
                    .or_insert((SIGNED_MIN, SIGNED_MAX));
                entry.0 = entry.0.max(left + i64::from(strict));
            }
            (None, None) if strict => {
                let entry = bounds
                    .entry(left.clone())
                    .or_insert((SIGNED_MIN, SIGNED_MAX));
                entry.1 = entry.1.min(SIGNED_MAX - 1);
            }
            _ => {}
        }
    }
    Some(bounds)
}

/// The two sides of an unsigned 64-bit order premise, lower side first,
/// and whether the order is strict.
fn unsigned64_order(proposition: &Proposition) -> Option<(&MachineTerm, &MachineTerm, bool)> {
    let Proposition::ConditionIs(condition, true) = proposition else {
        return None;
    };
    Some(match condition {
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessThan,
            left,
            right,
        } => (left, right, true),
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessEqual,
            left,
            right,
        } => (left, right, false),
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::GreaterThan,
            left,
            right,
        } => (right, left, true),
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::GreaterEqual,
            left,
            right,
        } => (right, left, false),
        _ => return None,
    })
}

/// The interval each cited unsigned 64-bit order premise gives its
/// non-constant side. A strict order between two symbolic values keeps the
/// lower one below the type's largest value.
fn unsigned64_bounds(premises: &[&Proposition]) -> Option<BTreeMap<MachineTerm, (u64, u64)>> {
    let mut bounds = BTreeMap::new();
    for premise in premises {
        let (lower, upper, strict) = unsigned64_order(premise)?;
        if !charge_bitvector(lower) || !charge_bitvector(upper) {
            return None;
        }
        let strict = u64::from(strict);
        match (lower.uint64_as_const(), upper.uint64_as_const()) {
            (None, Some(limit)) => {
                let Some(limit) = limit.checked_sub(strict) else {
                    continue;
                };
                let entry = bounds.entry(lower.clone()).or_insert((0, u64::MAX));
                entry.1 = entry.1.min(limit);
            }
            (Some(limit), None) => {
                let Some(limit) = limit.checked_add(strict) else {
                    continue;
                };
                let entry = bounds.entry(upper.clone()).or_insert((0, u64::MAX));
                entry.0 = entry.0.max(limit);
            }
            (None, None) if strict == 1 => {
                let entry = bounds.entry(lower.clone()).or_insert((0, u64::MAX));
                entry.1 = entry.1.min(u64::MAX - 1);
            }
            _ => {}
        }
    }
    Some(bounds)
}

enum OffsetPart<'a> {
    Offset(&'a AddressOffset),
    Scaled(crate::kernel::MachineOperandView<'a>, i64),
    /// An unsigned 64-bit index scaled by an element width.
    Scaled64(crate::kernel::MachineOperandView<'a>, i64),
}

/// An Integer rule's result as the rule derives it: a native comparison
/// result is the Integer comparison of its exact observations, in whichever
/// of its readings the rule's inputs name. The first reading that checks is
/// the node's.
fn integer_rule_holds(
    result: &Proposition,
    check: impl Fn(&Proposition) -> Result<(), ArithmeticRuleError>,
) -> Result<(), ArithmeticRuleError> {
    let negated;
    let native = match result {
        Proposition::Not(inner) => match inner.as_ref() {
            Proposition::ConditionIs(condition, value) => {
                negated = Proposition::ConditionIs(condition.clone(), !value);
                &negated
            }
            _ => result,
        },
        _ => result,
    };
    let readings =
        crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison(
            native,
        );
    if readings.is_empty() {
        return check(result);
    }
    let mut first_error = None;
    for reading in &readings {
        match check(reading) {
            Ok(()) => return Ok(()),
            Err(error) => {
                first_error.get_or_insert(error);
            }
        }
    }
    Err(first_error.expect("a reading was checked"))
}

/// Fixed local rules over the goal and the caller's ordered explicit inputs.
/// Polynomial search and signed-domain planning deliberately do not live here.
pub(super) fn normalizes_selected(goal: &Proposition, premises: &[Proposition]) -> bool {
    if !matches!(goal, Proposition::ConditionIs(..) | Proposition::Not(..)) {
        return false;
    }
    if premises.is_empty() {
        return pointer_alignment(None, goal);
    }
    // Reject impossible arities before reading native operands. Convert each
    // explicit input once, shared by the fixed rule family, rather than once
    // per rejected checker (important for long native expression spines).
    if matches!(premises.len(), 1 | 2 | 4) {
        let indices = (0..premises.len()).collect::<Vec<_>>();
        let cited = premises
            .iter()
            .map(|premise| {
                crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
                    premise,
                )
                .into_iter()
                .next()
                .unwrap_or_else(|| premise.clone())
            })
            .collect::<Vec<_>>();
        type Check =
            fn(usize, &[usize], &[Proposition], &Proposition) -> Result<(), ArithmeticRuleError>;
        let checks: [(usize, Check); 9] = [
            (4, super::integer_product_bounds::check),
            (4, super::integer_division_bounds::check),
            (2, super::integer_multiply_order::check),
            (2, super::integer_quotient_bound::check),
            (1, super::integer_bound_exclusion::check),
            (2, super::integer_relation_transport::check),
            (2, super::integer_quotient_shift::check),
            (2, super::integer_cast_identity::check),
            (2, super::integer_operation_identity::check),
        ];
        if integer_rule_holds(goal, |result| {
            checks
                .iter()
                .any(|(arity, check)| {
                    *arity == premises.len() && check(0, &indices, &cited, result).is_ok()
                })
                .then_some(())
                .ok_or(ArithmeticRuleError::NodeResultMismatch(0))
        })
        .is_ok()
        {
            return true;
        }
    }
    let inputs = premises.iter().collect::<Vec<_>>();
    if pointer_alignment(
        if premises.len() == 1 {
            premises.first()
        } else {
            None
        },
        goal,
    ) && premises.len() <= 1
    {
        return true;
    }
    if let Some((first, rest)) = inputs.split_first()
        && ((premises.len() == 1 && float_reflexive(first, goal))
            || pointer_translation(first, rest, goal)
            || pointer_word_equality(first, rest, goal)
            || pointer_word_from_alignment(&inputs, goal))
    {
        return true;
    }
    if let Proposition::ConditionIs(condition, truth) = goal
        && matches!(
            condition,
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::LessEqual,
                ..
            }
        )
    {
        let mut context = crate::kernel::PureFactContext::new();
        for premise in premises {
            if !charge_signed_bound(premise) {
                return false;
            }
            context = context.assume_proposition(premise.clone());
        }
        return context.decide_widened_sum_bound(condition) == Some(*truth);
    }
    false
}

fn pointer_translation(
    relation: &Proposition,
    bound_propositions: &[&Proposition],
    goal: &Proposition,
) -> bool {
    if let Proposition::ConditionIs(ConditionTerm::PointerValueEqual(left, right), true) = goal {
        let same_domain = |a: &PointerValue, b: &PointerValue| {
            a.provenance() == b.provenance()
                && a.bounds() == b.bounds()
                && a.bounds_are_known() == b.bounds_are_known()
        };
        let linked = match relation {
            Proposition::ConditionIs(ConditionTerm::PointerValueEqual(a, b), true) => {
                (same_domain(left, a) && same_domain(right, b))
                    || (same_domain(left, b) && same_domain(right, a))
            }
            _ => same_domain(left, right),
        };
        if !linked {
            return false;
        }
    }
    let Some((goal_left, goal_right, goal_blocks)) = pointer_sides(goal) else {
        return false;
    };
    let Some((premise_left, premise_right, premise_blocks)) = pointer_sides(relation) else {
        return false;
    };
    if !charge_pointer_offset(goal_left)
        || !charge_pointer_offset(goal_right)
        || !charge_pointer_offset(premise_left)
        || !charge_pointer_offset(premise_right)
    {
        return false;
    }
    if let Some((goal_l, goal_r)) = goal_blocks
        && (!charge_address_base(goal_l) || !charge_address_base(goal_r))
    {
        return false;
    }
    if let Some((premise_l, premise_r)) = premise_blocks
        && (!charge_address_base(premise_l) || !charge_address_base(premise_r))
    {
        return false;
    }
    let (left, right) = match (goal_blocks, premise_blocks) {
        (None, None) => (goal_left, goal_right),
        (Some((goal_l, goal_r)), Some((premise_l, premise_r)))
            if address_base_equal(goal_l, premise_l) && address_base_equal(goal_r, premise_r) =>
        {
            (goal_left, goal_right)
        }
        (Some((goal_l, goal_r)), Some((premise_l, premise_r)))
            if address_base_equal(goal_l, premise_r) && address_base_equal(goal_r, premise_l) =>
        {
            (goal_right, goal_left)
        }
        _ => return false,
    };
    // The cited bounds are of two kinds: signed 32-bit ones, which keep a
    // 32-bit index sum defined, and unsigned 64-bit ones, which keep a
    // 64-bit index sum from wrapping.
    let (wide_bounds, signed_bounds): (Vec<&Proposition>, Vec<&Proposition>) = bound_propositions
        .iter()
        .copied()
        .partition(|premise| unsigned64_order(premise).is_some());
    let Some(bounds) = scalar_bounds(&signed_bounds) else {
        return false;
    };
    let Some(wide_bounds) = unsigned64_bounds(&wide_bounds) else {
        return false;
    };
    use crate::kernel::MachineOperandView as V;
    // The original maps are sorted by native syntax. Binary search preserves
    // that exact matching rule while retaining the queried shared operand.
    let bounds: Vec<_> = bounds.into_iter().collect();
    let wide_bounds: Vec<_> = wide_bounds.into_iter().collect();
    fn lookup<T: Copy>(bounds: &[(MachineTerm, T)], value: V<'_>) -> Option<T> {
        bounds
            .binary_search_by(|(term, _)| {
                crate::kernel::machine_operand_syntax_cmp(V::Legacy(term), value)
            })
            .ok()
            .map(|index| bounds[index].1)
    }
    let wide_range = |value: V<'_>| match value.uint64_constant() {
        Some(value) => (value, value),
        None => lookup(&wide_bounds, value).unwrap_or((0, u64::MAX)),
    };
    let wide_sum_is_exact = |x: V<'_>, y: V<'_>| {
        if !pointer_index_payload(x).is_some_and(charge_payload)
            || !pointer_index_payload(y).is_some_and(charge_payload)
        {
            return false;
        }
        u128::from(wide_range(x).1) + u128::from(wide_range(y).1) <= u128::from(u64::MAX)
    };
    let atom_range = |value: V<'_>| {
        if let Some(bits) = value.word32_constant() {
            let value = i64::from(bits as i32);
            return Some((value, value));
        }
        if value.variable().is_some() {
            return Some(lookup(&bounds, value).unwrap_or((SIGNED_MIN, SIGNED_MAX)));
        }
        let payload = pointer_index_payload(value)?;
        let comparisons = (usize::BITS - bounds.len().max(1).leading_zeros()) as usize;
        if crate::instrumentation::deadline_exceeded_with_work(
            payload.saturating_mul(comparisons).max(1),
        ) {
            return None;
        }
        lookup(&bounds, value)
    };
    let sum_is_defined = |x: V<'_>, y: V<'_>| {
        let (Some((xmin, xmax)), Some((ymin, ymax))) = (atom_range(x), atom_range(y)) else {
            return false;
        };
        xmin + ymin >= SIGNED_MIN && xmax + ymax <= SIGNED_MAX
    };
    let mut terms = BTreeMap::<AddressOffset, i128>::new();
    let mut constant = 0i128;
    for (offset, sign) in [
        (left, 1i128),
        (premise_left, -1),
        (right, -1),
        (premise_right, 1),
    ] {
        let mut pending = vec![OffsetPart::Offset(offset)];
        while let Some(part) = pending.pop() {
            let atom = match part {
                OffsetPart::Offset(AddressOffset::Constant(value)) => {
                    let Some(next) = constant.checked_add(sign * i128::from(*value)) else {
                        return false;
                    };
                    constant = next;
                    continue;
                }
                OffsetPart::Offset(AddressOffset::Add(left, right)) => {
                    pending.push(OffsetPart::Offset(left));
                    pending.push(OffsetPart::Offset(right));
                    continue;
                }
                OffsetPart::Offset(AddressOffset::Int32Scaled { value, byte_width }) => {
                    pending.push(OffsetPart::Scaled(value.operand_view(), *byte_width));
                    continue;
                }
                OffsetPart::Scaled(value, width) => {
                    if let Some(int32_constant!(bits)) = value.literal() {
                        let value = i128::from(constant_u32(bits) as i32) * i128::from(width);
                        let Some(next) = constant.checked_add(sign * value) else {
                            return false;
                        };
                        constant = next;
                        continue;
                    }
                    if let Some((MachineIntegerType::Int32, MachineBinaryOp::Add, [left, right])) =
                        value.binary()
                        && sum_is_defined(left, right)
                    {
                        pending.push(OffsetPart::Scaled(left, width));
                        pending.push(OffsetPart::Scaled(right, width));
                        continue;
                    }
                    AddressOffset::Int32Scaled {
                        value: value.retain(MachineIntegerType::Int32),
                        byte_width: width,
                    }
                }
                OffsetPart::Offset(AddressOffset::Int64Scaled {
                    value,
                    byte_width,
                    unsigned: true,
                }) => {
                    pending.push(OffsetPart::Scaled64(value.operand_view(), *byte_width));
                    continue;
                }
                OffsetPart::Scaled64(value, width) => {
                    if let Some(bits) = value.uint64_constant() {
                        let value = i128::from(bits) * i128::from(width);
                        let Some(next) = constant.checked_add(sign * value) else {
                            return false;
                        };
                        constant = next;
                        continue;
                    }
                    if let Some((MachineIntegerType::UInt64, MachineBinaryOp::Add, [left, right])) =
                        value.binary()
                        && wide_sum_is_exact(left, right)
                    {
                        pending.push(OffsetPart::Scaled64(left, width));
                        pending.push(OffsetPart::Scaled64(right, width));
                        continue;
                    }
                    AddressOffset::Int64Scaled {
                        value: value.retain(MachineIntegerType::Int64),
                        byte_width: width,
                        unsigned: true,
                    }
                }
                OffsetPart::Offset(value) => value.clone(),
            };
            if !charge_map_insert(&atom, terms.len()) {
                return false;
            }
            let entry = terms.entry(atom).or_default();
            let Some(next) = entry.checked_add(sign) else {
                return false;
            };
            *entry = next;
        }
    }
    constant == 0 && terms.values().all(|coefficient| *coefficient == 0)
}

fn offset_difference(goal: &AddressOffset, premise: &AddressOffset) -> Option<i128> {
    if !charge_pointer_offset(goal) || !charge_pointer_offset(premise) {
        return None;
    }
    let mut terms = BTreeMap::<AddressOffset, i128>::new();
    let mut constant = 0i128;
    for (offset, sign) in [(goal, 1i128), (premise, -1)] {
        let mut pending = vec![offset];
        while let Some(offset) = pending.pop() {
            match offset {
                AddressOffset::Constant(value) => {
                    constant = constant.checked_add(sign * i128::from(*value))?
                }
                AddressOffset::Add(left, right) => {
                    pending.push(left);
                    pending.push(right);
                }
                other => {
                    if !charge_map_insert(other, terms.len()) {
                        return None;
                    }
                    let coefficient = terms.entry(other.clone()).or_default();
                    *coefficient = coefficient.checked_add(sign)?;
                }
            }
        }
    }
    terms.retain(|_, coefficient| *coefficient != 0);
    terms.is_empty().then_some(constant)
}

/// Literal discovery over one explicit unsigned expression. The charged walk
/// precedes the legacy constant recognizers; no fact or memory state is read.
pub(crate) fn unsigned_word_constant_for_discovery(
    value: crate::kernel::MachineOperandView<'_>,
) -> Option<u64> {
    let word = Word(value);
    if !word_view::charge(word) {
        return None;
    }
    word_view::constants(&[word])
        .get(&word.key())
        .copied()
        .flatten()
}

/// A bounded discovery hint over two explicit pointers, with no fact context.
/// The caller still constructs its ordinary address identity and offset law.
pub(crate) fn constant_pointer_byte_difference(left: &Address, right: &Address) -> Option<i128> {
    if !charge_pointer(left)
        || !charge_pointer(right)
        || !address_base_equal(&left.base, &right.base)
    {
        return None;
    }
    offset_difference(&left.offset, &right.offset)
}

/// Goal-local alignment of null, heap, global and static addresses. This
/// reads only the named block's registration and the written byte offset;
/// symbolic offsets and facts about other pointers are deliberately excluded.
pub(crate) fn intrinsic_pointer_alignment(result: &Proposition) -> bool {
    pointer_alignment(None, result)
}

fn pointer_alignment(premise: Option<&Proposition>, result: &Proposition) -> bool {
    let Proposition::ConditionIs(condition, expected) = result else {
        return false;
    };
    let Some((goal_pointer, goal_alignment)) = checked_pointer_alignment(condition) else {
        return false;
    };
    if !charge_pointer(goal_pointer) {
        return false;
    }
    let premise_alignment = premise.and_then(|proposition| {
        let Proposition::ConditionIs(condition, true) = proposition else {
            return None;
        };
        checked_pointer_alignment(condition)
    });
    if premise.is_some() && premise_alignment.is_none() {
        return false;
    }
    if !goal_alignment.is_power_of_two() {
        return false;
    }
    let aligned = if let Some((base, alignment)) = premise_alignment {
        if !charge_pointer(base) {
            return false;
        }
        if !address_base_equal(&base.base, &goal_pointer.base) || alignment % goal_alignment != 0 {
            return false;
        }
        let mut candidates = vec![goal_pointer.offset.clone()];
        if let Some(reduced) = drop_aligned_scaled_addends(&goal_pointer.offset, goal_alignment) {
            candidates.push(reduced);
        }
        let Some(aligned) = candidates.into_iter().find_map(|candidate| {
            offset_difference(&candidate, &base.offset)
                .map(|delta| delta.rem_euclid(goal_alignment as i128) == 0)
        }) else {
            return false;
        };
        aligned
    } else {
        let intrinsic_alignment = if pointer_equal(goal_pointer, &Address::null()) {
            // The null address is zero, so every valid power-of-two alignment
            // divides it; use the largest possible bound as an intrinsic
            // alignment sentinel.
            Some(u64::MAX)
        } else {
            match &goal_pointer.base {
                AddressBase::Heap(_) => Some(crate::kernel::primitives::HEAP_ALLOCATION_ALIGNMENT),
                block => {
                    let Some(payload) = address_base_payload(block) else {
                        return false;
                    };
                    crate::kernel::primitives::registered_block_alignment_charged(block, payload)
                }
            }
        };
        let Some(intrinsic) = intrinsic_alignment else {
            return false;
        };
        if goal_alignment > intrinsic {
            return false;
        }
        let Some(delta) = offset_difference(&goal_pointer.offset, &AddressOffset::Constant(0))
        else {
            return false;
        };
        delta.rem_euclid(goal_alignment as i128) == 0
    };
    *expected == aligned
}

/// Remove symbolic scaled addends whose byte scale is divisible by the target
/// alignment.  Such an addend cannot change the pointer's residue.  The
/// traversal is iterative because this helper runs on source-shaped pointer
/// offsets and must not inherit their nesting depth.
fn drop_aligned_scaled_addends(offset: &AddressOffset, alignment: u64) -> Option<AddressOffset> {
    if !charge_pointer_offset(offset) {
        return None;
    }
    let alignment = i64::try_from(alignment).ok()?;
    let mut pending = vec![offset];
    let mut parts = Vec::new();
    while let Some(offset) = pending.pop() {
        match offset {
            AddressOffset::Add(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            other => parts.push(other.clone()),
        }
    }
    fn constant_factor(term: crate::kernel::MachineOperandView<'_>) -> Option<i64> {
        let (MachineIntegerType::Int32, MachineBinaryOp::Multiply, [left, right]) =
            term.binary()?
        else {
            return None;
        };
        left.word32_constant()
            .or_else(|| right.word32_constant())
            .map(|value| i64::from(value as i32))
    }
    let divisible = |part: &AddressOffset| match part {
        AddressOffset::Int32Scaled { value, byte_width }
        | AddressOffset::Int64Scaled {
            value, byte_width, ..
        } => {
            let scale = constant_factor(value.operand_view())
                .and_then(|factor| factor.checked_mul(*byte_width))
                .unwrap_or(*byte_width);
            scale != 0 && scale % alignment == 0
        }
        _ => false,
    };
    if !parts.iter().any(divisible) {
        return None;
    }
    Some(
        parts
            .into_iter()
            .filter(|part| !divisible(part))
            .reduce(AddressOffset::add)
            .unwrap_or(AddressOffset::Constant(0)),
    )
}

#[derive(Clone, Debug)]
enum TaggedTag<'a> {
    Constant(u64),
    Source(Word<'a>),
    Add(Arc<TaggedTag<'a>>, Word<'a>),
    Subtract(Arc<TaggedTag<'a>>, Word<'a>),
    BitwiseAnd(Arc<TaggedTag<'a>>, u64),
    BitwiseOr(Arc<TaggedTag<'a>>, u64),
}

#[derive(Clone, Debug)]
struct TaggedAddress<'a> {
    /// Pointer payloads can be large symbolic offset trees.  The iterative
    /// evaluator keeps one of these forms at every visited term, so sharing
    /// the payload is essential: cloning an `Address` here would turn a tag
    /// chain over a deep pointer into a payload-depth by tag-depth operation.
    pointer: Arc<Address>,
    tag: Arc<TaggedTag<'a>>,
    /// The tag's constant value, when it is known.  Keeping this alongside
    /// the term is important: a symbolic tag chain must not be recursively
    /// re-evaluated every time another address operation extends it.
    tag_constant: Option<u64>,
}

/// Compare compact tag expressions without materializing their nested
/// bitvector syntax.  Shared tag prefixes are discharged by pointer identity;
/// distinct source leaves use the bounded iterative term comparator.
fn tagged_tag_equal<'a>(left: &Arc<TaggedTag<'a>>, right: &Arc<TaggedTag<'a>>) -> bool {
    let mut pending = vec![(Arc::clone(left), Arc::clone(right))];
    while let Some((left, right)) = pending.pop() {
        if Arc::ptr_eq(&left, &right) {
            continue;
        }
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return false;
        }
        match (&*left, &*right) {
            (TaggedTag::Constant(left), TaggedTag::Constant(right)) => {
                if left != right {
                    return false;
                }
            }
            (TaggedTag::Source(left), TaggedTag::Source(right)) => {
                if !word_view::equal(*left, *right) {
                    return false;
                }
            }
            (TaggedTag::Add(left_tag, left_term), TaggedTag::Add(right_tag, right_term))
            | (
                TaggedTag::Subtract(left_tag, left_term),
                TaggedTag::Subtract(right_tag, right_term),
            ) => {
                if !word_view::equal(*left_term, *right_term) {
                    return false;
                }
                pending.push((Arc::clone(left_tag), Arc::clone(right_tag)));
            }
            (
                TaggedTag::BitwiseAnd(left_tag, left_mask),
                TaggedTag::BitwiseAnd(right_tag, right_mask),
            )
            | (
                TaggedTag::BitwiseOr(left_tag, left_mask),
                TaggedTag::BitwiseOr(right_tag, right_mask),
            ) => {
                if left_mask != right_mask {
                    return false;
                }
                pending.push((Arc::clone(left_tag), Arc::clone(right_tag)));
            }
            _ => return false,
        }
    }
    true
}

fn pointer_index_hash(view: crate::kernel::MachineOperandView<'_>) -> Option<u64> {
    if let Some(leaf) = view
        .literal()
        .map(std::borrow::Cow::Owned)
        .or_else(|| view.read_source())
    {
        return bounded_term_hash(&leaf);
    }
    let (format, op, [left, right]) = view.binary()?;
    use MachineBinaryOp as O;
    use MachineIntegerType as T;
    if !matches!(
        (format, op),
        (
            T::Int32,
            O::Add | O::Subtract | O::BitwiseAnd | O::BitwiseOr
        ) | (
            T::UInt64,
            O::Add | O::Subtract | O::BitwiseAnd | O::BitwiseOr
        )
    ) {
        return None;
    }
    // Called only after the occurrence/depth-bounded pointer payload check.
    let header = MachineTerm::Binary {
        format,
        op,
        left: Box::new(MachineTerm::constant(0)),
        right: Box::new(MachineTerm::constant(0)),
    };
    let mut hash = DefaultHasher::new();
    std::mem::discriminant(&header).hash(&mut hash);
    (format, op).hash(&mut hash);
    pointer_index_hash(left)?.hash(&mut hash);
    pointer_index_hash(right)?.hash(&mut hash);
    Some(hash.finish())
}

fn pointer_identity_hash(pointer: &Address) -> Option<u64> {
    let payload = pointer_payload(pointer)?;
    if crate::instrumentation::deadline_exceeded_with_work(payload.max(1)) {
        return None;
    }
    let mut hasher = DefaultHasher::new();
    pointer.base.hash(&mut hasher);
    let mut pending = vec![&pointer.offset];
    while let Some(offset) = pending.pop() {
        match offset {
            AddressOffset::Constant(value) => {
                0u8.hash(&mut hasher);
                value.hash(&mut hasher);
            }
            AddressOffset::Variable(value) => {
                1u8.hash(&mut hasher);
                value.hash(&mut hasher);
            }
            AddressOffset::Add(left, right) => {
                2u8.hash(&mut hasher);
                pending.push(right);
                pending.push(left);
            }
            AddressOffset::Int32Scaled { value, byte_width } => {
                3u8.hash(&mut hasher);
                byte_width.hash(&mut hasher);
                pointer_index_hash(value.operand_view())?.hash(&mut hasher);
            }
            AddressOffset::Int64Scaled { .. } => return None,
        }
    }
    Some(hasher.finish())
}

/// An indexed view of the alignment evidence for one certificate node.  The
/// hash is only an index: a collision still goes through the bounded,
/// iterative pointer comparison before evidence is accepted.
struct AlignmentIndex<'a> {
    by_hash: HashMap<u64, Vec<AlignmentEntry<'a>>>,
}

struct AlignmentEntry<'a> {
    pointer: &'a Address,
    max_alignment: u64,
}

impl<'a> AlignmentIndex<'a> {
    fn new(alignments: &'a [(&'a Address, u64)]) -> Option<Self> {
        let mut by_hash: HashMap<u64, Vec<AlignmentEntry<'a>>> = HashMap::new();
        for (pointer, alignment) in alignments {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return None;
            }
            let candidates = by_hash.entry(pointer_identity_hash(pointer)?).or_default();
            let mut matched = false;
            for candidate in candidates.iter_mut() {
                if crate::instrumentation::deadline_exceeded_with_work(1) {
                    return None;
                }
                if pointer_equal(pointer, candidate.pointer) {
                    candidate.max_alignment = candidate.max_alignment.max(*alignment);
                    matched = true;
                    break;
                }
            }
            if !matched {
                candidates.push(AlignmentEntry {
                    pointer,
                    max_alignment: *alignment,
                });
            }
        }
        Some(Self { by_hash })
    }

    fn supports(&self, pointer: &Address, required: u64) -> bool {
        let Some(hash) = pointer_identity_hash(pointer) else {
            return false;
        };
        self.by_hash.get(&hash).is_some_and(|candidates| {
            candidates.iter().any(|candidate| {
                if crate::instrumentation::deadline_exceeded_with_work(1) {
                    return false;
                }
                candidate.max_alignment >= required && pointer_equal(pointer, candidate.pointer)
            })
        })
    }
}

fn bounded_term_hashes(roots: &[&MachineTerm]) -> Option<HashMap<usize, u64>> {
    let mut pending = roots.iter().map(|root| (*root, false)).collect::<Vec<_>>();
    let mut hashes: HashMap<usize, u64> = HashMap::new();
    while let Some((term, expanded)) = pending.pop() {
        let identity = term as *const MachineTerm as usize;
        if hashes.contains_key(&identity) {
            continue;
        }
        if expanded {
            let mut hasher = DefaultHasher::new();
            std::mem::discriminant(term).hash(&mut hasher);
            // One variant spells every format-carrying operator, so its
            // format and operator are part of the identity.
            if let MachineTerm::Binary { format, op, .. } = term {
                (format, op).hash(&mut hasher);
            }
            // So is a constant's format: one variant spells every constant.
            if let MachineTerm::Constant { format, .. } = term {
                format.hash(&mut hasher);
            }
            match term {
                bits32_constant!(value) => constant_u32(*value).hash(&mut hasher),
                int64_constant!(value) => constant_i64(*value).hash(&mut hasher),
                uint64_constant!(value) => constant_u64(*value).hash(&mut hasher),
                MachineTerm::Variable(value) => value.hash(&mut hasher),
                MachineTerm::MemoryLoad(memory, pointer, kind) => {
                    memory.shared_memory().arena_id().hash(&mut hasher);
                    kind.hash(&mut hasher);
                    pointer_identity_hash(pointer)?.hash(&mut hasher);
                }
                MachineTerm::PointerAddress(pointer, _) => {
                    pointer_identity_hash(pointer)?.hash(&mut hasher)
                }
                binary_term!(Int32, Add, left, right)
                | binary_term!(Int32, Subtract, left, right)
                | MachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op:
                        MachineBinaryOp::Add
                        | MachineBinaryOp::Subtract
                        | MachineBinaryOp::BitwiseAnd
                        | MachineBinaryOp::BitwiseOr,
                    left,
                    right,
                }
                | binary_term!(Int32, BitwiseAnd, left, right)
                | binary_term!(Int32, BitwiseOr, left, right) => {
                    hashes
                        .get(&(left.as_ref() as *const _ as usize))?
                        .hash(&mut hasher);
                    hashes
                        .get(&(right.as_ref() as *const _ as usize))?
                        .hash(&mut hasher);
                }
                _ => return None,
            }
            hashes.insert(identity, hasher.finish());
        } else {
            pending.push((term, true));
            match term {
                binary_term!(Int32, Add, left, right)
                | binary_term!(Int32, Subtract, left, right)
                | MachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op:
                        MachineBinaryOp::Add
                        | MachineBinaryOp::Subtract
                        | MachineBinaryOp::BitwiseAnd
                        | MachineBinaryOp::BitwiseOr,
                    left,
                    right,
                }
                | binary_term!(Int32, BitwiseAnd, left, right)
                | binary_term!(Int32, BitwiseOr, left, right) => {
                    pending.push((right, false));
                    pending.push((left, false));
                }
                _ => {}
            }
        }
    }
    Some(hashes)
}

fn bounded_term_hash(root: &MachineTerm) -> Option<u64> {
    bounded_term_hashes(&[root])?
        .get(&(root as *const MachineTerm as usize))
        .copied()
}

fn constant_value(term: Word<'_>, constants: &HashMap<WordKey, Option<u64>>) -> Option<u64> {
    constants.get(&term.key()).copied().flatten()
}

fn add_tag<'a>(
    form: TaggedAddress<'a>,
    right: Word<'a>,
    right_constant: Option<u64>,
) -> TaggedAddress<'a> {
    if form.tag_constant == Some(0) {
        TaggedAddress {
            pointer: form.pointer,
            tag: right_constant.map_or_else(
                || masked_source_tag(right),
                |value| Arc::new(TaggedTag::Constant(value)),
            ),
            tag_constant: right_constant,
        }
    } else if right_constant == Some(0) {
        form
    } else {
        TaggedAddress {
            pointer: form.pointer,
            tag: form.tag_constant.zip(right_constant).map_or_else(
                || Arc::new(TaggedTag::Add(form.tag, right)),
                |(left, right)| Arc::new(TaggedTag::Constant(left.wrapping_add(right))),
            ),
            tag_constant: form
                .tag_constant
                .zip(right_constant)
                .map(|(left, right)| left.wrapping_add(right)),
        }
    }
}

fn masked_source_tag<'a>(term: Word<'a>) -> Arc<TaggedTag<'a>> {
    if let Some((source, mask)) = masked_source(term) {
        Arc::new(TaggedTag::BitwiseAnd(
            Arc::new(TaggedTag::Source(source)),
            mask,
        ))
    } else {
        Arc::new(TaggedTag::Source(term))
    }
}

fn masked_source(term: Word<'_>) -> Option<(Word<'_>, u64)> {
    let WordNode::Binary {
        format: MachineIntegerType::UInt64,
        op: MachineBinaryOp::BitwiseAnd,
        left,
        right,
    } = term.node()
    else {
        return None;
    };
    match (left.uint64_as_const(), right.uint64_as_const()) {
        (None, Some(mask)) => Some((left, mask)),
        (Some(mask), None) => Some((right, mask)),
        _ => None,
    }
}
fn pointer_or_masked_tag<'a>(
    left: Word<'a>,
    right: Word<'a>,
) -> Option<(&'a Address, Word<'a>, u64)> {
    let (pointer, tag) = match (left.node(), right.node()) {
        (WordNode::PointerAddress(pointer), _) => (pointer, right),
        (_, WordNode::PointerAddress(pointer)) => (pointer, left),
        _ => return None,
    };
    let (_, mask) = masked_source(tag)?;
    let alignment = mask.checked_add(1).filter(|v| v.is_power_of_two())?;
    Some((pointer, tag, alignment))
}

fn tagged_form<'a>(
    term: Word<'a>,
    relation: (Word<'a>, Word<'a>),
    alignments: &AlignmentIndex<'_>,
) -> Option<TaggedAddress<'a>> {
    tagged_form_inner(term, Some(relation), alignments)
}

fn tagged_form_from_alignment<'a>(
    term: Word<'a>,
    alignments: &AlignmentIndex<'_>,
) -> Option<TaggedAddress<'a>> {
    tagged_form_inner(term, None, alignments)
}

fn tagged_form_inner<'a>(
    term: Word<'a>,
    relation: Option<(Word<'a>, Word<'a>)>,
    alignments: &AlignmentIndex<'_>,
) -> Option<TaggedAddress<'a>> {
    let identities = if let Some((left, right)) = relation {
        word_view::hashes(&[term, left, right])?
    } else {
        word_view::hashes(&[term])?
    };
    let constants = if let Some((left, right)) = relation {
        word_view::constants(&[term, left, right])
    } else {
        word_view::constants(&[term])
    };
    if constants.is_empty() {
        return None;
    }
    let relation_keys = relation.map(|(left, right)| {
        (
            identities.get(&left.key()).copied(),
            identities.get(&right.key()).copied(),
        )
    });
    enum Task<'a> {
        Visit(Word<'a>),
        FinishAdd {
            term: Word<'a>,
            left: Word<'a>,
            right: Word<'a>,
        },
        FinishAddRight {
            term: Word<'a>,
            left: Word<'a>,
        },
        FinishSubtract {
            term: Word<'a>,
            right: Word<'a>,
        },
        FinishAnd {
            term: Word<'a>,
            mask: u64,
            alignment: u64,
        },
        FinishOr {
            term: Word<'a>,
            constant: u64,
            alignment: u64,
        },
        FinishPointerOr {
            term: Word<'a>,
            pointer: &'a Address,
            tag: Word<'a>,
            alignment: u64,
        },
        FinishRelation {
            term: Word<'a>,
        },
    }

    fn store<'a>(
        identity: WordKey,
        result: Option<TaggedAddress<'a>>,
        active: &mut HashSet<WordKey>,
        results: &mut HashMap<WordKey, Option<TaggedAddress<'a>>>,
        values: &mut Vec<Option<TaggedAddress<'a>>>,
    ) {
        active.remove(&identity);
        values.push(result.clone());
        results.insert(identity, result);
    }

    let mut tasks = vec![Task::Visit(term)];
    let mut values = Vec::new();
    let mut active = HashSet::new();
    let mut results: HashMap<WordKey, Option<TaggedAddress<'a>>> = HashMap::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(current) => {
                let identity = current.key();
                if let Some(result) = results.get(&identity) {
                    values.push(result.clone());
                    continue;
                }
                if active.contains(&identity) {
                    values.push(None);
                    continue;
                }
                active.insert(identity);
                match current.node() {
                    WordNode::PointerAddress(pointer) => store(
                        identity,
                        Some(TaggedAddress {
                            pointer: Arc::new(pointer.clone()),
                            tag: Arc::new(TaggedTag::Constant(0)),
                            tag_constant: Some(0),
                        }),
                        &mut active,
                        &mut results,
                        &mut values,
                    ),
                    WordNode::Binary {
                        format: MachineIntegerType::UInt64,
                        op: MachineBinaryOp::Add,
                        left,
                        right,
                    } => {
                        tasks.push(Task::FinishAdd {
                            term: current,
                            left,
                            right,
                        });
                        tasks.push(Task::Visit(left));
                    }
                    WordNode::Binary {
                        format: MachineIntegerType::UInt64,
                        op: MachineBinaryOp::Subtract,
                        left,
                        right,
                    } => {
                        tasks.push(Task::FinishSubtract {
                            term: current,
                            right,
                        });
                        tasks.push(Task::Visit(left));
                    }
                    WordNode::Binary {
                        format: MachineIntegerType::UInt64,
                        op: MachineBinaryOp::BitwiseAnd,
                        left,
                        right,
                    } => {
                        let (inner, mask) = match (
                            constant_value(left, &constants),
                            constant_value(right, &constants),
                        ) {
                            (None, Some(mask)) => (left, mask),
                            (Some(mask), None) => (right, mask),
                            _ => {
                                store(identity, None, &mut active, &mut results, &mut values);
                                continue;
                            }
                        };
                        let Some(alignment) =
                            (!mask).checked_add(1).filter(|v| v.is_power_of_two())
                        else {
                            store(identity, None, &mut active, &mut results, &mut values);
                            continue;
                        };
                        tasks.push(Task::FinishAnd {
                            term: current,
                            mask,
                            alignment,
                        });
                        tasks.push(Task::Visit(inner));
                    }
                    WordNode::Binary {
                        format: MachineIntegerType::UInt64,
                        op: MachineBinaryOp::BitwiseOr,
                        left,
                        right,
                    } => {
                        if let Some((pointer, tag, alignment)) = pointer_or_masked_tag(left, right)
                        {
                            tasks.push(Task::FinishPointerOr {
                                term: current,
                                pointer,
                                tag,
                                alignment,
                            });
                            continue;
                        }
                        let (inner, constant) = match (
                            constant_value(left, &constants),
                            constant_value(right, &constants),
                        ) {
                            (None, Some(constant)) => (left, constant),
                            (Some(constant), None) => (right, constant),
                            _ => {
                                store(identity, None, &mut active, &mut results, &mut values);
                                continue;
                            }
                        };
                        let Some(alignment) = constant
                            .checked_add(1)
                            .and_then(|value| value.checked_next_power_of_two())
                        else {
                            store(identity, None, &mut active, &mut results, &mut values);
                            continue;
                        };
                        tasks.push(Task::FinishOr {
                            term: current,
                            constant,
                            alignment,
                        });
                        tasks.push(Task::Visit(inner));
                    }
                    _ if relation_keys
                        .is_some_and(|(left, _)| left == identities.get(&identity).copied())
                        && relation.is_some_and(|(left, _)| word_view::equal(current, left)) =>
                    {
                        let (_, right) = relation.expect("relation key is present");
                        tasks.push(Task::FinishRelation { term: current });
                        tasks.push(Task::Visit(right));
                    }
                    _ if relation_keys
                        .is_some_and(|(_, right)| right == identities.get(&identity).copied())
                        && relation.is_some_and(|(_, right)| word_view::equal(current, right)) =>
                    {
                        let (left, _) = relation.expect("relation key is present");
                        tasks.push(Task::FinishRelation { term: current });
                        tasks.push(Task::Visit(left));
                    }
                    _ => store(identity, None, &mut active, &mut results, &mut values),
                }
            }
            Task::FinishAdd { term, left, right } => {
                let left_form = values.pop().flatten();
                if let Some(form) = left_form {
                    store(
                        term.key(),
                        Some(add_tag(form, right, constant_value(right, &constants))),
                        &mut active,
                        &mut results,
                        &mut values,
                    );
                } else {
                    tasks.push(Task::FinishAddRight { term, left });
                    tasks.push(Task::Visit(right));
                }
            }
            Task::FinishAddRight { term, left } => {
                let right_form = values.pop().flatten();
                store(
                    term.key(),
                    right_form.map(|form| add_tag(form, left, constant_value(left, &constants))),
                    &mut active,
                    &mut results,
                    &mut values,
                );
            }
            Task::FinishSubtract { term, right } => {
                let left_form = values.pop().flatten();
                store(
                    term.key(),
                    left_form.map(|form| {
                        let right_constant = constant_value(right, &constants);
                        let tag = form.tag_constant.zip(right_constant).map_or_else(
                            || Arc::new(TaggedTag::Subtract(form.tag, right)),
                            |(left, right)| Arc::new(TaggedTag::Constant(left.wrapping_sub(right))),
                        );
                        TaggedAddress {
                            pointer: form.pointer,
                            tag,
                            tag_constant: form
                                .tag_constant
                                .zip(right_constant)
                                .map(|(left, right)| left.wrapping_sub(right)),
                        }
                    }),
                    &mut active,
                    &mut results,
                    &mut values,
                );
            }
            Task::FinishAnd {
                term,
                mask,
                alignment,
            } => {
                let form = values.pop().flatten();
                store(
                    term.key(),
                    form.and_then(|form| {
                        // A symbolic tag may itself be an explicitly masked
                        // source term.  Disjoint masks establish a zero tag
                        // locally; this is the bounded normal-form rule used
                        // for the rbtree parent-word shape, not a context
                        // search or alternate derivation.
                        let tag = if let Some(value) = form.tag_constant {
                            Arc::new(TaggedTag::Constant(value & mask))
                        } else if let TaggedTag::BitwiseAnd(_, source_mask) = form.tag.as_ref()
                            && source_mask & mask == 0
                        {
                            Arc::new(TaggedTag::Constant(0))
                        } else if let TaggedTag::Source(source) = form.tag.as_ref()
                            && let WordNode::Binary {
                                format: MachineIntegerType::UInt64,
                                op: MachineBinaryOp::BitwiseAnd,
                                left,
                                right,
                            } = source.node()
                            && let Some(source_mask) = constant_value(left, &constants)
                                .or_else(|| constant_value(right, &constants))
                        {
                            if source_mask & mask == 0 {
                                Arc::new(TaggedTag::Constant(0))
                            } else {
                                Arc::new(TaggedTag::BitwiseAnd(form.tag, mask))
                            }
                        } else {
                            Arc::new(TaggedTag::BitwiseAnd(form.tag, mask))
                        };
                        let tag_constant = match tag.as_ref() {
                            TaggedTag::Constant(value) => Some(*value),
                            _ => None,
                        };
                        alignments
                            .supports(form.pointer.as_ref(), alignment)
                            .then_some(TaggedAddress {
                                pointer: form.pointer,
                                tag,
                                tag_constant,
                            })
                    }),
                    &mut active,
                    &mut results,
                    &mut values,
                );
            }
            Task::FinishOr {
                term,
                constant,
                alignment,
            } => {
                let form = values.pop().flatten();
                store(
                    term.key(),
                    form.and_then(|form| {
                        let tag = form.tag_constant.map_or_else(
                            || Arc::new(TaggedTag::BitwiseOr(form.tag, constant)),
                            |value| Arc::new(TaggedTag::Constant(value | constant)),
                        );
                        (constant == 0 || alignments.supports(form.pointer.as_ref(), alignment))
                            .then_some(TaggedAddress {
                                pointer: form.pointer,
                                tag,
                                tag_constant: form.tag_constant.map(|tag| tag | constant),
                            })
                    }),
                    &mut active,
                    &mut results,
                    &mut values,
                );
            }
            Task::FinishPointerOr {
                term,
                pointer,
                tag,
                alignment,
            } => {
                store(
                    term.key(),
                    alignments
                        .supports(pointer, alignment)
                        .then(|| TaggedAddress {
                            pointer: Arc::new(pointer.clone()),
                            tag: masked_source_tag(tag),
                            tag_constant: None,
                        }),
                    &mut active,
                    &mut results,
                    &mut values,
                );
            }
            Task::FinishRelation { term } => {
                let result = values.pop().flatten();
                store(term.key(), result, &mut active, &mut results, &mut values);
            }
        }
    }
    values.pop().flatten()
}

/// Reading low tag bits only needs the base aligned to the mask's modulus.
/// The existing bounded word walker supplies the tag; no ambient reasoning or
/// memory history is consulted. Addition is modular, so higher tag bits do not
/// affect this projection.
fn pointer_tag_read_equal<'a>(
    left: Word<'a>,
    right: Word<'a>,
    relation: Option<(Word<'a>, Word<'a>)>,
    alignments: &AlignmentIndex<'_>,
) -> bool {
    let project = |term: Word<'a>| {
        let (word, mask) = masked_source(term)?;
        let alignment = mask
            .checked_add(1)
            .filter(|value| *value > 1 && value.is_power_of_two())?;
        let form = tagged_form_inner(word, relation, alignments)?;
        if !alignments.supports(form.pointer.as_ref(), alignment) {
            return None;
        }
        let tag = match form.tag.as_ref() {
            TaggedTag::Constant(value) => Arc::new(TaggedTag::Constant(value & mask)),
            TaggedTag::BitwiseAnd(inner, inner_mask) => {
                let mask = inner_mask & mask;
                if mask == 0 {
                    Arc::new(TaggedTag::Constant(0))
                } else {
                    Arc::new(TaggedTag::BitwiseAnd(Arc::clone(inner), mask))
                }
            }
            _ => Arc::new(TaggedTag::BitwiseAnd(form.tag, mask)),
        };
        Some(tag)
    };
    let source = |term: Word<'a>| {
        term.uint64_as_const().map_or_else(
            || masked_source_tag(term),
            |value| Arc::new(TaggedTag::Constant(value)),
        )
    };
    project(left).is_some_and(|tag| tagged_tag_equal(&tag, &source(right)))
        || project(right).is_some_and(|tag| tagged_tag_equal(&source(left), &tag))
}

fn word_comparison(
    proposition: &Proposition,
) -> Option<(
    crate::kernel::machine_integer::comparison::StructuralComparisonView<'_>,
    bool,
)> {
    let Proposition::ConditionIs(condition, truth) = proposition else {
        return None;
    };
    let view = crate::kernel::machine_integer::comparison::structural_comparison_view(condition)?;
    if !matches!(
        view.format,
        MachineIntegerType::Int64 | MachineIntegerType::UInt64
    ) || view.relation != CompareRelation::Equal
    {
        return None;
    }
    let expected = *truth != view.negated;
    Some((view, expected))
}

fn pointer_word_equality(
    relation: &Proposition,
    alignment_premises: &[&Proposition],
    result: &Proposition,
) -> bool {
    let Some((relation_view, true)) = word_comparison(relation) else {
        return false;
    };
    let [left, right] = relation_view
        .operands
        .each_ref()
        .map(|operand| Word(operand.operand_view()));
    let Some((goal_view, expected)) = word_comparison(result) else {
        return false;
    };
    let [goal_left, goal_right] = goal_view
        .operands
        .each_ref()
        .map(|operand| Word(operand.operand_view()));
    if ![left, right, goal_left, goal_right]
        .into_iter()
        .all(word_view::charge)
    {
        return false;
    }
    let mut alignments = Vec::new();
    for premise in alignment_premises {
        let Proposition::ConditionIs(condition, true) = premise else {
            return false;
        };
        let Some((pointer, alignment)) = checked_pointer_alignment(condition) else {
            return false;
        };
        if !charge_pointer(pointer) {
            return false;
        }
        alignments.push((pointer, alignment));
    }
    let Some(alignment_index) = AlignmentIndex::new(&alignments) else {
        return false;
    };
    if tagged_form(left, (left, right), &alignment_index).is_none()
        || tagged_form(right, (left, right), &alignment_index).is_none()
    {
        return false;
    }
    if expected
        && pointer_tag_read_equal(goal_left, goal_right, Some((left, right)), &alignment_index)
    {
        return true;
    }
    let goal_left_form = tagged_form(goal_left, (left, right), &alignment_index);
    let goal_right_form = tagged_form(goal_right, (left, right), &alignment_index);
    let equal = match (goal_left_form, goal_right_form) {
        (Some(goal_left), Some(goal_right)) => {
            pointer_equal(goal_left.pointer.as_ref(), goal_right.pointer.as_ref())
                && tagged_tag_equal(&goal_left.tag, &goal_right.tag)
        }
        _ => false,
    };
    let structural = if expected {
        equal
    } else {
        match (
            tagged_form(goal_left, (left, right), &alignment_index),
            tagged_form(goal_right, (left, right), &alignment_index),
        ) {
            (Some(goal_left), Some(goal_right))
                if pointer_equal(goal_left.pointer.as_ref(), goal_right.pointer.as_ref()) =>
            {
                matches!(
                    (goal_left.tag_constant, goal_right.tag_constant),
                    (Some(left), Some(right)) if left != right
                )
            }
            _ => false,
        }
    };
    if structural {
        return true;
    }
    false
}

fn pointer_word_from_alignment(alignment_premises: &[&Proposition], result: &Proposition) -> bool {
    let Some((view, expected)) = word_comparison(result) else {
        return false;
    };
    let [left, right] = view
        .operands
        .each_ref()
        .map(|operand| Word(operand.operand_view()));
    if !word_view::charge(left) || !word_view::charge(right) {
        return false;
    }
    for premise in alignment_premises {
        let Proposition::ConditionIs(condition, true) = premise else {
            return false;
        };
        if checked_pointer_alignment(condition).is_none() {
            return false;
        }
    }
    let alignments = alignment_premises
        .iter()
        .map(|premise| {
            let Proposition::ConditionIs(condition, true) = premise else {
                unreachable!("alignment premises were checked above");
            };
            checked_pointer_alignment(condition).expect("alignment premises were checked above")
        })
        .collect::<Vec<_>>();
    let alignment_index = AlignmentIndex::new(&alignments);
    let Some(alignment_index) = alignment_index else {
        return false;
    };
    if expected && pointer_tag_read_equal(left, right, None, &alignment_index) {
        return true;
    }
    let left_form = tagged_form_from_alignment(left, &alignment_index);
    let right_form = tagged_form_from_alignment(right, &alignment_index);
    let Some(left_form) = left_form else {
        return false;
    };
    let Some(right_form) = right_form else {
        return false;
    };
    let equal = pointer_equal(left_form.pointer.as_ref(), right_form.pointer.as_ref())
        && tagged_tag_equal(&left_form.tag, &right_form.tag);
    if expected {
        equal
    } else {
        pointer_equal(left_form.pointer.as_ref(), right_form.pointer.as_ref())
            && matches!(
                (left_form.tag_constant, right_form.tag_constant),
                (Some(left), Some(right)) if left != right
            )
    }
}

fn float_reflexive(finite: &Proposition, result: &Proposition) -> bool {
    let Proposition::ConditionIs(finite_condition, true) = finite else {
        return false;
    };
    let (finite_expression, finite_width) = match finite_condition {
        ConditionTerm::Float32(FloatCondition::Classification {
            value: expression,
            classification: FloatClassification::Finite,
        }) => (expression.as_ref(), 32),
        ConditionTerm::Float64(FloatCondition::Classification {
            value: expression,
            classification: FloatClassification::Finite,
        }) => (expression.as_ref(), 64),
        _ => return false,
    };
    if !charge_bitvector(finite_expression) {
        return false;
    }
    let Some((condition, left, right)) = finite_float_comparison(result) else {
        return false;
    };
    let width = if matches!(condition, ConditionTerm::Float32(_)) {
        32
    } else {
        64
    };
    charge_bitvector(left)
        && charge_bitvector(right)
        && bitvector_equal(left, right)
        && width == finite_width
        && bitvector_equal(left, finite_expression)
}

/// Extract the operands when the comparison has the polarity it would have
/// on equal finite operands.
fn finite_float_comparison(
    result: &Proposition,
) -> Option<(&ConditionTerm, &MachineTerm, &MachineTerm)> {
    let Proposition::ConditionIs(condition, expected) = result else {
        return None;
    };
    let (operator, left, right) = match condition {
        ConditionTerm::Float32(FloatCondition::Comparison {
            operator,
            left,
            right,
        })
        | ConditionTerm::Float64(FloatCondition::Comparison {
            operator,
            left,
            right,
        }) => (*operator, left.as_ref(), right.as_ref()),
        _ => return None,
    };
    let reflexive = matches!(
        operator,
        ComparisonOperator::Equal
            | ComparisonOperator::LessEqual
            | ComparisonOperator::GreaterEqual
    );
    (*expected == reflexive).then_some((condition, left, right))
}

pub(super) fn finite_float_reflexivity_premise(result: &Proposition) -> Option<Proposition> {
    let (condition, operand, other) = finite_float_comparison(result)?;
    if operand != other {
        return None;
    }
    let finite = match condition {
        ConditionTerm::Float32(_) => {
            ConditionTerm::float32_classification(operand.clone(), FloatClassification::Finite)
        }
        ConditionTerm::Float64(_) => {
            ConditionTerm::float64_classification(operand.clone(), FloatClassification::Finite)
        }
        _ => unreachable!("finite reflexivity only selects float comparisons"),
    };
    Some(Proposition::ConditionIs(finite, true))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shared_pointer_certificate_identity_preserves_payload_and_hash() {
        use crate::kernel::{
            KernelTerm, KernelTermExport, MachineOperandView as V, SharedMachineIntegerTerm as S,
            VerificationSession,
        };
        let _session = VerificationSession::enter();
        let x = MachineTerm::Variable(crate::kernel::Variable(1081201));
        let mut native = x.clone();
        let mut root =
            KernelTerm::retained_machine_operand(MachineIntegerType::Int32, V::Legacy(&x));
        for depth in 0..9 {
            let index = S::from_shared(MachineIntegerType::Int32, root.clone()).unwrap();
            let pointer = Address {
                base: AddressBase::ExternalArgument,
                offset: AddressOffset::Int32Scaled {
                    value: index.clone(),
                    byte_width: 4,
                },
            };
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(
                pointer_index_payload(index.operand_view()),
                bitvector_payload(&native),
                "depth {depth}"
            );
            if bitvector_payload(&native).is_some() {
                assert_eq!(
                    pointer_index_hash(index.operand_view()),
                    bounded_term_hash(&native)
                );
            }
            let equal = pointer_offset_equal(&pointer.offset, &pointer.offset);
            assert_eq!(equal, bitvector_payload(&native).is_some());
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
            native = MachineTerm::Binary {
                format: MachineIntegerType::Int32,
                op: MachineBinaryOp::Add,
                left: Box::new(native.clone()),
                right: Box::new(native),
            };
        }
    }

    #[test]
    fn signed_domain_query_views_match_legacy_interval_shapes() {
        use crate::kernel::machine_integer::definedness::{
            integer_bounds_of_definedness, interval_query_form,
        };
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            for op in [
                OverflowOperation::Add,
                OverflowOperation::Subtract,
                OverflowOperation::Multiply,
                OverflowOperation::Divide,
            ] {
                let legacy = Proposition::ConditionIs(
                    ConditionTerm::Overflows {
                        format,
                        op,
                        left: Box::new(MachineTerm::Variable(crate::kernel::Variable(986302))),
                        right: Box::new(
                            if format == MachineIntegerType::Int64
                                || format == MachineIntegerType::UInt64
                            {
                                MachineTerm::int64_constant(1)
                            } else {
                                MachineTerm::constant(1)
                            },
                        ),
                    },
                    false,
                );
                let mut forms = vec![legacy.clone()];
                let bounds = integer_bounds_of_definedness(&legacy);
                if let [a, b] = bounds.as_slice() {
                    forms.extend([
                        a.clone(),
                        Proposition::And(Box::new(a.clone()), Box::new(b.clone())),
                        Proposition::And(Box::new(b.clone()), Box::new(a.clone())),
                    ]);
                    forms.push(Proposition::And(
                        Box::new(Proposition::And(Box::new(a.clone()), Box::new(b.clone()))),
                        Box::new(legacy.clone()),
                    ));
                }
                for proposition in forms {
                    let adapted = interval_query_form(&proposition);
                    let expected =
                        signed_definedness_operands(adapted.as_ref().unwrap_or(&proposition));
                    let query = signed_definedness_query(&proposition);
                    assert_eq!(query.is_some(), expected.is_some());
                    if let (
                        Some((width, operands, subtract)),
                        Some((expected_width, left, right, expected_subtract)),
                    ) = (query, expected)
                    {
                        assert_eq!(width, expected_width);
                        assert_eq!(subtract, expected_subtract);
                        let ty = match width {
                            SignedDefinedWidth::Int32 => MachineIntegerType::Int32,
                            SignedDefinedWidth::Int64 => MachineIntegerType::Int64,
                        };
                        for (operand, expected) in operands.iter().zip([left, right]) {
                            assert!(
                                operand.operand_view().retain(ty)
                                    == crate::kernel::SharedMachineIntegerTerm::intern(
                                        ty,
                                        expected.clone()
                                    )
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn constant_bound_views_preserve_native_comparison_polarity() {
        use crate::kernel::{MachineOperandView, Variable};
        for (format, width) in [
            (MachineIntegerType::Int32, SignedDefinedWidth::Int32),
            (MachineIntegerType::Int64, SignedDefinedWidth::Int64),
        ] {
            let term = MachineTerm::Variable(Variable(982601));
            for constant in [-5, 0, 7] {
                let literal = if format == MachineIntegerType::Int32 {
                    MachineTerm::constant(constant as u32)
                } else {
                    MachineTerm::int64_constant(constant)
                };
                for relation in [
                    CompareRelation::Equal,
                    CompareRelation::LessThan,
                    CompareRelation::LessEqual,
                    CompareRelation::GreaterThan,
                    CompareRelation::GreaterEqual,
                ] {
                    for reverse in [false, true] {
                        for truth in [false, true] {
                            let (left, right) = if reverse {
                                (literal.clone(), term.clone())
                            } else {
                                (term.clone(), literal.clone())
                            };
                            let premise = Proposition::ConditionIs(
                                ConditionTerm::Compare {
                                    format,
                                    relation,
                                    left: Box::new(left),
                                    right: Box::new(right),
                                },
                                truth,
                            );
                            let expected = if relation == CompareRelation::Equal {
                                truth.then_some((Some(constant), Some(constant)))
                            } else {
                                let greater = matches!(
                                    relation,
                                    CompareRelation::GreaterThan | CompareRelation::GreaterEqual
                                ) ^ reverse
                                    ^ !truth;
                                let strict = matches!(
                                    relation,
                                    CompareRelation::LessThan | CompareRelation::GreaterThan
                                ) ^ !truth;
                                Some(if greater {
                                    (Some(constant + i64::from(strict)), None)
                                } else {
                                    (None, Some(constant - i64::from(strict)))
                                })
                            };
                            assert_eq!(
                                signed_constant_bound_on_view(
                                    width,
                                    &premise,
                                    MachineOperandView::Legacy(&term)
                                ),
                                expected
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn cast_term_identity_keeps_formats_and_operand_identity() {
        use crate::kernel::{IntegerTerm, MachineIntegerConstant, MachineIntegerType, Variable};
        let native_cast = |source, destination, variable| MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            value: Box::new(MachineTerm::Variable(Variable(variable))),
            from: source,
            to: destination,
        };
        let cast = native_cast(
            MachineIntegerType::Int32,
            MachineIntegerType::Int64,
            891_001,
        );
        assert!(bitvector_equal(&cast, &cast.clone()));
        for other in [
            native_cast(
                MachineIntegerType::UInt32,
                MachineIntegerType::Int64,
                891_001,
            ),
            native_cast(
                MachineIntegerType::Int32,
                MachineIntegerType::UInt64,
                891_001,
            ),
            native_cast(
                MachineIntegerType::Int32,
                MachineIntegerType::Int64,
                891_002,
            ),
        ] {
            assert!(!bitvector_equal(&cast, &other));
        }
        let observed = |destination, variable| MachineTerm::IntegerToMachine {
            value: IntegerTerm::Variable(Variable(variable)).into(),
            destination,
        };
        let cast = observed(MachineIntegerType::Int64, 891_003);
        assert!(bitvector_equal(&cast, &cast.clone()));
        assert!(!bitvector_equal(
            &cast,
            &observed(MachineIntegerType::UInt64, 891_003)
        ));
        assert!(!bitvector_equal(
            &cast,
            &observed(MachineIntegerType::Int64, 891_004)
        ));
        let constant = |value| {
            MachineTerm::machine_constant(
                MachineIntegerConstant::from_integer(MachineIntegerType::Int128.format(), &value)
                    .unwrap(),
            )
        };
        assert!(bitvector_equal(&constant(1.into()), &constant(1.into())));
        assert!(!bitvector_equal(&constant(1.into()), &constant(2.into())));
    }

    fn pointer(offset: AddressOffset) -> Address {
        Address {
            base: AddressBase::ExternalArgument,
            offset,
        }
    }

    fn add(left: AddressOffset, right: AddressOffset) -> AddressOffset {
        AddressOffset::Add(Box::new(left), Box::new(right))
    }

    fn tagged_tag_nodes(root: &Arc<TaggedTag<'_>>) -> usize {
        let mut pending = vec![Arc::clone(root)];
        let mut seen = HashSet::new();
        while let Some(tag) = pending.pop() {
            let identity = Arc::as_ptr(&tag) as usize;
            if !seen.insert(identity) {
                continue;
            }
            match &*tag {
                TaggedTag::Add(child, _)
                | TaggedTag::Subtract(child, _)
                | TaggedTag::BitwiseAnd(child, _)
                | TaggedTag::BitwiseOr(child, _) => pending.push(Arc::clone(child)),
                TaggedTag::Constant(_) | TaggedTag::Source(_) => {}
            }
        }
        seen.len()
    }

    fn deep_pointer(depth: usize) -> Address {
        let mut offset = AddressOffset::Constant(0);
        for _ in 0..depth {
            offset = add(offset, AddressOffset::Constant(1));
        }
        pointer(offset)
    }

    fn measured_tagged_form(pointer_depth: usize, tag_depth: usize) -> (bool, usize, usize) {
        let address = MachineTerm::PointerAddress(
            Box::new(deep_pointer(pointer_depth)),
            crate::kernel::AddressObjectClass::NONE,
        );
        let variable = MachineTerm::Variable(crate::kernel::Variable(394));
        let mut tagged = address;
        for index in 0..tag_depth {
            tagged = MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Add,
                left: Box::new(tagged),
                right: Box::new(MachineTerm::Variable(crate::kernel::Variable(
                    (400 + index) as u64,
                ))),
            };
        }
        let alignments = AlignmentIndex::new(&[]).expect("empty alignment index");
        let (form, work) = crate::instrumentation::measure_deterministic_work(|| {
            tagged_form(
                (&variable).into(),
                ((&variable).into(), (&tagged).into()),
                &alignments,
            )
        });
        let nodes = form
            .as_ref()
            .map(|form| tagged_tag_nodes(&form.tag))
            .unwrap_or(0);
        (form.is_some(), work, nodes)
    }

    #[test]
    fn pointer_scalar_bounds_do_not_admit_native_width_operations() {
        let wide = MachineTerm::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::Add,
            left: Box::new(MachineTerm::Variable(crate::kernel::Variable(1))),
            right: Box::new(MachineTerm::uint64_constant(1)),
        };
        let bound = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(wide),
                right: Box::new(MachineTerm::constant(i32::MAX as u32)),
            },
            true,
        );
        assert!(scalar_bounds(&[&bound]).is_none());
    }

    #[test]
    fn retained_masked_read_equation_checks_native_pointer_goal() {
        use crate::kernel::MachineOperandView;
        let _session = crate::kernel::VerificationSession::enter();
        let next = pointer(AddressOffset::Constant(0));
        let address = MachineTerm::pointer_address(next.clone());
        let raw = MachineTerm::MemoryLoad(
            crate::kernel::ProgramPoint::at(
                &(crate::kernel::intern_memory(crate::kernel::SymbolicMemory::new())),
            ),
            Box::new(next.clone()),
            crate::kernel::LoadKind::Bits64,
        );
        let tagged = MachineTerm::uint64_add(
            address.clone(),
            MachineTerm::uint64_bitwise_and(raw.clone(), MachineTerm::uint64_constant(1)),
        );
        let roots = [&raw, &tagged].map(|word| {
            crate::kernel::KernelTerm::retained_machine_operand(
                MachineIntegerType::UInt64,
                MachineOperandView::Legacy(word),
            )
        });
        let relation = Proposition::ConditionIs(
            crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::UInt64,
                CompareRelation::Equal,
                roots.each_ref().map(MachineOperandView::Shared),
            ),
            true,
        );
        let alignment = Proposition::ConditionIs(ConditionTerm::pointer_aligned(next, 8), true);
        let goal = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                address,
                MachineTerm::uint64_bitwise_and(raw, MachineTerm::uint64_constant(!1)),
            ),
            true,
        );
        let exports = crate::kernel::KernelTermExport::machine_export_count();
        assert!(pointer_word_equality(&relation, &[&alignment], &goal));
        assert_eq!(
            crate::kernel::KernelTermExport::machine_export_count(),
            exports
        );
    }

    #[test]
    fn tagged_word_tag_arena_stays_linear_for_deep_symbolic_chains() {
        let alignments = AlignmentIndex::new(&[]).expect("empty alignment index");
        let mut previous = 0;
        for depth in [4, 16, 64, 256, 1024] {
            let address = MachineTerm::PointerAddress(
                Box::new(pointer(AddressOffset::Constant(0))),
                crate::kernel::AddressObjectClass::NONE,
            );
            let variable = MachineTerm::Variable(crate::kernel::Variable(294));
            let mut tagged = address;
            for index in 0..depth {
                tagged = MachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::Add,
                    left: Box::new(tagged),
                    right: Box::new(MachineTerm::Variable(crate::kernel::Variable(300 + index))),
                };
            }
            let form = tagged_form(
                (&variable).into(),
                ((&variable).into(), (&tagged).into()),
                &alignments,
            )
            .expect("the relation should provide a tagged form");
            let nodes = tagged_tag_nodes(&form.tag);
            assert_eq!(nodes, depth as usize);
            assert!(nodes >= previous);
            previous = nodes;
        }
    }

    #[test]
    fn tagged_form_shares_deep_pointer_payload_across_tag_depth() {
        let (small_valid, small_work, small_nodes) = measured_tagged_form(4, 4);
        let (deep_pointer_valid, deep_pointer_work, deep_pointer_nodes) =
            measured_tagged_form(64, 4);
        let (deep_tags_valid, deep_tags_work, deep_tags_nodes) = measured_tagged_form(4, 64);
        let (cross_valid, cross_work, cross_nodes) = measured_tagged_form(64, 64);

        assert!(small_valid && deep_pointer_valid && deep_tags_valid && cross_valid);
        assert_eq!(small_nodes, 4);
        assert_eq!(deep_pointer_nodes, 4);
        assert_eq!(deep_tags_nodes, 64);
        assert_eq!(cross_nodes, 64);

        // Sharing the pointer payload makes the two dimensions additive.  A
        // pointer clone at every tag node would make the cross case grow like
        // pointer_depth * tag_depth and violate this bound by a wide margin.
        let additive_bound = small_work
            .saturating_add(deep_pointer_work)
            .saturating_add(deep_tags_work)
            .saturating_add(64);
        assert!(
            cross_work <= additive_bound,
            "cross-product work was not additive: small={small_work}, pointer={deep_pointer_work}, tags={deep_tags_work}, cross={cross_work}"
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/arithmetic_special/tests.rs");
    }
}

#[cfg(test)]
mod unsigned_widening_tests {
    use super::*;
    use crate::kernel::Variable;

    #[test]
    fn widened_operand_identity_preserves_leaf_and_conversion_identity() {
        let value = MachineTerm::Variable(Variable(994_101));
        let widened =
            MachineTerm::legacy_cast(MachineCastSpelling::UInt64From32, Box::new(value.clone()));
        assert!(bitvector_equal(&widened, &widened));
        assert!(!bitvector_equal(
            &widened,
            &MachineTerm::legacy_cast(
                MachineCastSpelling::UInt64From32,
                Box::new(MachineTerm::Variable(Variable(994_102)))
            )
        ));
        assert!(!bitvector_equal(
            &widened,
            &MachineTerm::legacy_cast(
                MachineCastSpelling::Int64FromUInt32,
                Box::new(value.clone())
            )
        ));
        assert!(!bitvector_equal(&widened, &value));
        let mut deep = value;
        for _ in 0..MAX_TERM_PAYLOAD {
            deep = MachineTerm::legacy_cast(MachineCastSpelling::UInt64From32, Box::new(deep));
        }
        assert!(!bitvector_equal(&deep, &deep));
    }
}

#[cfg(test)]
mod normalization_scaling_tests {
    include!("../../scaling_tests/kernel/proof/arithmetic_special/normalization.rs");
}
