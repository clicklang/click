//! Preserve the native bitwise constructors' exact, fact-independent spelling.
use super::*;
use crate::kernel::{MachineUnaryOp, machine_operand_syntax_cmp};

fn constant(format: MachineIntegerType, bits: u64) -> KernelTerm {
    let value = if format.format().bits() == 32 {
        MachineTerm::constant(bits as u32).in_format32(format)
    } else if format.format().is_signed() {
        MachineTerm::int64_constant(bits as i64)
    } else {
        MachineTerm::uint64_constant(bits)
    };
    KernelTerm::retained_native_machine_operand(format, &value)
}
fn bits(value: &KernelTerm) -> Option<u64> {
    let KernelType::Program(ty) = value.ty() else {
        return None;
    };
    let format = MachineIntegerType::from_c_type(*ty)?;
    let view = MachineOperandView::Shared(value);
    if format.format().bits() == 32 {
        view.literal()?.constant32().map(u64::from)
    } else if format.format().is_signed() {
        view.int64_constant().map(|n| n as u64)
    } else {
        view.uint64_constant()
    }
}

fn same(a: &KernelTerm, b: &KernelTerm) -> bool {
    machine_operand_syntax_cmp(MachineOperandView::Shared(a), MachineOperandView::Shared(b)).is_eq()
}
fn node(
    format: MachineIntegerType,
    op: MachineBinaryOp,
    left: KernelTerm,
    right: KernelTerm,
) -> KernelTerm {
    KernelTerm::machine_binary_shared(format, op, [left, right])
}

pub(super) fn apply(
    op: MachineBinaryOp,
    left: &SpecValue,
    right: &SpecValue,
) -> Option<PreparedExpression> {
    let (a, left) = left.machine()?;
    let (b, right) = right.machine()?;
    let format = crate::kernel::machine_integer::conversion::usual_arithmetic_format(a, b)?;
    let left = promote(a, left, format)?;
    let right = promote(b, right, format)?;
    Some(PreparedExpression {
        value: binary(format, op, left, right),
        obligations: Vec::new(),
    })
}

fn promote(
    source: MachineIntegerType,
    value: MachineOperandView<'_>,
    target: MachineIntegerType,
) -> Option<KernelTerm> {
    let root = retained_operand(source, value);
    if source == target {
        Some(root)
    } else {
        cast(&root.into(), target.c_type())
    }
}

fn binary(
    format: MachineIntegerType,
    op: MachineBinaryOp,
    left: KernelTerm,
    right: KernelTerm,
) -> KernelTerm {
    use MachineBinaryOp as O;
    use MachineIntegerType as T;
    if format.format().bits() == 32 && op == O::BitwiseXor {
        return xor32(format, left, right);
    }
    if format == T::UInt64 && op == O::BitwiseAnd {
        return and64(left, right);
    }
    if format.format().bits() == 32 {
        let (a, b) = (bits(&left), bits(&right));
        match op {
            O::BitwiseAnd => {
                if b == Some(u64::from(u32::MAX)) {
                    return left;
                }
                if a == Some(u64::from(u32::MAX)) {
                    return right;
                }
                if a == Some(0) || b == Some(0) {
                    return constant(format, 0);
                }
            }
            O::BitwiseOr => {
                if b == Some(0) {
                    return left;
                }
                if a == Some(0) {
                    return right;
                }
                if a == Some(u64::from(u32::MAX)) || b == Some(u64::from(u32::MAX)) {
                    return constant(format, u64::from(u32::MAX));
                }
            }
            _ => unreachable!(),
        }
        if same(&left, &right) {
            return left;
        }
    } else if format == T::UInt64 && op == O::BitwiseOr {
        if let Some((T::UInt64, O::BitwiseAnd, [a, b])) = MachineOperandView::Shared(&left).binary()
            && let Some(mask) = a.uint64_constant().or_else(|| b.uint64_constant())
            && let Some(value) = bits(&right)
            && mask & !value == 0
        {
            return constant(format, value);
        }
        if bits(&left) == Some(0) {
            return right;
        }
        if bits(&right) == Some(0) {
            return left;
        }
    }
    if let (Some(a), Some(b)) = (bits(&left), bits(&right)) {
        return constant(
            format,
            match op {
                O::BitwiseAnd => a & b,
                O::BitwiseOr => a | b,
                O::BitwiseXor => a ^ b,
                _ => unreachable!(),
            },
        );
    }
    node(format, op, left, right)
}

fn and64(left: KernelTerm, right: KernelTerm) -> KernelTerm {
    use MachineBinaryOp as O;
    use MachineIntegerType as T;
    let Some(mut mask) = bits(&right) else {
        return if bits(&left) == Some(0) {
            constant(T::UInt64, 0)
        } else {
            node(T::UInt64, O::BitwiseAnd, left, right)
        };
    };
    let mut current = MachineOperandView::Shared(&left);
    let mut retained_mask = right;
    let literal = |value: MachineOperandView<'_>| value.uint64_constant();
    let mut ors = Vec::new();
    let result = loop {
        crate::instrumentation::record_deterministic_work(1);
        if let Some((T::UInt64, operator, [a, b])) = current.binary() {
            let selected = match (literal(a), literal(b)) {
                (None, Some(n)) => Some((a, n)),
                (Some(n), None) => Some((b, n)),
                _ => None,
            };
            if let Some((other, inner)) = selected {
                if operator == O::BitwiseAnd {
                    current = other;
                    mask &= inner;
                    retained_mask = constant(T::UInt64, mask);
                    continue;
                }
                if mask != 0 && operator == O::BitwiseOr {
                    ors.push(inner & mask);
                    retained_mask = constant(T::UInt64, mask);
                    current = other;
                    continue;
                }
            }
        }
        if mask == 0 {
            break constant(T::UInt64, 0);
        }
        if let Some(value) = literal(current) {
            break constant(T::UInt64, value & mask);
        }
        break node(
            T::UInt64,
            O::BitwiseAnd,
            retained_operand(T::UInt64, current),
            retained_mask,
        );
    };
    ors.into_iter().rev().fold(result, |value, n| {
        binary(T::UInt64, O::BitwiseOr, value, constant(T::UInt64, n))
    })
}

fn xor32(format: MachineIntegerType, left: KernelTerm, right: KernelTerm) -> KernelTerm {
    let mut pending = vec![
        MachineOperandView::Shared(&right),
        MachineOperandView::Shared(&left),
    ];
    let mut terms = Vec::new();
    let mut folded = 0;
    while let Some(value) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(n) = value.literal().and_then(|value| value.constant32()) {
            folded ^= u64::from(n);
        } else if let Some((found, MachineBinaryOp::BitwiseXor, [a, b])) = value.binary()
            && found == format
        {
            pending.push(b);
            pending.push(a);
        } else {
            terms.push(retained_operand(format, value));
        }
    }
    terms.sort_by(|a, b| {
        machine_operand_syntax_cmp(MachineOperandView::Shared(a), MachineOperandView::Shared(b))
    });
    let mut normalized: Vec<KernelTerm> = Vec::new();
    let mut index = 0;
    while index < terms.len() {
        let mut end = index + 1;
        while end < terms.len() && same(&terms[index], &terms[end]) {
            end += 1;
        }
        if (end - index) % 2 == 1 {
            normalized.push(terms[index].clone());
        }
        index = end;
    }
    if folded != 0 {
        normalized.push(constant(format, folded));
        normalized.sort_by(|a, b| {
            machine_operand_syntax_cmp(MachineOperandView::Shared(a), MachineOperandView::Shared(b))
        });
    }
    normalized
        .into_iter()
        .reduce(|a, b| node(format, MachineBinaryOp::BitwiseXor, a, b))
        .unwrap_or_else(|| constant(format, 0))
}

pub(super) fn not(value: &SpecValue) -> Option<KernelTerm> {
    let (source, operand) = value.machine()?;
    if source.format().bits() > 64 {
        return None;
    }
    let format = if source.format().bits() < 32 {
        MachineIntegerType::Int32
    } else {
        source
    };
    let operand = promote(source, operand, format)?;
    if let Some(value) = bits(&operand) {
        return Some(constant(format, !value));
    }
    if format.format().bits() == 32
        && let Some((found, MachineUnaryOp::BitwiseNot, inner)) =
            MachineOperandView::Shared(&operand).unary()
        && found == format
    {
        return Some(retained_operand(format, inner));
    }
    Some(KernelTerm::machine_unary_shared(
        format,
        MachineUnaryOp::BitwiseNot,
        operand,
    ))
}

/// A selected tag-clearing equality is a side fact, never a result rewrite.
/// Both lookups use exact operand keys in existing indexes.
pub(super) fn tag_equation(
    value: &KernelTerm,
    assumptions: &PureFactContext,
) -> Option<ConditionTerm> {
    use MachineBinaryOp as O;
    use MachineIntegerType as T;
    let view = MachineOperandView::Shared(value);
    let (T::UInt64, O::BitwiseAnd, [inner, mask]) = view.binary()? else {
        return None;
    };
    let mask = mask.uint64_constant()?;
    let (T::UInt64, op @ (O::BitwiseOr | O::Add), [a, b]) = inner.binary()? else {
        return None;
    };
    let compare = |left: &KernelTerm, right: &KernelTerm| {
        crate::kernel::machine_integer::comparison::condition_for_operand_views(
            // Native uint64_equal uses the sign-independent Int64 word carrier.
            T::Int64,
            CompareRelation::Equal,
            [
                MachineOperandView::Shared(left),
                MachineOperandView::Shared(right),
            ],
        )
    };
    for (word, tag) in [(a, b), (b, a)] {
        let Some(bound) = crate::kernel::eval::pointer_tags::tag_bound_citing(
            tag,
            assumptions,
            &mut crate::kernel::eval::pointer_tags::UsedFacts::new(),
        ) else {
            continue;
        };
        if bound & mask != 0 {
            continue;
        }
        let word = retained_operand(T::UInt64, word);
        if op == O::Add {
            let Some(alignment) = bound
                .checked_add(1)
                .and_then(u64::checked_next_power_of_two)
            else {
                continue;
            };
            let low = and64(word.clone(), constant(T::UInt64, alignment - 1));
            let clear = compare(&low, &constant(T::UInt64, 0));
            if clear != ConditionTerm::Constant(true)
                && assumptions
                    .selected_comparison_source(&clear, true)
                    .is_none()
            {
                continue;
            }
        }
        let masked = and64(word, constant(T::UInt64, mask));
        return Some(compare(value, &masked));
    }
    None
}
