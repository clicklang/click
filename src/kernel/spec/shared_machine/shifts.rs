//! Retained C and Rust shifts share count handling and preserve language-specific result rules.
use super::*;

fn convert(
    source: MachineIntegerType,
    root: KernelTerm,
    target: MachineIntegerType,
) -> Option<KernelTerm> {
    if source == target {
        Some(root)
    } else {
        cast(&root.into(), target.c_type())
    }
}

pub(super) fn apply(
    op: MachineBinaryOp,
    left: (MachineIntegerType, MachineOperandView<'_>),
    right: (MachineIntegerType, MachineOperandView<'_>),
) -> Option<PreparedExpression> {
    with_count_width(op, left, right, None)
}

pub(super) fn rust(
    op: MachineBinaryOp,
    left: &SpecValue,
    right: &SpecValue,
) -> Option<PreparedExpression> {
    let (format, view) = left.machine()?;
    let bits = format.format().bits();
    if bits > 64 {
        return None;
    }
    let operand_format = if op == MachineBinaryOp::ShiftLeft {
        if bits == 64 {
            MachineIntegerType::UInt64
        } else {
            MachineIntegerType::UInt32
        }
    } else {
        format
    };
    let operand = convert(format, retained_operand(format, view), operand_format)?;
    let mut result = with_count_width(
        op,
        (operand_format, MachineOperandView::Shared(&operand)),
        right.machine()?,
        Some(bits),
    )?;
    let KernelType::C(result_type) = result.value.ty() else {
        unreachable!()
    };
    let result_format = MachineIntegerType::from_c_type(*result_type)?;
    result.value = convert(result_format, result.value, format)?;
    Some(result)
}

fn with_count_width(
    op: MachineBinaryOp,
    (left_format, left): (MachineIntegerType, MachineOperandView<'_>),
    (right_format, right): (MachineIntegerType, MachineOperandView<'_>),
    count_width: Option<u32>,
) -> Option<PreparedExpression> {
    use crate::kernel::machine_integer::conversion::usual_arithmetic_format;
    let format = usual_arithmetic_format(left_format, left_format)?;
    let mut count_format = usual_arithmetic_format(right_format, right_format)?;
    let left = convert(left_format, retained_operand(left_format, left), format)?;
    let mut count = convert(
        right_format,
        retained_operand(right_format, right),
        count_format,
    )?;
    let wide = format.format().bits() == 64;
    if wide && count_format.format().bits() == 32 {
        let target = if count_format.format().is_signed() {
            MachineIntegerType::Int64
        } else {
            MachineIntegerType::UInt64
        };
        count = convert(count_format, count, target)?;
        count_format = target;
    }
    let compare = |format, root: &KernelTerm, relation, n: u32| {
        let bound =
            crate::kernel::machine_integer::range::constant_word(format, &n.into()).unwrap();
        crate::kernel::machine_integer::comparison::condition_for_operand_views(
            format,
            relation,
            [
                MachineOperandView::Shared(root),
                MachineOperandView::Legacy(&bound),
            ],
        )
    };
    let mut domain = Vec::new();
    let mut require_false = |condition| {
        if PureFactContext::decide_intrinsically(&condition) != Some(false) {
            domain.push(Proposition::ConditionIs(condition, false));
        }
    };
    if count_format.format().is_signed() {
        require_false(compare(count_format, &count, CompareRelation::LessThan, 0));
    }
    require_false(compare(
        count_format,
        &count,
        CompareRelation::GreaterEqual,
        count_width.unwrap_or(format.format().bits()),
    ));
    // Keep the wide count in its bounds; only the operation reads its low word.
    if !wide && count_format.format().bits() == 64 {
        count = convert(count_format, count, MachineIntegerType::UInt32)?;
    }
    if op == MachineBinaryOp::ShiftLeft && format.format().is_signed() {
        require_false(compare(format, &left, CompareRelation::LessThan, 0));
        domain.push(Proposition::ConditionIs(
            ConditionTerm::signed_shift_result_fits_views(
                format,
                MachineOperandView::Shared(&left),
                MachineOperandView::Shared(&count),
            ),
            true,
        ));
    }
    let obligations = Proposition::arithmetic_domain(domain)
        .map(|domain| {
            ProofObligation::evaluation_domain(domain).with_context("shift expression is defined")
        })
        .into_iter()
        .collect();
    Some(PreparedExpression {
        value: logical_binary(format, op, left, count),
        obligations,
    })
}
