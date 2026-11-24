//! Fact identity of a machine comparison, read without exporting operands.
//! Native narrow comparisons and their promoted spellings share this reading;
//! stored terms and the comparison's written direction remain unchanged.
use crate::kernel::{
    CompareRelation, ConditionTerm, MachineCastSpelling as Encoding, MachineIntegerType,
    MachineOperandView as View,
};
use crate::kernel::{constant_u32, int32_constant, uint32_constant};

#[derive(Clone, Copy)]
pub(crate) enum FactOperand<'a> {
    Term(View<'a>),
    Value(i128),
}
pub(crate) fn fact_operand_identity<'a>(
    format: MachineIntegerType,
    relation: CompareRelation,
    [mut left, mut right]: [View<'a>; 2],
) -> (MachineIntegerType, [FactOperand<'a>; 2]) {
    let format = ConditionTerm::fact_format(format, relation);
    if relation == CompareRelation::Equal && format.format().bits() == 32 {
        let peel = |term: View<'a>| match term.cast() {
            Some((Encoding::Generic, source, destination, operand))
                if crate::kernel::is_sign_cast32(source, destination) =>
            {
                operand
            }
            _ => term,
        };
        left = peel(left);
        right = peel(right);
    }
    let narrow_value = |term: View<'a>| match term
        .literal()
        .and_then(|literal| literal.as_machine_constant())
    {
        Some(c) if c.format() == format.format() => c
            .to_i128()
            .map(FactOperand::Value)
            .unwrap_or(FactOperand::Term(term)),
        _ => FactOperand::Term(term),
    };
    if format.format().bits() < 32 {
        return (format, [narrow_value(left), narrow_value(right)]);
    }
    let widening = |term: View<'a>| match term.cast() {
        Some((Encoding::Generic, source, destination, operand))
            if crate::kernel::is_narrow_widening32(source, destination) =>
        {
            Some((source, operand))
        }
        _ => None,
    };
    if format == MachineIntegerType::Int32
        && let Some((source, _)) = widening(left).or_else(|| widening(right))
    {
        let bits = source.format().bits();
        let (low, high) = if source.format().is_signed() {
            (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
        } else {
            (0, (1i128 << bits) - 1)
        };
        let side = |term: View<'a>| -> Option<FactOperand<'a>> {
            let value = match term.literal() {
                Some(int32_constant!(v)) => Some(i128::from(constant_u32(v) as i32)),
                Some(uint32_constant!(v)) if relation == CompareRelation::Equal => {
                    Some(i128::from(constant_u32(v) as i32))
                }
                _ => None,
            };
            if let Some(value) = value {
                return (low <= value && value <= high).then_some(FactOperand::Value(value));
            }
            widening(term)
                .filter(|(found, _)| *found == source)
                .map(|(_, operand)| FactOperand::Term(operand))
        };
        if let (Some(left), Some(right)) = (side(left), side(right)) {
            return (source, [left, right]);
        }
    }
    let side = |term: View<'a>| {
        // K6: either 32-bit literal spelling denotes the same word in an
        // equality. Match ComparisonSide's signed identity value without
        // converting or exporting the surrounding operand.
        if relation == CompareRelation::Equal
            && format.format().bits() == 32
            && let Some(bits) = term.word32_constant()
        {
            FactOperand::Value(i128::from(bits as i32))
        } else {
            FactOperand::Term(term)
        }
    };
    (format, [side(left), side(right)])
}
