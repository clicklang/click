//! Fact identity of a machine comparison, read without exporting operands.
//! Native narrow comparisons and their promoted spellings share this reading;
//! stored terms and the comparison's written direction remain unchanged.
use crate::kernel::{
    Bitvector32Term, CompareRelation, ConditionTerm, KernelMachineCastEncoding as Encoding,
    MachineIntegerType, MachineOperandView as View,
};

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
    let narrow_value = |term: View<'a>| match term.literal() {
        Some(Bitvector32Term::MachineIntegerConstant(c)) if c.format() == format.format() => c
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
                Some(Bitvector32Term::Constant(v)) => Some(i128::from(v as i32)),
                Some(Bitvector32Term::UInt32Constant(v)) if relation == CompareRelation::Equal => {
                    Some(i128::from(v as i32))
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
    (format, [FactOperand::Term(left), FactOperand::Term(right)])
}
