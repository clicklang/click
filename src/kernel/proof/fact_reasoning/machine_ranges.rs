//! Range and value checks for explicitly unfolded machine expressions.
//! Unknown guards contribute both arms. Opaque operands never consult the
//! proof context, and the walk refuses when it uses its local allowance.

use crate::kernel::{
    BooleanOperandView, CompareRelation, IntegerComparisonOperator, IntegerTerm, KernelTerm,
    KernelTermNode, MachineBinaryOp, MachineIntegerConstant, MachineIntegerType,
    MachineOperandView, OldConditionTerm, OldMachineTerm,
};
use num_traits::ToPrimitive;

#[derive(Clone, Copy)]
struct Range {
    min: i128,
    max: i128,
}

impl Range {
    fn exact(value: i128) -> Self {
        Self {
            min: value,
            max: value,
        }
    }

    fn union(self, other: Self) -> Self {
        Self {
            min: self.min.min(other.min),
            max: self.max.max(other.max),
        }
    }

    fn fits(self, ty: MachineIntegerType) -> Option<Self> {
        let format = ty.format();
        MachineIntegerConstant::from_signed(format, self.min)?;
        MachineIntegerConstant::from_signed(format, self.max)?;
        Some(self)
    }

    fn compare(self, relation: CompareRelation, other: Self) -> Option<bool> {
        use CompareRelation::*;
        match relation {
            GreaterThan => other.compare(LessThan, self),
            GreaterEqual => other.compare(LessEqual, self),
            LessThan if self.max < other.min => Some(true),
            LessThan if self.min >= other.max => Some(false),
            LessEqual if self.max <= other.min => Some(true),
            LessEqual if self.min > other.max => Some(false),
            Equal if self.max < other.min || other.max < self.min => Some(false),
            Equal if self.min == self.max && self.min == other.min && other.min == other.max => {
                Some(true)
            }
            _ => None,
        }
    }
}

// Bound the stack and visits even when a shallow shared DAG repeats the
// same subexpression many times. The allowance covers the written decimal
// power/length tables, including the two copies in an unfolded padding bound.
const MAX_VISITS: usize = 512;
const MAX_DEPTH: usize = 64;

pub(super) fn comparison_value(condition: &OldConditionTerm) -> Option<bool> {
    Check { left: MAX_VISITS }.condition(condition, MAX_DEPTH)
}

struct Check {
    left: usize,
}

impl Check {
    fn condition(&mut self, condition: &OldConditionTerm, depth: usize) -> Option<bool> {
        use CompareRelation::*;
        let (relation, left, right, negated) = match condition {
            OldConditionTerm::Constant(value) => return Some(*value),
            OldConditionTerm::Compare {
                format,
                relation,
                left,
                right,
            } => {
                return self.machine_comparison(
                    *format,
                    *relation,
                    [left.as_ref(), right.as_ref()].map(MachineOperandView::Old),
                    depth,
                );
            }
            OldConditionTerm::IntegerEqual(left, right) => (Equal, left, right, false),
            OldConditionTerm::IntegerNotEqual(left, right) => (Equal, left, right, true),
            OldConditionTerm::IntegerLessThan(left, right) => (LessThan, left, right, false),
            OldConditionTerm::IntegerLessEqual(left, right) => (LessEqual, left, right, false),
            OldConditionTerm::IntegerGreaterThan(left, right) => (GreaterThan, left, right, false),
            OldConditionTerm::IntegerGreaterEqual(left, right) => {
                (GreaterEqual, left, right, false)
            }
            _ => return None,
        };
        let left = self.integer(left.as_ref(), depth)?;
        let right = self.integer(right.as_ref(), depth)?;
        left.compare(relation, right).map(|value| value != negated)
    }

    fn integer(&mut self, value: &IntegerTerm, depth: usize) -> Option<Range> {
        match value {
            IntegerTerm::Constant(value) if value.bits() <= 128 => {
                Some(Range::exact(value.to_i128()?))
            }
            IntegerTerm::Machine(value) => self.word(value.ty(), value.operand_view(), depth),
            _ => None,
        }
    }

    fn shared_integer(&mut self, value: &KernelTerm, depth: usize) -> Option<Range> {
        match value.node() {
            KernelTermNode::IntegerLiteral(value) if value.bits() <= 128 => {
                Some(Range::exact(value.to_i128()?))
            }
            KernelTermNode::MachineObservation { format, operand } => {
                self.word(*format, MachineOperandView::Shared(operand), depth)
            }
            _ => None,
        }
    }

    fn machine_comparison(
        &mut self,
        ty: MachineIntegerType,
        relation: CompareRelation,
        [left, right]: [MachineOperandView<'_>; 2],
        depth: usize,
    ) -> Option<bool> {
        let left = self.word(ty, left, depth)?;
        let right = self.word(ty, right, depth)?;
        left.compare(relation, right)
    }

    fn guard(&mut self, guard: BooleanOperandView<'_>, depth: usize) -> Option<bool> {
        if let Some((ty, relation, operands)) = guard.comparison() {
            return self.machine_comparison(ty, relation, operands, depth);
        }
        if let BooleanOperandView::Shared(root) = guard {
            match root.node() {
                KernelTermNode::BoolLiteral(value) => return Some(*value),
                KernelTermNode::IntegerCompare {
                    operator,
                    arguments: [left, right],
                } => {
                    use IntegerComparisonOperator as Op;
                    let relation = match operator {
                        Op::LessThan => CompareRelation::LessThan,
                        Op::LessEqual => CompareRelation::LessEqual,
                        Op::GreaterThan => CompareRelation::GreaterThan,
                        Op::GreaterEqual => CompareRelation::GreaterEqual,
                        Op::Equal | Op::NotEqual => CompareRelation::Equal,
                    };
                    let left = self.shared_integer(left, depth)?;
                    let right = self.shared_integer(right, depth)?;
                    return left
                        .compare(relation, right)
                        .map(|value| value != (*operator == Op::NotEqual));
                }
                _ => {}
            }
        }
        self.condition(guard.native_leaf()?, depth)
    }

    fn word(
        &mut self,
        ty: MachineIntegerType,
        value: MachineOperandView<'_>,
        depth: usize,
    ) -> Option<Range> {
        let depth = depth.checked_sub(1)?;
        self.left = self.left.checked_sub(1)?;
        if ty.format().bits() > 64 || crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        if let Some(literal) = value.literal() {
            let OldMachineTerm::Constant { format, bits } = literal else {
                return None;
            };
            if format.format().bits() != ty.format().bits() {
                return None;
            }
            let value = MachineIntegerConstant::from_term_bits(ty.format(), bits).to_i128()?;
            return Some(Range::exact(value));
        }
        if let Some((guard, [yes, no])) = value.conditional_view() {
            return match self.guard(guard, depth) {
                Some(true) => self.word(ty, yes, depth),
                Some(false) => self.word(ty, no, depth),
                None => Some(self.word(ty, yes, depth)?.union(self.word(ty, no, depth)?)),
            };
        }
        if let Some((_, source, destination, operand)) = value.cast() {
            let range = self.word(source, operand, depth)?.fits(destination)?;
            return Self::read_at(ty, destination, range);
        }
        let (format, op, [a, b]) = value.binary()?;
        if format.format().bits() != ty.format().bits() {
            return None;
        }
        use MachineBinaryOp::*;
        if op == BitwiseAnd && !format.format().is_signed() {
            // A literal mask bounds all possible inputs without reading the
            // masked operand. The parent operation must still fit its format.
            let mask = [a, b]
                .into_iter()
                .find_map(|operand| format.constant_from_term(&operand.literal()?)?.to_i128())?;
            return Self::read_at(ty, format, Range { min: 0, max: mask });
        }
        if !matches!(op, Add | Subtract | Divide | Remainder) {
            return None;
        }
        let a = self.word(format, a, depth)?;
        let b = self.word(format, b, depth)?;
        let range = match op {
            Add => Range {
                min: a.min + b.min,
                max: a.max + b.max,
            }
            .fits(format)?,
            Subtract => Range {
                min: a.min - b.max,
                max: a.max - b.min,
            }
            .fits(format)?,
            Divide | Remainder if a.min == a.max && b.min == b.max => {
                let numerator = MachineIntegerConstant::from_signed(format.format(), a.min)?;
                let divisor = MachineIntegerConstant::from_signed(format.format(), b.min)?;
                let (quotient, remainder) = numerator.truncating_div_rem(divisor).ok()?;
                let result = if op == Divide { quotient } else { remainder };
                Range::exact(result.to_i128()?)
            }
            _ => return None,
        };
        Self::read_at(ty, format, range)
    }

    /// A comparison can read either sign of an equal-width word. Reinterpret
    /// both endpoints only when the range does not cross the sign boundary.
    fn read_at(ty: MachineIntegerType, format: MachineIntegerType, range: Range) -> Option<Range> {
        if format == ty {
            return Some(range);
        }
        if format.format().bits() != ty.format().bits() {
            return None;
        }
        let read = |value| {
            let bits = MachineIntegerConstant::from_signed(format.format(), value)?.bits();
            MachineIntegerConstant::from_term_bits(ty.format(), bits).to_i128()
        };
        let min = read(range.min)?;
        let max = read(range.max)?;
        (max - min == range.max - range.min).then_some(Range { min, max })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn masked_unsigned_ranges_skip_the_masked_operand() {
        use MachineBinaryOp as Op;
        use MachineIntegerType as Ty;

        let ty = Ty::UInt32;
        let literal = OldMachineTerm::constant;
        let binary = |op, left, right| OldMachineTerm::Binary {
            format: ty,
            op,
            left: Box::new(left),
            right: Box::new(right),
        };
        let samples = [4, 16, 64].map(|size| {
            let mut input = OldMachineTerm::var(crate::kernel::Variable(996000));
            for _ in 0..size {
                input = binary(Op::Add, input, literal(1));
            }
            let equality = |mask, offset| OldConditionTerm::Compare {
                format: ty,
                relation: CompareRelation::Equal,
                left: Box::new(binary(
                    Op::Add,
                    binary(Op::BitwiseAnd, input.clone(), literal(mask)),
                    literal(offset),
                )),
                right: Box::new(literal(0)),
            };
            let goal = equality(7, 1);
            let wrapped = equality(1 << 31, 1 << 31);
            let (answer, work) =
                crate::instrumentation::measure_deterministic_work(|| comparison_value(&goal));
            assert_eq!(answer, Some(false));
            assert_eq!(comparison_value(&wrapped), None);
            work
        });
        assert_eq!(samples, [samples[0]; 3]);
    }

    #[test]
    fn unfolded_machine_ranges_refuse_wrapping_bounds_and_invalid_division() {
        use MachineBinaryOp as Op;
        use MachineIntegerType as Ty;
        let word = OldMachineTerm::uint64_constant;
        let signed = OldMachineTerm::int64_constant;
        for (format, op, left, right, bound) in [
            (Ty::UInt64, Op::Add, word(u64::MAX), word(1), word(1)),
            (Ty::UInt64, Op::Divide, word(12), word(0), word(1)),
            (
                Ty::Int64,
                Op::Remainder,
                signed(i64::MIN),
                signed(-1),
                signed(0),
            ),
        ] {
            let condition = OldConditionTerm::Compare {
                format,
                relation: CompareRelation::GreaterEqual,
                left: Box::new(OldMachineTerm::Binary {
                    format,
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                }),
                right: Box::new(bound),
            };
            assert_eq!(comparison_value(&condition), None, "{condition:?}");
        }
    }
}
