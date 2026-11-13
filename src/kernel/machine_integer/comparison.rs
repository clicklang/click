//! Exact comparison: `to_integer(a) R to_integer(b)` holds exactly when the
//! native comparison of `a` and `b` at their format does. `to_integer` is
//! injective and order-preserving on every format, so the two comparisons
//! have the same truth.

mod fact_identity;
pub(crate) use fact_identity::{FactOperand, fact_operand_identity};

use super::{Relation, identity, range, representation};
use crate::kernel::{
    ConditionTerm, IntegerTerm, MachineIntegerType, MachineTerm, Proposition, SharedIntegerTerm,
    SharedMachineIntegerTerm,
};

/// A written comparison for structural matching. Unlike checking views, this
/// preserves direction and performs no arithmetic cancellation or evaluation.
pub(crate) struct StructuralComparisonView<'a> {
    pub(crate) format: MachineIntegerType,
    pub(crate) relation: crate::kernel::CompareRelation,
    pub(crate) negated: bool,
    pub(crate) operands: [ComparisonOperand<'a>; 2],
}

pub(crate) fn structural_comparison_view(
    condition: &ConditionTerm,
) -> Option<StructuralComparisonView<'_>> {
    use crate::kernel::CompareRelation as R;
    if let ConditionTerm::Compare {
        format,
        relation,
        left,
        right,
    } = condition
    {
        return Some(StructuralComparisonView {
            format: *format,
            relation: *relation,
            negated: false,
            operands: [
                ComparisonOperand::Written(left),
                ComparisonOperand::Written(right),
            ],
        });
    }
    let (relation, negated) = match condition {
        ConditionTerm::IntegerEqual(..) => (R::Equal, false),
        ConditionTerm::IntegerNotEqual(..) => (R::Equal, true),
        ConditionTerm::IntegerLessThan(..) => (R::LessThan, false),
        ConditionTerm::IntegerLessEqual(..) => (R::LessEqual, false),
        ConditionTerm::IntegerGreaterThan(..) => (R::GreaterThan, false),
        ConditionTerm::IntegerGreaterEqual(..) => (R::GreaterEqual, false),
        _ => return None,
    };
    let mut view = comparison_view_at_format(condition, true)?;
    if matches!(relation, R::GreaterThan | R::GreaterEqual) {
        view.operands.swap(0, 1);
    }
    Some(StructuralComparisonView {
        format: view.format,
        relation,
        negated,
        operands: view.operands,
    })
}

/// An Integer comparison as `left REL right` with its truth folded in:
/// `>`/`>=` swap their operands, and a false comparison is negated.
fn integer_relation(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(Relation, &SharedIntegerTerm, &SharedIntegerTerm)> {
    let (relation, left, right) = match condition {
        ConditionTerm::IntegerLessThan(left, right) => (Relation::Less, left, right),
        ConditionTerm::IntegerLessEqual(left, right) => (Relation::LessEqual, left, right),
        ConditionTerm::IntegerGreaterThan(left, right) => (Relation::Less, right, left),
        ConditionTerm::IntegerGreaterEqual(left, right) => (Relation::LessEqual, right, left),
        ConditionTerm::IntegerEqual(left, right) => (Relation::Equal, left, right),
        ConditionTerm::IntegerNotEqual(left, right) => (Relation::NotEqual, left, right),
        _ => return None,
    };
    Some(match (relation, value) {
        (relation, true) => (relation, left, right),
        // not (l < r) is r <= l; not (l <= r) is r < l.
        (Relation::Less, false) => (Relation::LessEqual, right, left),
        (Relation::LessEqual, false) => (Relation::Less, right, left),
        (Relation::Equal, false) => (Relation::NotEqual, left, right),
        (Relation::NotEqual, false) => (Relation::Equal, left, right),
    })
}

/// The native machine comparison equivalent to the Integer comparison
/// `condition` with truth `value`, when both sides observe one machine
/// format exactly: `to_integer(x)` against `to_integer(y)` of the same
/// format, or against a constant that format represents. A constant outside
/// the format's range makes the Integer comparison decided by the range
/// alone; nothing is returned for it, nor for a format whose Integer
/// comparisons keep their Integer spelling
/// (`representation::spells_comparison_natively`).
pub(crate) fn native_comparison_of_integer_observation(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(ConditionTerm, bool)> {
    native_comparison_view(condition, value)?.boxed_condition()
}

/// Construct a checking comparison from two borrowed operands. Native inputs
/// and fixed-size atoms keep their written comparison; shared arithmetic stays
/// in exact observations. This never exports a shared arithmetic tree.
pub(crate) fn condition_for_operand_views(
    format: MachineIntegerType,
    relation: crate::kernel::CompareRelation,
    operands: [crate::kernel::MachineOperandView<'_>; 2],
) -> ConditionTerm {
    use crate::kernel::{CompareRelation as R, MachineOperandView as V};
    if format == MachineIntegerType::UInt32
        && let Some(bound) = operands[1].literal().and_then(|word| word.constant32())
    {
        let upper = operands[0].unsigned32_upper_bound();
        let result = match relation {
            R::LessThan if upper < bound => Some(true),
            R::LessEqual if upper <= bound => Some(true),
            R::GreaterThan if upper <= bound => Some(false),
            R::GreaterEqual if upper < bound => Some(false),
            _ => None,
        };
        if let Some(result) = result {
            return ConditionTerm::Constant(result);
        }
    }
    let atoms = operands.map(|operand| match operand {
        V::Shared(root) => root
            .machine_constant_reading()
            .map(|literal| literal.legacy_term())
            .or_else(|| operand.variable().copied().map(MachineTerm::Variable))
            .or_else(|| root.machine_read_leaf().cloned())
            .or_else(|| {
                // A signedness cast of one variable is still a fixed-size
                // atom. Keep the native guard spelling used by cited bounds;
                // never export a shared arithmetic operand here.
                let crate::kernel::KernelTermNode::MachineCast {
                    encoding: crate::kernel::MachineCastSpelling::Generic,
                    source,
                    destination,
                    operand,
                } = root.node()
                else {
                    return None;
                };
                if !crate::kernel::is_sign_cast32(*source, *destination) {
                    return None;
                }
                let crate::kernel::KernelTermNode::Variable(variable) = operand.node() else {
                    return None;
                };
                Some(MachineTerm::sign_cast32(
                    *source,
                    *destination,
                    MachineTerm::Variable(*variable),
                ))
            }),
        V::Legacy(_) => None,
    });
    let operands: [V<'_>; 2] = std::array::from_fn(|index| {
        atoms[index]
            .as_ref()
            .map(V::Legacy)
            .unwrap_or(operands[index])
    });
    if let [V::Legacy(left), V::Legacy(right)] = operands {
        return ConditionTerm::machine_compare(format, relation, left.clone(), right.clone());
    }
    let [left, right] = operands.map(|operand| {
        if let Some(literal) = operand.literal() {
            // Native wide equality uses an Int64 word comparison even when
            // its literals were written as UInt64. Retain the word's bits
            // while giving its Integer observation the comparison's sign.
            let literal = match &literal {
                MachineTerm::Constant { format: source, .. }
                    if source.format().bits() == format.format().bits() =>
                {
                    MachineTerm::machine_integer_cast(*source, format, literal)
                }
                _ => literal,
            };
            IntegerTerm::from_machine(format, literal).expect("typed comparison literal")
        } else {
            IntegerTerm::Machine(match operand {
                V::Legacy(value) => SharedMachineIntegerTerm::intern(format, value.clone()),
                V::Shared(root) => SharedMachineIntegerTerm::observe_shared(
                    format,
                    root.with_machine_observation_type(format),
                )
                .expect("typed comparison operand"),
            })
        }
    });
    match relation {
        R::Equal => ConditionTerm::integer_equal(left, right),
        R::LessThan => ConditionTerm::integer_less_than(left, right),
        R::LessEqual => ConditionTerm::integer_less_equal(left, right),
        R::GreaterThan => ConditionTerm::integer_greater_than(left, right),
        R::GreaterEqual => ConditionTerm::integer_greater_equal(left, right),
    }
}

/// Retain native arithmetic at an explicit checking boundary. This is a
/// syntax-only reading of the selected comparison, not a lowering policy.
pub(crate) fn retained_arithmetic_comparison(condition: &ConditionTerm) -> Option<ConditionTerm> {
    let ConditionTerm::Compare {
        format,
        relation,
        left,
        right,
    } = condition
    else {
        return None;
    };
    if !matches!(
        format,
        MachineIntegerType::Int32
            | MachineIntegerType::UInt32
            | MachineIntegerType::Int64
            | MachineIntegerType::UInt64
    ) {
        return None;
    }
    use crate::kernel::{KernelTerm, MachineBinaryOp as O, MachineOperandView as V};
    let operands = [V::Legacy(left), V::Legacy(right)];
    let roots = operands.map(|operand| {
        operand
            .binary()
            .filter(|(_, op, _)| {
                matches!(
                    op,
                    O::Add
                        | O::Subtract
                        | O::Multiply
                        | O::Divide
                        | O::Remainder
                        | O::ShiftLeft
                        | O::ShiftRight
                )
            })
            .map(|_| KernelTerm::retained_machine_operand(*format, operand))
    });
    if roots.iter().all(Option::is_none) {
        return None;
    }
    Some(condition_for_operand_views(
        *format,
        *relation,
        std::array::from_fn(|i| roots[i].as_ref().map(V::Shared).unwrap_or(operands[i])),
    ))
}

/// A comparison query retaining its original shared operand identities.
/// Boxed conditions are an explicit compatibility output for unmigrated callers.
#[derive(Clone)]
pub(crate) struct NativeComparisonView<'a> {
    pub(crate) format: MachineIntegerType,
    pub(crate) relation: Relation,
    pub(crate) operands: [ComparisonOperand<'a>; 2],
}

#[derive(Clone)]
pub(crate) enum ComparisonOperand<'a> {
    Observation(SharedMachineIntegerTerm),
    Constant(MachineTerm),
    Written(&'a MachineTerm),
}

impl ComparisonOperand<'_> {
    pub(crate) fn operand_view(&self) -> crate::kernel::MachineOperandView<'_> {
        match self {
            Self::Observation(machine) => machine.operand_view(),
            Self::Constant(value) => crate::kernel::MachineOperandView::Legacy(value),
            Self::Written(value) => crate::kernel::MachineOperandView::Legacy(value),
        }
    }

    pub(super) fn boxed_value(&self) -> &MachineTerm {
        match self {
            Self::Observation(machine) => machine.value(),
            Self::Constant(value) => value,
            Self::Written(value) => value,
        }
    }
}

impl NativeComparisonView<'_> {
    /// A shared reading of the existing 32-bit additive cancellation rule.
    /// Only the selected roots and at most four child identities are inspected.
    pub(crate) fn cancelled_equality(&self) -> Option<NativeComparisonView<'static>> {
        use crate::kernel::{KernelTermImport, MachineBinaryOp, MachineOperandView as V};
        if self.format.format().bits() != 32
            || !matches!(self.relation, Relation::Equal | Relation::NotEqual)
        {
            return None;
        }
        let [left, right] = self
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        fn sum(view: V<'_>) -> Option<(MachineIntegerType, MachineBinaryOp, [V<'_>; 2])> {
            view.binary().filter(|(format, operation, _)| {
                format.format().bits() == 32 && *operation == MachineBinaryOp::Add
            })
        }
        let same = |format, a: V<'_>, b: V<'_>| match (a, b) {
            (V::Shared(a), V::Shared(b)) => a == b,
            (V::Legacy(a), V::Legacy(b)) => a == b,
            (V::Shared(a), V::Legacy(b)) | (V::Legacy(b), V::Shared(a)) => {
                KernelTermImport::default()
                    .machine_arithmetic(format, b)
                    .as_ref()
                    == Some(a)
            }
        };
        let owned = |view: V<'_>| match view {
            V::Shared(_) => ComparisonOperand::Observation(view.retain(self.format)),
            V::Legacy(term) => ComparisonOperand::Constant(term.clone()),
        };
        let result = |a, b| NativeComparisonView {
            format: self.format,
            relation: self.relation,
            operands: [a, b],
        };
        if let (Some((lf, _, [a, b])), Some((rf, _, [c, d]))) = (sum(left), sum(right))
            && lf == rf
        {
            for ((kept, other), (matched, remainder)) in [
                ((a, b), (c, d)),
                ((a, b), (d, c)),
                ((b, a), (c, d)),
                ((b, a), (d, c)),
            ] {
                if same(lf, kept, matched) {
                    return Some(result(owned(other), owned(remainder)));
                }
            }
        }
        for (side, partner, reverse) in [(left, right, false), (right, left, true)] {
            if let Some((format, _, [a, b])) = sum(side) {
                for (kept, other) in [(a, b), (b, a)] {
                    if same(format, kept, partner) {
                        let zero =
                            ComparisonOperand::Constant(MachineTerm::constant_at32(format, 0));
                        return Some(if reverse {
                            result(zero, owned(other))
                        } else {
                            result(owned(other), zero)
                        });
                    }
                }
            }
        }
        None
    }

    pub(crate) fn cancelled_form(mut self) -> Self {
        while let Some(next) = self.cancelled_equality() {
            self = next;
        }
        self
    }

    /// The value-preserving 32-bit reading of a narrow comparison, retaining
    /// shared operands. Checking folds only the two cast roots.
    pub(crate) fn widened(&self) -> Option<NativeComparisonView<'static>> {
        if self.format.format().bits() >= 32 {
            return None;
        }
        let destination = MachineIntegerType::Int32;
        let operands = self
            .operands
            .each_ref()
            .map(|operand| match operand.operand_view() {
                crate::kernel::MachineOperandView::Shared(term) => ComparisonOperand::Observation(
                    SharedMachineIntegerTerm::from_shared(
                        destination,
                        term.checking_machine_cast(self.format, destination),
                    )
                    .expect("shared widening"),
                ),
                crate::kernel::MachineOperandView::Legacy(term) => ComparisonOperand::Constant(
                    super::conversion::convert_term(self.format, destination, term.clone()),
                ),
            });
        Some(NativeComparisonView {
            format: destination,
            relation: self.relation,
            operands,
        })
    }

    /// An exact Integer reading retaining the carrier's shared operands.
    /// This is a checking consequence; the original lowered term is untouched.
    pub(crate) fn integer_condition(&self) -> ConditionTerm {
        let [left, right] = self.operands.each_ref().map(|operand| match operand {
            ComparisonOperand::Observation(value) => IntegerTerm::Machine(value.clone()).into(),
            other => IntegerTerm::from_machine(self.format, other.boxed_value().clone())
                .expect("comparison carrier has its declared format")
                .into(),
        });
        match self.relation {
            Relation::Equal => ConditionTerm::IntegerEqual(left, right),
            Relation::NotEqual => ConditionTerm::IntegerNotEqual(left, right),
            Relation::Less => ConditionTerm::IntegerLessThan(left, right),
            Relation::LessEqual => ConditionTerm::IntegerLessEqual(left, right),
        }
    }

    /// Match the native comparison representation's polarity for exact
    /// quantified-body identity: disequality is a false equality.
    pub(crate) fn integer_proposition(&self) -> crate::kernel::Proposition {
        let condition = self.integer_condition();
        if let ConditionTerm::IntegerNotEqual(left, right) = condition {
            crate::kernel::Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), false)
        } else {
            crate::kernel::Proposition::ConditionIs(condition, true)
        }
    }

    /// A checking reading that retains arithmetic in the shared arena.
    /// Only fixed-size leaves and already-written native operands use Compare.
    pub(crate) fn retained_condition(&self) -> (ConditionTerm, bool) {
        use crate::kernel::CompareRelation as R;
        let relation = match self.relation {
            Relation::Equal | Relation::NotEqual => R::Equal,
            Relation::Less => R::LessThan,
            Relation::LessEqual => R::LessEqual,
        };
        (
            condition_for_operand_views(
                self.format,
                relation,
                self.operands
                    .each_ref()
                    .map(|operand| operand.operand_view()),
            ),
            self.relation != Relation::NotEqual,
        )
    }

    fn boxed_condition(&self) -> Option<(ConditionTerm, bool)> {
        representation::comparison(
            self.format,
            self.relation,
            self.operands[0].boxed_value().clone(),
            self.operands[1].boxed_value().clone(),
        )
    }
}

/// One view for written native comparisons and exact Integer observations.
/// Native operands are borrowed; Integer operands retain their shared handles.
pub(crate) fn comparison_view(
    condition: &ConditionTerm,
    value: bool,
) -> Option<NativeComparisonView<'_>> {
    use crate::kernel::CompareRelation as R;
    let ConditionTerm::Compare {
        format,
        relation,
        left,
        right,
    } = condition
    else {
        return native_comparison_view(condition, value).map(NativeComparisonView::cancelled_form);
    };
    let (relation, left, right) = match (relation, value) {
        (R::Equal, true) => (Relation::Equal, left, right),
        (R::Equal, false) => (Relation::NotEqual, left, right),
        (R::LessThan, true) | (R::GreaterEqual, false) => (Relation::Less, left, right),
        (R::LessEqual, true) | (R::GreaterThan, false) => (Relation::LessEqual, left, right),
        (R::GreaterThan, true) | (R::LessEqual, false) => (Relation::Less, right, left),
        (R::GreaterEqual, true) | (R::LessThan, false) => (Relation::LessEqual, right, left),
    };
    Some(NativeComparisonView {
        format: *format,
        relation,
        operands: [
            ComparisonOperand::Written(left),
            ComparisonOperand::Written(right),
        ],
    })
}

pub(crate) fn native_comparison_view(
    condition: &ConditionTerm,
    value: bool,
) -> Option<NativeComparisonView<'static>> {
    // Numeric evaluation belongs in the checking comparison form. Surface
    // lowering uses the structural reading below, retaining arithmetic.
    // An observation is read through its value relations (rule W):
    // `to_integer(d as int128) != 0` is `d != 0`.
    let operand = |term: &SharedIntegerTerm| -> Option<SharedIntegerTerm> {
        let read = term.value_read();
        if !std::ptr::eq(read, term.as_ref()) {
            return Some(read.clone().into());
        }
        if !term.is_literal_arithmetic() || term.as_const().is_some() {
            return Some(term.clone());
        }
        crate::kernel::proof::integer_arithmetic::literal_integer_value(term)
            .map(|value| IntegerTerm::constant(value).into())
    };
    let written = condition;
    let condition = match condition {
        ConditionTerm::IntegerLessThan(left, right) => {
            ConditionTerm::IntegerLessThan(operand(left)?, operand(right)?)
        }
        ConditionTerm::IntegerLessEqual(left, right) => {
            ConditionTerm::IntegerLessEqual(operand(left)?, operand(right)?)
        }
        ConditionTerm::IntegerGreaterThan(left, right) => {
            ConditionTerm::IntegerGreaterThan(operand(left)?, operand(right)?)
        }
        ConditionTerm::IntegerGreaterEqual(left, right) => {
            ConditionTerm::IntegerGreaterEqual(operand(left)?, operand(right)?)
        }
        ConditionTerm::IntegerEqual(left, right) => {
            ConditionTerm::IntegerEqual(operand(left)?, operand(right)?)
        }
        ConditionTerm::IntegerNotEqual(left, right) => {
            ConditionTerm::IntegerNotEqual(operand(left)?, operand(right)?)
        }
        _ => return None,
    };
    // Reading an exact extension can expose different operand formats (for
    // example int32 i beside int64 n). Keep the written common-format view
    // available to the order checker in that case. This selects two roots;
    // it neither exports a shared subtree nor consults facts.
    structural_native_comparison_view(&condition, value)
        .or_else(|| structural_native_comparison_view(written, value))
}

pub(crate) fn structural_native_comparison_of_integer_observation(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(ConditionTerm, bool)> {
    structural_native_comparison_view(condition, value)?.boxed_condition()
}

pub(crate) fn structural_native_comparison_view(
    condition: &ConditionTerm,
    value: bool,
) -> Option<NativeComparisonView<'static>> {
    // A 128-bit comparison has a native node, but the kernel's order
    // reasoning (the difference graph, interval bounds) works on its
    // Integer form, so an Integer comparison of 128-bit observations keeps
    // that spelling (`representation::spells_comparison_natively`).
    let spelled_natively = |side: &IntegerTerm| match side {
        IntegerTerm::Machine(machine) => representation::spells_comparison_natively(machine.ty()),
        _ => true,
    };
    if let ConditionTerm::IntegerLessThan(left, right)
    | ConditionTerm::IntegerLessEqual(left, right)
    | ConditionTerm::IntegerGreaterThan(left, right)
    | ConditionTerm::IntegerGreaterEqual(left, right)
    | ConditionTerm::IntegerEqual(left, right)
    | ConditionTerm::IntegerNotEqual(left, right) = condition
        && !(spelled_natively(left) && spelled_natively(right))
    {
        return None;
    }
    comparison_view_at_format(condition, value)
}

/// Whether `proposition` is an Integer comparison of exact observations of
/// a 128-bit format (or of one and a constant it represents): the reading
/// of that format's native comparison, which keeps its Integer spelling
/// ([`representation::spells_comparison_natively`]). One match on the root
/// and the two sides.
pub(crate) fn reads_wide_integer_observations(proposition: &Proposition) -> bool {
    let Proposition::ConditionIs(condition, value) = proposition else {
        return false;
    };
    comparison_view_at_format(condition, *value)
        .is_some_and(|view| !representation::spells_comparison_natively(view.format))
}

/// [`native_comparison_of_integer_observation`] at every format, whatever
/// its spelling: the forward map the converse reading checks against.
fn native_comparison_at_format(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(ConditionTerm, bool)> {
    comparison_view_at_format(condition, value)?.boxed_condition()
}

fn comparison_view_at_format(
    condition: &ConditionTerm,
    value: bool,
) -> Option<NativeComparisonView<'static>> {
    let (relation, left, right) = integer_relation(condition, value)?;
    let ty = match (&**left, &**right) {
        (IntegerTerm::Machine(left), IntegerTerm::Machine(right)) if left.ty() == right.ty() => {
            left.ty()
        }
        (IntegerTerm::Machine(machine), IntegerTerm::Constant(_))
        | (IntegerTerm::Constant(_), IntegerTerm::Machine(machine)) => machine.ty(),
        _ => return None,
    };
    // An 8- or 16-bit observation is a native value of its format, compared
    // natively at it; a constant is that format's constant. An observation
    // whose operand is a word of another width (the byte of a 32-bit sum)
    // has no native comparison: its root width, read in O(1), decides.
    let narrow = ty.format().bits() < 32;
    let carrier = |side: &IntegerTerm| -> Option<ComparisonOperand<'static>> {
        match side {
            IntegerTerm::Machine(machine)
                if narrow
                    && machine.operand_view().root_width().is_some_and(|width| {
                        width != crate::kernel::CarrierWidth::of_machine_type(ty)
                    }) =>
            {
                None
            }
            IntegerTerm::Machine(machine) => Some(ComparisonOperand::Observation(machine.clone())),
            IntegerTerm::Constant(constant) => Some(ComparisonOperand::Constant(
                range::constant_word(ty, constant)?,
            )),
            _ => None,
        }
    };
    let left = carrier(left)?;
    let right = carrier(right)?;
    Some(NativeComparisonView {
        format: ty,
        relation,
        operands: [left, right],
    })
}

/// The native comparison an Integer comparison holds exactly when, read
/// through in-range machine operations: each side that is the exact value
/// of a machine `+` or `-` of observations of one format is replaced by
/// that operation's observation
/// (`identity::machine_operation_of_integer_value`), and the result is read
/// as [`native_comparison_of_integer_observation`] reads it.
/// `to_integer(a) <= 4294967295 - to_integer(b)` on `uint32` reads as
/// `a <= 4294967295u32 - b`. The returned bounds are what each replaced
/// operation needs to equal its exact value; the reading holds only with
/// them. A comparison with no operation side, or whose native form folds
/// to a constant, has no such reading. At most one candidate format per
/// observation the two sides name is tried; nothing else is visited.
#[cfg(test)]
pub(crate) fn native_comparison_through_integer_operations(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(
    ConditionTerm,
    bool,
    Vec<identity::IntegerOperationRangeBound>,
)> {
    let (view, bounds) = comparison_view_through_integer_operations(condition, value)?;
    match view.boxed_condition()? {
        (ConditionTerm::Constant(_), _) => None,
        (native, truth) => Some((native, truth, bounds)),
    }
}

/// The operation bridge before any legacy condition is exported. Range
/// premises are explicit outputs, so callers retain the same authority checks.
pub(crate) fn comparison_view_through_integer_operations(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(
    NativeComparisonView<'static>,
    Vec<identity::IntegerOperationRangeBound>,
)> {
    let (left, right) = match condition {
        ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right)
        | ConditionTerm::IntegerEqual(left, right)
        | ConditionTerm::IntegerNotEqual(left, right) => {
            // Each side is read through its observations' value relations
            // (rule W), so `to_integer(x as uint32) + 1` is an operation on
            // `x`'s own format. Both readings are cached on the sides.
            (&**left.read_through_ref(), &**right.read_through_ref())
        }
        _ => return None,
    };
    let operation =
        |side: &IntegerTerm| matches!(side, IntegerTerm::Add(..) | IntegerTerm::Subtract(..));
    if !operation(left) && !operation(right) {
        return None;
    }
    // The machine formats the sides observe, directly or as operands.
    let mut types = Vec::new();
    for side in [left, right] {
        let operands = match side {
            IntegerTerm::Add(a, b) | IntegerTerm::Subtract(a, b) => vec![&**a, &**b],
            other => vec![other],
        };
        for operand in operands {
            if let IntegerTerm::Machine(machine) = operand
                && !types.contains(&machine.ty())
            {
                types.push(machine.ty());
            }
        }
    }
    types.into_iter().find_map(|ty| {
        let mut bounds = Vec::new();
        let mut read = |side: &IntegerTerm| -> Option<IntegerTerm> {
            if !operation(side) {
                return Some(side.clone());
            }
            let (observed, needed) = identity::machine_operation_of_integer_value(side, ty)?;
            bounds.extend(needed);
            Some(observed)
        };
        let (left, right) = (read(left)?, read(right)?);
        let (left, right): (SharedIntegerTerm, SharedIntegerTerm) = (left.into(), right.into());
        let read = match condition {
            ConditionTerm::IntegerLessThan(..) => ConditionTerm::IntegerLessThan(left, right),
            ConditionTerm::IntegerLessEqual(..) => ConditionTerm::IntegerLessEqual(left, right),
            ConditionTerm::IntegerGreaterThan(..) => ConditionTerm::IntegerGreaterThan(left, right),
            ConditionTerm::IntegerGreaterEqual(..) => {
                ConditionTerm::IntegerGreaterEqual(left, right)
            }
            ConditionTerm::IntegerEqual(..) => ConditionTerm::IntegerEqual(left, right),
            _ => ConditionTerm::IntegerNotEqual(left, right),
        };
        Some((native_comparison_view(&read, value)?, bounds))
    })
}

/// The Integer readings of a native comparison fact
/// ([`integer_observations_of_native_comparison`]), and of a promoted
/// comparison of widenings ([`integer_comparisons_of_widenings`]). A native
/// 8- or 16-bit comparison is the same fact as the `int32` comparison of
/// its operands' widenings (rule K8, [`narrow_comparison_as_int32`]), so it
/// has that comparison's readings.
pub(crate) fn integer_readings_with_promotions(proposition: &Proposition) -> Vec<Proposition> {
    if let Proposition::ConditionIs(condition, value) = proposition {
        let promoted = narrow_comparison_as_int32(condition);
        let widened =
            integer_comparisons_of_widenings(promoted.as_ref().unwrap_or(condition), *value);
        if !widened.is_empty() {
            return widened;
        }
    }
    integer_observations_of_native_comparison(proposition)
}

/// A native 8- or 16-bit comparison as the signed `int32` comparison of its
/// operands' widenings, which hold the same values (rule K8): `a <=_u8 b`
/// holds exactly when `widen(a) <= widen(b)` does. Order and interval
/// reasoning keeps its facts on 32-bit terms; this is its one bridge to a
/// native narrow fact, filed beside it and consulted for a native goal. The
/// comparison is built by the folding constructor, so it is the same term a
/// promoted comparison of the widenings is. `None` for any other condition.
/// One match on the root and two widenings.
pub(crate) fn narrow_comparison_as_int32(condition: &ConditionTerm) -> Option<ConditionTerm> {
    let ConditionTerm::Compare {
        format,
        relation,
        left,
        right,
    } = condition
    else {
        return None;
    };
    if format.format().bits() >= 32 {
        return None;
    }
    let widen = |term: &MachineTerm| {
        super::conversion::convert_term(*format, MachineIntegerType::Int32, term.clone())
    };
    Some(ConditionTerm::machine_compare(
        MachineIntegerType::Int32,
        *relation,
        widen(left),
        widen(right),
    ))
}

/// The `int32` spelling a native 8- or 16-bit comparison fact is also filed
/// under by the 32-bit indexes (order bounds, the `int32` equality graph,
/// scalar evidence, exact constants, truth nodes), which read that
/// spelling: [`narrow_comparison_as_int32`], unless it folds to a constant.
/// Each index files it inside its own adjuster, so assuming, forgetting and
/// rebuilding a fact agree.
pub(crate) fn narrow_fact_widening(condition: &ConditionTerm) -> Option<ConditionTerm> {
    narrow_comparison_as_int32(condition)
        .filter(|widened| !matches!(widened, ConditionTerm::Constant(_)))
}

/// The native 8- or 16-bit comparison a promoted `int32` comparison of
/// widenings from one narrow format is the same fact as (rule K8), spelled
/// natively: the reverse of [`narrow_comparison_as_int32`], read through
/// [`ConditionTerm::comparison_fact`]. A Rust comparison of two narrow
/// values states this native comparison. `None` for any other condition.
pub(crate) fn native_narrow_comparison(condition: &ConditionTerm) -> Option<ConditionTerm> {
    let ConditionTerm::Compare {
        format: MachineIntegerType::Int32,
        ..
    } = condition
    else {
        return None;
    };
    let (format, relation, left, right) = condition.comparison_fact()?;
    (format.format().bits() < 32).then(|| {
        ConditionTerm::narrow_compare(
            format,
            relation,
            left.term(format).into_owned(),
            right.term(format).into_owned(),
        )
    })
}

/// [`narrow_comparison_as_int32`] of a condition fact, with its truth.
pub(crate) fn narrow_proposition_as_int32(proposition: &Proposition) -> Option<Proposition> {
    let Proposition::ConditionIs(condition, value) = proposition else {
        return None;
    };
    narrow_comparison_as_int32(condition).map(|widened| Proposition::ConditionIs(widened, *value))
}

/// C compares an 8- or 16-bit value through its widening to `int32`
/// (rule C2): a signed 32-bit comparison whose sides are each such a
/// widening or a constant, at least one a widening, is the Integer
/// comparison of the sides' values, which a widening preserves (K8):
/// `0 <= widen(x)` is `0 <= to_integer(x as int32)`, which the Integer
/// engines read as `0 <= to_integer(x)` (rule W: a widening's observation is
/// built as written and read through to its operand's), so there is one
/// reading. One match on the two sides.
fn integer_comparisons_of_widenings(condition: &ConditionTerm, value: bool) -> Vec<Proposition> {
    use crate::kernel::CompareRelation as R;
    let ConditionTerm::Compare {
        format: MachineIntegerType::Int32,
        relation,
        left,
        right,
    } = condition
    else {
        return Vec::new();
    };
    let widening = |side: &MachineTerm| side.narrow_widening32_operand().is_some();
    if !widening(left) && !widening(right) {
        return Vec::new();
    }
    let side = |term: &MachineTerm| -> Option<SharedIntegerTerm> {
        if !widening(term) && term.constant32().is_none() {
            return None;
        }
        IntegerTerm::from_machine(MachineIntegerType::Int32, term.clone()).map(Into::into)
    };
    let (Some(l), Some(r)) = (side(left), side(right)) else {
        return Vec::new();
    };
    let (condition, truth) = match (relation, value) {
        (R::Equal, truth) => (ConditionTerm::IntegerEqual(l, r), truth),
        (R::LessThan, true) | (R::GreaterEqual, false) => {
            (ConditionTerm::IntegerLessThan(l, r), true)
        }
        (R::LessEqual, true) | (R::GreaterThan, false) => {
            (ConditionTerm::IntegerLessEqual(l, r), true)
        }
        (R::GreaterThan, true) | (R::LessEqual, false) => {
            (ConditionTerm::IntegerLessThan(r, l), true)
        }
        (R::GreaterEqual, true) | (R::LessThan, false) => {
            (ConditionTerm::IntegerLessEqual(r, l), true)
        }
    };
    vec![Proposition::ConditionIs(condition, truth)]
}

/// The Integer comparisons of exact observations whose native comparison
/// ([`native_comparison_of_integer_observation`]) is exactly `proposition`,
/// a native comparison fact: `1u32 <= x` gives `1 <= to_integer(x)`. Each
/// candidate is recomputed through the forward map, so only exact
/// converses, up to the fact's equivalent order spellings, are returned. A
/// 32-bit word equality may read as `int32` or as `uint32`
/// (`representation::comparison_readings`).
pub(crate) fn integer_observations_of_native_comparison(
    proposition: &Proposition,
) -> Vec<Proposition> {
    let Proposition::ConditionIs(condition, value) = proposition else {
        return Vec::new();
    };
    let Some((left, right, types)) = representation::comparison_readings(condition) else {
        return Vec::new();
    };
    // A native order has four spellings (`a >= 1` is `1 <= a`, and a false
    // `0 < x` is `x <= 0`) in every order family; the forward map produces
    // one, so compare against all of them.
    let spellings = crate::kernel::proof::fact_reasoning::order_claim_forms(proposition);
    let mut lifted = Vec::new();
    for &ty in types {
        let (Some(left), Some(right)) = (
            IntegerTerm::from_machine(ty, left.clone()),
            IntegerTerm::from_machine(ty, right.clone()),
        ) else {
            continue;
        };
        let (left, right): (SharedIntegerTerm, SharedIntegerTerm) = (left.into(), right.into());
        let candidates = [
            ConditionTerm::IntegerLessEqual(left.clone(), right.clone()),
            ConditionTerm::IntegerLessThan(left.clone(), right.clone()),
            ConditionTerm::IntegerLessEqual(right.clone(), left.clone()),
            ConditionTerm::IntegerLessThan(right.clone(), left.clone()),
            ConditionTerm::IntegerEqual(left.clone(), right.clone()),
        ];
        for candidate in candidates {
            let truth = if matches!(candidate, ConditionTerm::IntegerEqual(..)) {
                *value
            } else {
                true
            };
            if native_comparison_at_format(&candidate, truth).is_some_and(
                |(native, native_truth)| {
                    let native = Proposition::ConditionIs(native, native_truth);
                    &native == proposition || spellings.contains(&native)
                },
            ) {
                lifted.push(Proposition::ConditionIs(candidate, truth));
                break;
            }
        }
    }
    lifted
}

#[cfg(test)]
mod borrowed_comparison_tests {
    use super::*;
    use crate::kernel::{CompareRelation as R, MachineOperandView, Variable};

    #[test]
    fn written_comparison_views_borrow_and_normalize_every_relation() {
        for format in super::super::FORMATS {
            for (relation, truth, expected, swapped) in [
                (R::Equal, true, Relation::Equal, false),
                (R::Equal, false, Relation::NotEqual, false),
                (R::LessThan, true, Relation::Less, false),
                (R::LessThan, false, Relation::LessEqual, true),
                (R::LessEqual, true, Relation::LessEqual, false),
                (R::LessEqual, false, Relation::Less, true),
                (R::GreaterThan, true, Relation::Less, true),
                (R::GreaterThan, false, Relation::LessEqual, false),
                (R::GreaterEqual, true, Relation::LessEqual, true),
                (R::GreaterEqual, false, Relation::Less, false),
            ] {
                let condition = ConditionTerm::Compare {
                    format,
                    relation,
                    left: Box::new(MachineTerm::Variable(Variable(982412))),
                    right: Box::new(MachineTerm::Variable(Variable(982413))),
                };
                let ConditionTerm::Compare { left, right, .. } = &condition else {
                    unreachable!()
                };
                let view = comparison_view(&condition, truth).unwrap();
                assert_eq!(view.format, format);
                assert_eq!(view.relation, expected);
                let written = if swapped {
                    [right.as_ref(), left.as_ref()]
                } else {
                    [left.as_ref(), right.as_ref()]
                };
                for (operand, written) in view.operands.iter().zip(written) {
                    let MachineOperandView::Legacy(value) = operand.operand_view() else {
                        panic!("borrowed input")
                    };
                    assert!(std::ptr::eq(value, written));
                }
            }
        }
    }
}
