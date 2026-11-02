//! Ordinary propositions for arithmetic domains. Construction reads only the
//! operation's explicit operands; deciding these propositions is separate.
use super::*;

impl ConditionTerm {
    /// The two ordinary equalities describing the exceptional signed quotient
    /// or remainder pair. C promotes narrow operands before reaching this helper.
    pub(crate) fn signed_division_exception_tests(
        format: MachineIntegerType,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> [Self; 2] {
        let (minimum, minus_one) = match format {
            MachineIntegerType::Int32 => (
                Bitvector32Term::Constant(i32::MIN as u32),
                Bitvector32Term::Constant(u32::MAX),
            ),
            MachineIntegerType::Int64 => (
                Bitvector32Term::Int64Constant(i64::MIN),
                Bitvector32Term::Int64Constant(-1),
            ),
            _ => unreachable!("native signed division uses int32 or int64"),
        };
        [
            Self::machine_compare(format, CompareRelation::Equal, left.clone(), minimum),
            Self::machine_compare(format, CompareRelation::Equal, right.clone(), minus_one),
        ]
    }
}

#[cfg(test)]
mod construction_tests {
    use super::*;

    #[test]
    fn domain_construction_retains_symbolic_truths_for_obligation_discharge() {
        let value = IntegerTerm::from_machine(
            MachineIntegerType::Int64,
            Bitvector32Term::Variable(Variable(987000)),
        )
        .unwrap();
        // An already written symbolic bound stays a proposition. The domain
        // builder's root-type rule below does not fold ordinary comparisons.
        let domain = Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::integer_less_equal(
                    value.clone(),
                    IntegerTerm::constant_i64(i64::MAX),
                ),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::integer_greater_equal(value, IntegerTerm::constant_i64(i64::MIN)),
                true,
            )),
        );
        // A machine value fits its type, but proving that is not construction.
        let (retained, work) = crate::instrumentation::measure_deterministic_work(|| {
            Proposition::arithmetic_domain([domain.clone()])
        });
        assert_eq!(retained, Some(domain));
        assert_eq!(
            work, 3,
            "only the conjunction and its two conditions are visited"
        );
        assert_eq!(
            Proposition::arithmetic_domain([
                Proposition::ConditionIs(ConditionTerm::Constant(true), true),
                Proposition::ConditionIs(ConditionTerm::Constant(false), false),
            ]),
            None
        );
        let falsehood = Proposition::ConditionIs(ConditionTerm::Constant(false), true);
        assert_eq!(
            Proposition::arithmetic_domain([falsehood.clone()]),
            Some(falsehood)
        );
    }

    #[test]
    fn an_exact_machine_value_needs_a_range_only_for_a_noncontaining_type() {
        use MachineIntegerType as Ty;
        for (source, destination, fits) in [
            (Ty::Int32, Ty::Int32, true),
            (Ty::Int8, Ty::Int32, true),
            (Ty::UInt32, Ty::Int64, true),
            (Ty::Int32, Ty::Int8, false),
            (Ty::UInt32, Ty::Int32, false),
            (Ty::Int32, Ty::UInt32, false),
        ] {
            let value =
                IntegerTerm::from_machine(source, Bitvector32Term::Variable(Variable(987001)))
                    .unwrap();
            let range = Proposition::arithmetic_result_range(destination, value);
            assert_eq!(
                matches!(
                    range,
                    Proposition::ConditionIs(ConditionTerm::Constant(true), true)
                ),
                fits
            );
        }
    }
}

impl Proposition {
    pub(crate) fn signed_division_exclusion(
        format: MachineIntegerType,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> Self {
        let [minimum, minus_one] =
            ConditionTerm::signed_division_exception_tests(format, left, right);
        Self::Or(
            Box::new(Self::ConditionIs(minimum, false)),
            Box::new(Self::ConditionIs(minus_one, false)),
        )
    }

    pub(crate) fn signed_division_defined(
        format: MachineIntegerType,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> Self {
        let zero = match format {
            MachineIntegerType::Int32 => Bitvector32Term::Constant(0),
            MachineIntegerType::Int64 => Bitvector32Term::Int64Constant(0),
            _ => unreachable!("native signed division uses int32 or int64"),
        };
        Self::And(
            Box::new(Self::ConditionIs(
                ConditionTerm::machine_compare(format, CompareRelation::Equal, right.clone(), zero),
                false,
            )),
            Box::new(Self::signed_division_exclusion(format, left, right)),
        )
    }
}

impl Proposition {
    /// The complete representability domain of exact signed arithmetic.
    /// Mathematical arithmetic is total, so these bounds introduce no debt
    /// for the machine operation whose definedness they describe.
    pub(crate) fn arithmetic_result_range(format: MachineIntegerType, exact: IntegerTerm) -> Self {
        // An identity such as x + 0 can leave the exact result as one machine
        // observation. Its type already guarantees this range. Inspect only
        // the root type, never its operand or any facts; ordinary written
        // comparisons and the machine operation itself remain structural.
        if let IntegerTerm::Machine(value) = &exact
            && format.format().contains(value.ty().format())
        {
            return Self::ConditionIs(ConditionTerm::Constant(true), true);
        }
        let (minimum, maximum) = format.format().bounds();
        Self::And(
            Box::new(Self::ConditionIs(
                ConditionTerm::integer_less_equal(exact.clone(), IntegerTerm::constant(maximum)),
                true,
            )),
            Box::new(Self::ConditionIs(
                ConditionTerm::integer_greater_equal(exact, IntegerTerm::constant(minimum)),
                true,
            )),
        )
    }

    pub(crate) fn signed_arithmetic_domain(
        format: MachineIntegerType,
        op: MachineBinaryOp,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> Self {
        let a = IntegerTerm::from_machine(format, left.clone()).expect("arithmetic operand");
        let b = IntegerTerm::from_machine(format, right.clone()).expect("arithmetic operand");
        let exact = match op {
            MachineBinaryOp::Add => IntegerTerm::add(a, b),
            MachineBinaryOp::Subtract => IntegerTerm::subtract(a, b),
            MachineBinaryOp::Multiply => IntegerTerm::multiply(a, b),
            _ => unreachable!("ring arithmetic"),
        };
        Self::arithmetic_result_range(format, exact)
    }

    /// Conjoin an operation's domain once, discarding literal truths only.
    /// Symbolic conditions belong to ordinary obligation discharge. Running
    /// even the empty-context proof checker here repeatedly normalizes growing
    /// operand trees while the evaluator is only trying to construct a debt.
    pub(crate) fn arithmetic_domain(parts: impl IntoIterator<Item = Self>) -> Option<Self> {
        fn retain(part: Proposition) -> Option<Proposition> {
            crate::instrumentation::record_deterministic_work(1);
            match part {
                Proposition::ConditionIs(ConditionTerm::Constant(actual), expected)
                    if actual == expected =>
                {
                    None
                }
                Proposition::And(left, right) => match (retain(*left), retain(*right)) {
                    (Some(left), Some(right)) => {
                        Some(Proposition::And(Box::new(left), Box::new(right)))
                    }
                    (left, right) => left.or(right),
                },
                Proposition::Or(left, right) => match (retain(*left), retain(*right)) {
                    (Some(left), Some(right)) => {
                        Some(Proposition::Or(Box::new(left), Box::new(right)))
                    }
                    _ => None,
                },
                part => Some(part),
            }
        }
        parts
            .into_iter()
            .filter_map(retain)
            .reduce(|left, right| Self::And(Box::new(left), Box::new(right)))
    }
}

impl ConditionTerm {
    /// A total representability comparison. The enclosing shift domain checks
    /// the original count; masking here makes the bound itself well-defined
    /// even when that original count is invalid.
    pub(crate) fn signed_shift_result_fits(
        format: MachineIntegerType,
        left: Bitvector32Term,
        count: Bitvector32Term,
    ) -> Self {
        let constant = |n: u64| {
            crate::kernel::machine_integer::range::constant_word(format, &n.into())
                .expect("shift bound fits")
        };
        let bits = format.format().bits();
        let masked = Bitvector32Term::machine_binary(
            format,
            MachineBinaryOp::BitwiseAnd,
            count,
            constant((bits - 1).into()),
        );
        let bound = Bitvector32Term::machine_binary(
            format,
            MachineBinaryOp::ShiftRight,
            constant(if bits == 32 {
                i32::MAX as u64
            } else {
                i64::MAX as u64
            }),
            masked,
        );
        Self::machine_compare(format, CompareRelation::LessEqual, left, bound)
    }
}
