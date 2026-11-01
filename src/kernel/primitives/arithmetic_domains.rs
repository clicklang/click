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

    /// Conjoin an operation's domain once. Only intrinsic truths disappear;
    /// no ambient facts participate in constructing the obligation.
    pub(crate) fn arithmetic_domain(parts: impl IntoIterator<Item = Self>) -> Option<Self> {
        fn retain(part: Proposition) -> Option<Proposition> {
            match part {
                Proposition::ConditionIs(ref condition, value)
                    if PureFactContext::decide_intrinsically(condition) == Some(value) =>
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
