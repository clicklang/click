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
