//! Existing unsigned order premises read from retained operand roots.
//! Each rule examines at most two operation levels; no context is searched.
use crate::kernel::machine_integer::{
    Relation,
    comparison::{NativeComparisonView, comparison_view, condition_for_operand_views},
};
use crate::kernel::{
    Bitvector32Term as B, CompareRelation as R, ConditionTerm as C, MachineBinaryOp as Op,
    MachineIntegerType as T, MachineOperandView as V,
};

fn order(condition: &C) -> Option<NativeComparisonView<'_>> {
    // Native rules historically accept only these written directions.
    if matches!(
        condition,
        C::Compare {
            relation: R::GreaterThan | R::GreaterEqual,
            ..
        }
    ) {
        return None;
    }
    comparison_view(condition, true).filter(|view| {
        view.format == T::UInt64 && matches!(view.relation, Relation::Less | Relation::LessEqual)
    })
}

fn binary(operand: V<'_>, op: Op) -> Option<[V<'_>; 2]> {
    let (format, operation, operands) = operand.binary()?;
    (format == T::UInt64 && operation == op).then_some(operands)
}

fn same(a: V<'_>, b: V<'_>) -> bool {
    match (a, b) {
        (V::Legacy(a), V::Legacy(b)) => a == b,
        (V::Shared(a), V::Shared(b)) => a == b,
        (V::Shared(shared), V::Legacy(legacy)) | (V::Legacy(legacy), V::Shared(shared)) => {
            crate::kernel::KernelTermImport::default()
                .machine_arithmetic(T::UInt64, legacy)
                .as_ref()
                == Some(shared)
        }
    }
}

fn compare(relation: R, a: V<'_>, b: V<'_>) -> C {
    condition_for_operand_views(T::UInt64, relation, [a, b])
}

fn predecessor(operand: V<'_>) -> Option<V<'_>> {
    let [a, b] = binary(operand, Op::Add)?;
    if b.uint64_constant() == Some(1) {
        Some(a)
    } else if a.uint64_constant() == Some(1) {
        Some(b)
    } else {
        None
    }
}

impl C {
    /// A sufficient premise for non-wrapping unsigned successor rules.
    pub(crate) fn uint64_successor_guard(&self) -> Option<Self> {
        let view = order(self)?;
        let [a, b] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        if predecessor(b).is_some_and(|previous| same(previous, a)) {
            return Some(compare(
                R::LessEqual,
                a,
                V::Legacy(&B::UInt64Constant(u64::MAX - 1)),
            ));
        }
        if view.relation == Relation::LessEqual {
            return Some(compare(R::LessThan, predecessor(a)?, b));
        }
        let [n, next] = binary(a, Op::Subtract)?;
        let [other_n, old] = binary(b, Op::Subtract)?;
        (same(n, other_n) && predecessor(next).is_some_and(|p| same(p, old)))
            .then(|| compare(R::LessThan, old, n))
    }

    /// Sufficient non-wrapping bounds for an unsigned slice remainder length.
    pub(crate) fn uint64_subtraction_guard(&self) -> Option<Self> {
        let view = order(self)?;
        let [a, b] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        if view.relation == Relation::Less && a.uint64_constant() == Some(0) {
            let [length, midpoint] = binary(b, Op::Subtract)?;
            return Some(compare(R::LessThan, midpoint, length));
        }
        let [length, midpoint] = binary(a, Op::Subtract)?;
        (same(length, b)
            && (view.relation == Relation::LessEqual
                || midpoint.uint64_constant().is_some_and(|c| c >= 1)))
        .then(|| compare(R::LessEqual, midpoint, length))
    }

    pub(crate) fn uint64_remainder_bound_guard(&self) -> Option<Self> {
        let view = order(self)?;
        let [a, b] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        let [n, d] = binary(a, Op::Remainder)?;
        ((view.relation == Relation::LessEqual && same(n, b))
            || (view.relation == Relation::Less && same(d, b)))
        .then(|| compare(R::LessThan, V::Legacy(&B::UInt64Constant(0)), d))
    }

    /// `(n - k) <= upper` follows from `k <= n <= upper`.
    pub(crate) fn uint64_subtraction_upper_bound_guards(&self) -> Option<Vec<Self>> {
        let view = order(self)?;
        if view.relation != Relation::LessEqual {
            return None;
        }
        let [difference, upper] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        let [length, removed] = binary(difference, Op::Subtract)?;
        if same(length, upper) {
            return None;
        }
        Some(vec![
            compare(R::LessEqual, removed, length),
            compare(R::LessEqual, length, upper),
        ])
    }

    /// Restore at most the removed amount under the same three native premises.
    pub(crate) fn uint64_partial_restoration_upper_bound_guards(&self) -> Option<Vec<Self>> {
        let view = order(self)?;
        if view.relation != Relation::LessEqual {
            return None;
        }
        let [sum, upper] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        let [left, right] = binary(sum, Op::Add)?;
        let ([whole, removed], restored) = if let Some(parts) = binary(left, Op::Subtract) {
            (parts, right)
        } else {
            (binary(right, Op::Subtract)?, left)
        };
        Some(vec![
            compare(R::LessEqual, removed, whole),
            compare(R::LessEqual, restored, removed),
            compare(R::LessEqual, whole, upper),
        ])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{IntegerTerm, KernelTermExport, SharedMachineIntegerTerm, Variable};

    fn guards(c: &C) -> Vec<Option<Vec<C>>> {
        vec![
            c.uint64_successor_guard().map(|g| vec![g]),
            c.uint64_subtraction_guard().map(|g| vec![g]),
            c.uint64_remainder_bound_guard().map(|g| vec![g]),
            c.uint64_subtraction_upper_bound_guards(),
            c.uint64_partial_restoration_upper_bound_guards(),
        ]
    }

    #[test]
    fn shared_wide_guards_preserve_native_premises_and_refusals() {
        let _session = crate::kernel::VerificationSession::enter();
        let n = B::uint64_add(B::Variable(Variable(998121)), B::Variable(Variable(998124)));
        let k = B::uint64_add(B::Variable(Variable(998122)), B::Variable(Variable(998125)));
        let r = B::Variable(Variable(998123));
        let next = B::uint64_add(k.clone(), B::UInt64Constant(1));
        let difference = B::uint64_subtract(n.clone(), k.clone());
        let cases = [
            (k.clone(), next.clone(), 0),
            (next.clone(), n.clone(), 0),
            (B::uint64_subtract(n.clone(), next), difference.clone(), 0),
            (B::UInt64Constant(0), difference.clone(), 1),
            (difference.clone(), n.clone(), 1),
            (
                B::uint64_subtract(n.clone(), B::UInt64Constant(2)),
                n.clone(),
                1,
            ),
            (B::uint64_remainder(n.clone(), k.clone()), n.clone(), 2),
            (B::uint64_remainder(n.clone(), k.clone()), k.clone(), 2),
            (difference.clone(), r.clone(), 3),
            (B::uint64_add(difference.clone(), k.clone()), r.clone(), 4),
            (B::uint64_add(r.clone(), difference), n.clone(), 4),
            (n.clone(), r.clone(), 5),
        ];
        let mut exercised = [false; 5];
        for (a, b, expected_rule) in cases {
            for relation in [R::LessThan, R::LessEqual] {
                let native = C::Compare {
                    format: T::UInt64,
                    relation,
                    left: Box::new(a.clone()),
                    right: Box::new(b.clone()),
                };
                let expected = guards(&native);
                if expected_rule < 5 && expected[expected_rule].is_some() {
                    exercised[expected_rule] = true;
                }
                let a = SharedMachineIntegerTerm::from_shared(
                    T::UInt64,
                    crate::kernel::KernelTermImport::default()
                        .machine_arithmetic(T::UInt64, &a)
                        .unwrap(),
                )
                .unwrap();
                let b = SharedMachineIntegerTerm::from_shared(
                    T::UInt64,
                    crate::kernel::KernelTermImport::default()
                        .machine_arithmetic(T::UInt64, &b)
                        .unwrap(),
                )
                .unwrap();
                let observed = match relation {
                    R::LessThan => C::integer_less_than(
                        IntegerTerm::Machine(a.clone()),
                        IntegerTerm::Machine(b.clone()),
                    ),
                    _ => C::integer_less_equal(
                        IntegerTerm::Machine(a.clone()),
                        IntegerTerm::Machine(b.clone()),
                    ),
                };
                let exports = KernelTermExport::machine_export_count();
                let actual = guards(&observed);
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                // Fixed-size atoms may use native comparison constructors;
                // the arithmetic operands must remain shared.
                for operand in [&a, &b] {
                    assert!(
                        operand.operand_view().binary().is_none() || !operand.has_boxed_operand(),
                        "cached arithmetic operand for {native:?}"
                    );
                }
                for (actual, expected) in actual.into_iter().zip(expected) {
                    match (actual, expected) {
                        (None, None) => {}
                        (Some(actual), Some(expected)) => {
                            assert_eq!(actual.len(), expected.len());
                            for (actual, expected) in actual.iter().zip(&expected) {
                                match (
                                    comparison_view(actual, true),
                                    comparison_view(expected, true),
                                ) {
                                    (Some(a), Some(b)) => {
                                        assert_eq!(a.format, b.format);
                                        assert_eq!(a.relation, b.relation);
                                        for (a, b) in a.operands.iter().zip(&b.operands) {
                                            assert!(same(a.operand_view(), b.operand_view()));
                                        }
                                    }
                                    _ => assert_eq!(actual, expected),
                                }
                            }
                        }
                        _ => panic!("different guard selection for {native:?}"),
                    }
                }
                assert_eq!(KernelTermExport::machine_export_count(), exports);
            }
        }
        assert!(exercised.into_iter().all(|hit| hit));
        let reversed = C::Compare {
            format: T::UInt64,
            relation: R::GreaterEqual,
            left: Box::new(n),
            right: Box::new(k),
        };
        assert!(guards(&reversed).iter().all(Option::is_none));
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/primitives/wide_order_guards/tests.rs");
}
