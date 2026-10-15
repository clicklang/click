// Scaling tests of `src/kernel/tests/wide_multiply_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn wide_multiply_known_bounds_work_does_not_scan_unrelated_ambient_facts() {
    let (_, bounds) = product_and_bounds(MachineIntegerType::Int128, MachineIntegerType::Int128);
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut assumptions = PureFactContext::new();
        for index in 0..size {
            assumptions = assumptions
                .assume_condition(ConditionTerm::Variable(Variable(151_000 + index)), true);
        }
        for bound in &bounds {
            assumptions = assumptions.assume_condition(bound.clone(), true);
        }
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::eval::apply_c_multiply(
                CValue::Int128(Bitvector32Term::Variable(Variable(150_001))),
                CValue::Int128(Bitvector32Term::Variable(Variable(150_002))),
                Vec::new().into(),
                Vec::new(),
                &assumptions,
            )
        });
        assert_eq!(paths.len(), 1);
        assert!(paths[0].facts.iter().any(|fact| matches!(
            fact.proposition(),
            Proposition::ConditionIs(ConditionTerm::IntegerEqual(_, _), true)
        )));
        assert!(work < 4096, "{size}: {work}");
        samples.push(work);
    }
    assert!(
        samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 64,
        "{samples:?}"
    );
}

#[test]
fn wide_multiply_resolves_indexed_narrow_inputs_with_their_signedness() {
    for (ty, input, expected) in [
        (
            MachineIntegerType::Int64,
            Bitvector32Term::Int64Constant(i64::MIN),
            BigInt::from(i64::MIN) * 2,
        ),
        (
            MachineIntegerType::UInt64,
            Bitvector32Term::UInt64Constant(u64::MAX),
            BigInt::from(u64::MAX) * 2,
        ),
    ] {
        let variable = Bitvector32Term::Variable(Variable(153_000));
        let condition = if ty == MachineIntegerType::Int64 {
            ConditionTerm::int64_equal(variable.clone(), input)
        } else {
            ConditionTerm::uint64_equal(variable.clone(), input)
        };
        let mut samples = Vec::new();
        for size in [16, 64, 256, 1024] {
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                assumptions = assumptions
                    .assume_condition(ConditionTerm::Variable(Variable(154_000 + index)), true);
            }
            assumptions = assumptions.assume_condition(condition.clone(), true);
            let widened = Bitvector32Term::machine_integer_cast(
                ty,
                MachineIntegerType::Int128,
                variable.clone(),
            );
            let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::eval::apply_c_multiply(
                    CValue::Int128(widened),
                    MachineIntegerType::Int128
                        .constant_value(
                            MachineIntegerConstant::from_signed(
                                MachineIntegerType::Int128.format(),
                                2,
                            )
                            .unwrap(),
                        )
                        .unwrap(),
                    Vec::new().into(),
                    Vec::new(),
                    &assumptions,
                )
            });
            assert_eq!(paths.len(), 1);
            assert!(paths[0].obligations.is_empty());
            let CExpressionOutcome::Value(value) = &paths[0].outcome else {
                panic!("known bounded product")
            };
            assert_eq!(
                MachineIntegerType::Int128
                    .constant_from_value(value)
                    .unwrap()
                    .to_integer(),
                expected
            );
            assert!(work < 4096, "{size}: {work}");
            samples.push(work);
        }
        assert!(
            samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 64,
            "{samples:?}"
        );
    }
}
