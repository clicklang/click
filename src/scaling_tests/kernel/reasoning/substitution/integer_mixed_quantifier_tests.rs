// Scaling tests of `src/kernel/reasoning/substitution.rs` (module `integer_mixed_quantifier_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn integer_function_quantifier_substitution_preserves_shared_dags() {
    let from = Variable(90);
    let mut work = Vec::new();
    for depth in [8, 16, 32, 64] {
        let mut value = IntegerTerm::var(from);
        for _ in 0..depth {
            let child: SharedIntegerTerm = value.into();
            value = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                "pair".into(),
                vec![
                    PureFunctionArgument::Integer(child.clone()),
                    PureFunctionArgument::Integer(child),
                ],
            ));
        }
        let source = Proposition::Equal(
            Term::Integer(value.into()),
            Term::Integer(IntegerTerm::constant_i64(0).into()),
        );
        let (result, measured) = crate::instrumentation::measure_deterministic_work(|| {
            substitute_integer_variable_in_pure_proposition(
                &source,
                from,
                &IntegerTerm::constant_i64(2),
            )
            .unwrap()
        });
        let Proposition::Equal(Term::Integer(value), _) = result else {
            panic!("equality lost")
        };
        let mut value = value.into_native_compat();
        for _ in 0..depth {
            let IntegerTerm::PureFunctionApplication(application) = value else {
                panic!("application lost")
            };
            let [
                PureFunctionArgument::Integer(left),
                PureFunctionArgument::Integer(right),
            ] = application.arguments()
            else {
                panic!("arguments lost")
            };
            assert_eq!(left.id(), right.id());
            value = left.as_ref().clone();
        }
        assert_eq!(value, IntegerTerm::constant_i64(2));
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(pair[1] <= pair[0] * 3, "{work:?}");
    }
}

#[test]
fn integer_substitution_nested_carrier_scopes_scale_with_shared_body() {
    let source = Variable(9_240);
    let mut work = Vec::new();
    for depth in [8, 16, 32, 64] {
        let mut body = Proposition::Equal(
            Term::Integer(IntegerTerm::var(source).into()),
            Term::Integer(IntegerTerm::constant_i64(0).into()),
        );
        for index in (0..depth).rev() {
            let variable = Variable(9_300 + (index / 2) as u64);
            body = if index % 2 == 0 {
                crate::kernel::quantifiers::test_forall(
                    Default::default(),
                    variable,
                    Sort::ProgramInt32,
                    body,
                )
            } else {
                crate::kernel::quantifiers::test_exists(
                    format!("integer{index}"),
                    variable,
                    Sort::Integer,
                    body,
                )
            };
        }
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            substitute_integer_variable_in_pure_proposition(
                &body,
                source,
                &IntegerTerm::constant_i64(3),
            )
            .expect("nested carrier scopes should remain bounded")
        });
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3,
            "nested scope rewrite expanded: {work:?}"
        );
    }
}

#[test]
fn integer_substitution_algebraic_capture_scales_with_nested_scopes() {
    let from = Variable(9_350);
    let bound = Variable(9_351);
    let algebraic_type = AlgebraicType::parameter("Flag".into());
    let replacement = algebraic_projection(&algebraic_type, bound);
    let samples = [8, 16, 32, 64].map(|depth| {
        let mut source = Proposition::Equal(
            Term::Integer(IntegerTerm::var(from).into()),
            Term::Integer(replacement.clone().into()),
        );
        for _ in 0..depth {
            source = crate::kernel::quantifiers::test_forall(
                Default::default(),
                bound,
                Sort::Algebraic(algebraic_type.clone()),
                source,
            );
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            substitute_integer_variable_in_pure_proposition(&source, from, &replacement).unwrap()
        });
        let mut remaining = result;
        let mut issued = BTreeSet::new();
        let mut innermost = bound;
        for _ in 0..depth {
            let Proposition::ForAll { var, body, .. } = remaining else {
                panic!("quantifier was lost");
            };
            assert_ne!(*var, bound);
            assert!(issued.insert(var));
            innermost = *var;
            remaining = *body;
        }
        assert_eq!(
            remaining,
            Proposition::Equal(
                Term::Integer(replacement.clone().into()),
                Term::Integer(algebraic_projection(&algebraic_type, innermost).into())
            )
        );
        work
    });
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3,
            "algebraic capture work must scale with explicit scopes: {samples:?}"
        );
    }
}
