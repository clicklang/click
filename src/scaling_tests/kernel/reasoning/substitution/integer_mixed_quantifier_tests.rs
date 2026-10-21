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
            Term::Integer(value),
            Term::Integer(IntegerTerm::constant_i64(0)),
        );
        let (result, measured) = crate::instrumentation::measure_deterministic_work(|| {
            substitute_integer_variable_in_pure_proposition(
                &source,
                from,
                &IntegerTerm::constant_i64(2),
            )
            .unwrap()
        });
        let Proposition::Equal(Term::Integer(mut value), _) = result else {
            panic!("equality lost")
        };
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
            Term::Integer(IntegerTerm::var(source)),
            Term::Integer(IntegerTerm::constant_i64(0)),
        );
        for index in (0..depth).rev() {
            let variable = Variable(9_300 + (index / 2) as u64);
            body = if index % 2 == 0 {
                Proposition::ForAll { name: Default::default(),
                    var: variable,
                    sort: Sort::CInt32,
                    body: Box::new(body),
                }
            } else {
                Proposition::Exists {
                    name: format!("integer{index}"),
                    var: variable,
                    sort: Sort::Integer,
                    body: Box::new(body),
                }
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
