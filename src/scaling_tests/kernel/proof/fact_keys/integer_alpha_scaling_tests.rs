// Scaling tests of `src/kernel/proof/fact_keys.rs` (module `integer_alpha_scaling_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn truncating_integer_alpha_keys_preserve_operator_and_shared_binders() {
    for depth in [2usize, 8, 32, 128] {
        let build = |variable, remainder| {
            let mut term = IntegerTerm::var(Variable(variable));
            for _ in 0..depth {
                let child: SharedIntegerTerm = term.into();
                term = if remainder {
                    IntegerTerm::TruncatingRemainder(child.clone(), child)
                } else {
                    IntegerTerm::TruncatingQuotient(child.clone(), child)
                };
            }
            term
        };
        let key = |variable, remainder| {
            alpha_integer_key(
                &build(variable, remainder),
                &mut BTreeMap::from([(Variable(variable), 0)]),
            )
            .unwrap()
        };
        let (left, work) = crate::instrumentation::measure_deterministic_work(|| key(91001, false));
        let right = key(91002, false);
        assert_eq!(left, right);
        assert!(work <= 8 * depth + 16, "depth={depth}, work={work}");
        assert_ne!(left, key(91001, true));
        let mut a = DefaultHasher::new();
        let mut b = DefaultHasher::new();
        left.hash(&mut a);
        right.hash(&mut b);
        assert_eq!(a.finish(), b.finish());
    }
}

#[test]
fn integer_fold_alpha_key_visits_shared_bodies_once_per_scope() {
    let mut work = Vec::new();
    for depth in [8, 16, 32, 64] {
        let mut term = IntegerTerm::var(Variable(920));
        for _ in 0..depth {
            let child: SharedIntegerTerm = term.into();
            term = integer_key_test_fold(
                Variable(921),
                IntegerTerm::constant_i64(0),
                IntegerTerm::Add(child.clone(), child),
            );
        }
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            alpha_integer_key(&term, &mut BTreeMap::new()).unwrap()
        });
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(pair[1] <= pair[0] * 3, "{work:?}");
    }
}
