// Scaling tests of `src/kernel/primitives/integer.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn exact_integer_numeric_work_has_explicit_size_scaling() {
    let mut additions = Vec::new();
    let mut products = Vec::new();
    for bits in [64usize, 128, 256, 512] {
        let magnitude = BigInt::one() << bits;
        let (sum, add_work) = crate::instrumentation::measure_deterministic_work(|| {
            IntegerTerm::add(
                IntegerTerm::constant(magnitude.clone()),
                IntegerTerm::constant(-&magnitude - 7),
            )
        });
        assert_eq!(sum.as_const(), Some(&BigInt::from(-7)));
        let (product, product_work) = crate::instrumentation::measure_deterministic_work(|| {
            IntegerTerm::multiply(
                IntegerTerm::constant(magnitude.clone()),
                IntegerTerm::constant(-&magnitude),
            )
        });
        assert_eq!(product.as_const(), Some(&-(BigInt::one() << (2 * bits))));
        additions.push(add_work);
        products.push(product_work);
    }
    for pair in additions.windows(2) {
        assert!(pair[1] > pair[0]);
        assert!(
            pair[1] <= 2 * pair[0] + 8,
            "addition charges linear numeric work"
        );
    }
    for pair in products.windows(2) {
        assert!(
            pair[1] > 3 * pair[0],
            "multiplication must not charge only operand lengths"
        );
        assert!(
            pair[1] <= 4 * pair[0] + 8,
            "the conservative product allowance scales by bit products"
        );
    }
}

#[test]
fn truncating_integer_congruence_visits_shared_nodes_once() {
    for depth in [2usize, 8, 32, 128] {
        let from: SharedIntegerTerm = IntegerTerm::var(Variable(84)).into();
        let to: SharedIntegerTerm = IntegerTerm::var(Variable(85)).into();
        let mut term = from.clone();
        for level in 0..depth {
            term = if level % 2 == 0 {
                IntegerTerm::TruncatingQuotient(term.clone(), term).into()
            } else {
                IntegerTerm::TruncatingRemainder(term.clone(), term).into()
            };
        }
        let goal = Proposition::ConditionIs(ConditionTerm::IntegerEqual(term.clone(), term), true);
        let (rewritten, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::substitute_integer_term_in_proposition(&goal, &from, &to).unwrap()
        });
        assert!(work <= 4 * depth + 8, "depth={depth}, work={work}");
        let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) = rewritten
        else {
            unreachable!()
        };
        assert_eq!(left.id(), right.id());
        let mut node = left;
        for _ in 0..depth {
            let (left, right) = match node.as_ref() {
                IntegerTerm::TruncatingQuotient(a, b) | IntegerTerm::TruncatingRemainder(a, b) => {
                    (a, b)
                }
                _ => unreachable!(),
            };
            assert_eq!(left.id(), right.id());
            node = left.clone();
        }
        assert_eq!(node, to);
    }
}

#[test]
fn truncating_integer_constant_work_scales_with_operand_bits() {
    let mut work = Vec::new();
    for bits in [64usize, 128, 256, 512] {
        let a: BigInt = (BigInt::one() << bits) + 7;
        let b: BigInt = (BigInt::one() << (bits / 2)) + 1;
        let (_, charged) = crate::instrumentation::measure_deterministic_work(|| {
            IntegerTerm::truncating_quotient(
                IntegerTerm::constant(a.clone()),
                IntegerTerm::constant(b.clone()),
            )
        });
        work.push(charged);
    }
    for pair in work.windows(2) {
        assert!(pair[1] > 3 * pair[0]);
        assert!(pair[1] <= 4 * pair[0] + 16);
    }
}
