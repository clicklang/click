// Scaling tests of `src/kernel/proof/term_rewrite/spec_rewrite.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn checked_spec_rewrite_match_bindings_scale_with_arity() {
    let mut samples = Vec::new();
    for arity in [4usize, 8, 16, 32] {
        let arm = SpecIntegerMatchArm {
            variant: "Node".into(),
            bindings: (0..arity).map(|index| format!("v{index}")).collect(),
            binding_types: vec![AlgebraicValueType::Integer; arity],
            binding_variables: (0..arity)
                .map(|index| Some(Variable(100 + index as u64)))
                .collect(),
            body: Box::new(SpecIntegerExpression::Term(IntegerTerm::constant_i64(0))),
        };
        let c_replacements = BTreeMap::new();
        let integer_replacements = BTreeMap::new();
        let algebraic_replacements = BTreeMap::new();
        let (rewritten, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut rewrite = TermRewrite::for_checked_typed_variables(
                &c_replacements,
                &integer_replacements,
                &algebraic_replacements,
            );
            rewrite.rewrite_spec_integer_match_arm(&arm)
        });
        let rewritten = rewritten.unwrap();
        assert_eq!(rewritten.binding_variables, arm.binding_variables);
        samples.push((arity, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 2 + 64,
            "Integer match binding rewrite grew superlinearly: {samples:?}"
        );
    }
}

#[test]
fn checked_spec_rewrite_scales_with_nested_spec_nodes() {
    let source = Variable(47);
    let mut samples = Vec::new();
    for depth in [8usize, 16, 32, 64] {
        let mut proposition = SpecProposition::IntegerComparison {
            left: SpecIntegerExpression::Term(IntegerTerm::var(source)),
            operator: IntegerComparisonOperator::Equal,
            right: SpecIntegerExpression::Term(IntegerTerm::constant_i64(7)),
        };
        for _ in 0..depth {
            proposition = SpecProposition::Not(Box::new(proposition));
        }
        let c_replacements = BTreeMap::new();
        let integer_replacements = BTreeMap::from([(source, IntegerTerm::constant_i64(7))]);
        let algebraic_replacements = BTreeMap::new();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut rewrite = TermRewrite::for_checked_typed_variables(
                &c_replacements,
                &integer_replacements,
                &algebraic_replacements,
            );
            rewrite.spec_proposition(&proposition)
        });
        assert!(result.is_ok());
        samples.push((depth, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 2 + 64,
            "checked Spec rewrite grew superlinearly: {samples:?}"
        );
    }
}
