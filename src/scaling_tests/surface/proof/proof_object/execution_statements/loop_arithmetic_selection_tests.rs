// Goal-local arithmetic selection from the loop's allowed named premises.
use super::*;

#[test]
fn ranking_selection_skips_other_counter_equalities() {
    for size in [4u64, 32, 64, 256] {
        let i = Bitvector32Term::Variable(Variable(794_001));
        let variable =
            |name: &str| ContractExpression::CFragment(CExpression::Variable(name.into()));
        let number = |value| ContractExpression::CFragment(CExpression::Value(int32(value)));
        let lower = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(
                Box::new(Bitvector32Term::Constant(0)),
                Box::new(i.clone()),
            ),
            true,
        );
        let upper = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(
                Box::new(i.clone()),
                Box::new(Bitvector32Term::Constant(4)),
            ),
            true,
        );
        let mut named = vec![
            (
                lower.clone(),
                ClickProposition::Comparison {
                    left: number(0),
                    operator: ComparisonOperator::LessEqual,
                    right: variable("i"),
                },
            ),
            (
                upper.clone(),
                ClickProposition::Comparison {
                    left: variable("i"),
                    operator: ComparisonOperator::LessThan,
                    right: number(4),
                },
            ),
        ];
        for index in 0..size {
            named.push((
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(Bitvector32Term::Variable(Variable(795_000 + index))),
                        Box::new(i.clone()),
                    ),
                    true,
                ),
                ClickProposition::Comparison {
                    left: variable(&format!("v{index}")),
                    operator: ComparisonOperator::Equal,
                    right: variable("i"),
                },
            ));
        }
        let measure = Bitvector32Term::Add(
            Box::new(Bitvector32Term::Subtract(
                Box::new(Bitvector32Term::Constant(0)),
                Box::new(i),
            )),
            Box::new(Bitvector32Term::Constant(3)),
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(
                Box::new(Bitvector32Term::Constant(0)),
                Box::new(measure),
            ),
            true,
        );
        let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
            compact_bundle_arithmetic_premises(&goal, &named)
        });
        assert_eq!(selected.len(), 2, "{size} counter equalities");
        let kernels = selected
            .into_iter()
            .map(|(kernel, _)| kernel)
            .collect::<Vec<_>>();
        assert!(kernels.contains(&lower));
        assert!(kernels.contains(&upper));
        assert!(
            work <= size as usize * 16 + 256,
            "{size} counters: {work} selection work"
        );
        let certificate =
            crate::surface::checking::plan_signed_arithmetic_certificate(&goal, &kernels).unwrap();
        certificate.check(&goal, &kernels).unwrap();
    }
}
