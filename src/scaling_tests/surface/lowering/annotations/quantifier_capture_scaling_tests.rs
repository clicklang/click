// Scaling tests of native capture selection in `annotations.rs`.
use super::*;

#[test]
fn quantifier_capture_selection_visits_only_the_explicit_proposition() {
    for count in [16usize, 64, 256] {
        let mut proposition = ClickProposition::Comparison {
            left: ContractExpression::ProgramExpression(ProgramExpression::Value(
                ProgramValue::UInt64(crate::kernel::MachineTerm::Variable(Variable::produced(
                    crate::kernel::Producer::ProofQuantifier,
                    0,
                ))),
            )),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::ProgramExpression(ProgramExpression::Variable(
                "bound".into(),
            )),
        };
        let leaf = proposition.clone();
        for _ in 1..count {
            proposition = ClickProposition::And(Box::new(proposition), Box::new(leaf.clone()));
        }
        let mut captures = BTreeSet::<QuantifierCapture>::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            collect_click_proposition_referenced_bindings(&proposition, &mut captures);
        });
        assert_eq!(captures.len(), 2);
        assert!(
            captures.contains(&QuantifierCapture::Variable(Variable::produced(
                crate::kernel::Producer::ProofQuantifier,
                0
            )))
        );
        assert!(captures.contains(&QuantifierCapture::Name("bound".to_string())));
        assert!(
            work >= 2 * count && work <= 16 * count,
            "{count} inputs: {work} work"
        );
    }
}
