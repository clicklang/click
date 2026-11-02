//! Native signed division records its ordinary domain, not an opaque overflow
//! atom. The zero-divisor split has already happened on entry here.
use super::*;

pub(super) fn apply_nonzero(
    format: MachineIntegerType,
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    result: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Vec<CExpressionPath> {
    let [minimum, minus_one] =
        ConditionTerm::signed_division_exception_tests(format, &left, &right);
    let safe = Proposition::signed_division_exclusion(format, &left, &right);
    let exceptional = Proposition::And(
        Box::new(Proposition::ConditionIs(minimum.clone(), true)),
        Box::new(Proposition::ConditionIs(minus_one.clone(), true)),
    );
    let known = if assumptions.proves_exact(&safe) {
        Some(false)
    } else if assumptions.proves_exact(&exceptional) {
        Some(true)
    } else {
        match (
            decide_with_facts(assumptions, &facts, &minimum),
            decide_with_facts(assumptions, &facts, &minus_one),
        ) {
            (Some(false), _) | (_, Some(false)) => Some(false),
            (Some(true), Some(true)) => Some(true),
            _ => None,
        }
    };
    let behavior = match format {
        MachineIntegerType::Int32 => CUndefinedBehavior::SignedDivisionOverflow,
        MachineIntegerType::Int64 => CUndefinedBehavior::SignedOverflow,
        _ => unreachable!("native signed division width"),
    };
    if known == Some(true) {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(behavior),
            facts,
            obligations,
        }];
    }
    let mut normal_facts = facts.clone();
    if known.is_none() {
        add_path_fact(&mut normal_facts, assumptions, safe)
            .expect("unknown signed division has a normal path");
    }
    let value = match format {
        MachineIntegerType::Int32 => int32(result(left, right)),
        MachineIntegerType::Int64 => CValue::Int64(result(left, right)),
        _ => unreachable!("native signed division width"),
    };
    let mut paths = vec![CExpressionPath {
        outcome: CExpressionOutcome::Value(value),
        facts: normal_facts,
        obligations: obligations.clone(),
    }];
    if known.is_none() {
        let mut bad = facts;
        add_path_fact(&mut bad, assumptions, exceptional)
            .expect("unknown signed division has an exceptional path");
        paths.push(CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(behavior),
            facts: bad,
            obligations,
        });
    }
    paths
}

#[cfg(test)]
mod tests {
    use super::*;

    fn terms() -> (Bitvector32Term, Bitvector32Term) {
        (
            Bitvector32Term::Variable(Variable(970_001)),
            Bitvector32Term::Variable(Variable(970_002)),
        )
    }
    fn result(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
        Bitvector32Term::Binary {
            format: MachineIntegerType::Int32,
            op: MachineBinaryOp::Divide,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    #[test]
    fn execution_records_an_ordinary_exclusion_and_exception_pair() {
        let (left, right) = terms();
        let domain =
            Proposition::signed_division_exclusion(MachineIntegerType::Int32, &left, &right);
        let [minimum, minus_one] = ConditionTerm::signed_division_exception_tests(
            MachineIntegerType::Int32,
            &left,
            &right,
        );
        let exceptional = Proposition::And(
            Box::new(Proposition::ConditionIs(minimum, true)),
            Box::new(Proposition::ConditionIs(minus_one, true)),
        );
        let paths = apply_nonzero(
            MachineIntegerType::Int32,
            left.clone(),
            right.clone(),
            ExecutionFacts::new(),
            vec![],
            &PureFactContext::new(),
            result,
        );
        assert_eq!(paths.len(), 2);
        assert!(matches!(paths[0].outcome, CExpressionOutcome::Value(_)));
        assert!(paths[0].facts.contains_proposition(&domain));
        assert!(matches!(
            paths[1].outcome,
            CExpressionOutcome::UndefinedBehavior(_)
        ));
        assert!(paths[1].facts.contains_proposition(&exceptional));
        let facts = PureFactContext::new().assume_proposition(domain);
        let paths = apply_nonzero(
            MachineIntegerType::Int32,
            left,
            right,
            ExecutionFacts::new(),
            vec![],
            &facts,
            result,
        );
        assert_eq!(paths.len(), 1);
        assert!(matches!(paths[0].outcome, CExpressionOutcome::Value(_)));
    }

    #[test]
    fn division_and_remainder_domains_are_ordinary_fact_stable_propositions() {
        for format in [MachineIntegerType::Int32, MachineIntegerType::Int64] {
            let (left, right) = terms();
            let wrap = |word| match format {
                MachineIntegerType::Int32 => CValue::Int32(word),
                _ => CValue::Int64(word),
            };
            for op in [MachineBinaryOp::Divide, MachineBinaryOp::Remainder] {
                let path = apply_spec_machine_arithmetic(
                    op,
                    &wrap(left.clone()),
                    &wrap(right.clone()),
                    &ExecutionFacts::new(),
                    &[],
                )
                .unwrap();
                assert_eq!(path.obligations.len(), 1);
                let conjunction = path.obligations[0].proposition().clone();
                assert_eq!(
                    conjunction,
                    Proposition::signed_division_defined(format, &left, &right)
                );
                assert!(path.obligations.iter().all(|debt| !debt.is_assumable()));
            }
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../../scaling_tests/kernel/eval/operators/division_domains.rs");
    }
}
