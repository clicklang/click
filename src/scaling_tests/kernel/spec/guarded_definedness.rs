// A conjunction reads each right operand under every conjunct before it. The
// guard context grows by one conjunct per operand, so lowering a chain is
// linear in its length, including when every conjunct owes a domain.
#[test]
fn guarded_conjunction_chains_scale_with_their_length() {
    fn work(conjuncts: u32) -> usize {
        let _session = crate::kernel::VerificationSession::enter();
        let value = |id: u32| {
            SpecExpression::Value(ProgramValue::Int32(OldMachineTerm::Variable(Variable(
                696_000 + u64::from(id),
            ))))
        };
        // `x_k + 1 > 0`: each conjunct owes its addition's domain.
        let conjunct = |k: u32| SpecProposition::Comparison {
            left: SpecExpression::Add(
                Box::new(value(k)),
                Box::new(SpecExpression::Value(crate::kernel::int32(1))),
            ),
            operator: ComparisonOperator::GreaterThan,
            right: SpecExpression::Value(crate::kernel::int32(0)),
        };
        let proposition = (0..conjuncts)
            .map(conjunct)
            .reduce(|left, right| SpecProposition::And(Box::new(left), Box::new(right)))
            .unwrap();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::program_lower_spec_proposition_with_checked_obligations(
                &ExecutionState::new(),
                &proposition,
                None,
                &PureFactContext::new(),
            )
            .unwrap()
        });
        work
    }
    let samples: Vec<_> = [4, 16, 64].map(work).into();
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5 + 256, "conjuncts: {samples:?}");
    }
}

// `defined(e)` evaluates each operand once and its root once: a nested sum's
// lowering is linear in its depth.
#[test]
fn operation_definedness_scales_with_expression_depth() {
    fn work(depth: u32) -> usize {
        let _session = crate::kernel::VerificationSession::enter();
        let mut expression = SpecExpression::Value(ProgramValue::Int32(OldMachineTerm::Variable(
            Variable(697_000),
        )));
        for _ in 0..depth {
            expression = SpecExpression::Add(
                Box::new(expression),
                Box::new(SpecExpression::Value(crate::kernel::int32(1))),
            );
        }
        let proposition = SpecProposition::OperationDefined(expression);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::program_lower_spec_proposition_with_checked_obligations(
                &ExecutionState::new(),
                &proposition,
                None,
                &PureFactContext::new(),
            )
            .unwrap()
        });
        work
    }
    let samples: Vec<_> = [4, 16, 64].map(work).into();
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5 + 256, "depth: {samples:?}");
    }
}

// A chain whose later conjuncts owe domains under more than
// `GUARDED_CONJUNCTION_LIMIT` earlier conjuncts is refused by name rather than
// lowered in time that grows faster than its length; a long chain whose
// conjuncts owe nothing is unaffected.
#[test]
fn guarded_conjunction_chains_past_the_limit_are_refused_by_name() {
    let _session = crate::kernel::VerificationSession::enter();
    let value = |id: usize| {
        SpecExpression::Value(ProgramValue::Int32(OldMachineTerm::Variable(Variable(
            698_500 + id as u64,
        ))))
    };
    let chain = |conjuncts: usize, owes: bool| {
        (0..conjuncts)
            .map(|k| SpecProposition::Comparison {
                left: if owes {
                    SpecExpression::Add(
                        Box::new(value(k)),
                        Box::new(SpecExpression::Value(crate::kernel::int32(1))),
                    )
                } else {
                    value(k)
                },
                operator: ComparisonOperator::GreaterThan,
                right: SpecExpression::Value(crate::kernel::int32(0)),
            })
            .reduce(|left, right| SpecProposition::And(Box::new(left), Box::new(right)))
            .unwrap()
    };
    let lower = |proposition: &SpecProposition| {
        crate::kernel::program_lower_spec_proposition_with_checked_obligations(
            &ExecutionState::new(),
            proposition,
            None,
            &PureFactContext::new(),
        )
    };
    let limit = crate::kernel::GUARDED_CONJUNCTION_LIMIT;
    assert!(
        lower(&chain(limit + 1, true)).is_ok(),
        "the limit itself is supported"
    );
    let refusal = lower(&chain(limit + 2, true)).unwrap_err();
    assert!(
        refusal
            .message
            .starts_with("unsupported: a conjunction reads a side"),
        "{}",
        refusal.message
    );
    assert!(
        lower(&chain(4 * limit, false)).is_ok(),
        "no domain, no guard copies"
    );
}
