#[test]
fn evaluated_sequence_handoffs_keep_growing_dags_without_exports() {
    let mut baseline = None;
    for size in [4, 16, 64, 256] {
        let _session = VerificationSession::enter();
        let atom =
            KernelTerm::variable(KernelType::Program(ProgramType::UInt32), Variable(10993406));
        let mut root = atom;
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::UInt32,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let state =
            ExecutionState::new().with_retained_local("word", ExecutionValue::Shared(root.clone()));
        let expression = SpecSequenceExpression::Literal(vec![SpecExpression::ProgramExpression(
            ProgramExpression::Variable("word".into()),
        )]);
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut execution = ExecutionBudget::default();
            let paths = evaluate_spec_sequence_at_state_in(
                SpecScope::new(&state, None, &NO_ALGEBRAIC_BINDINGS),
                &expression,
                &PureFactContext::new(),
                &mut SpecEvaluation::logical(&mut execution),
                false,
            )
            .unwrap();
            assert_eq!(paths.len(), 1);
            for _ in 0..32 {
                let sequence = paths[0].value.clone();
                let SequenceTermNode::Literal(values) = sequence.node.as_ref() else {
                    panic!("literal")
                };
                assert_eq!(values.retained_value(0).unwrap().shared(), Some(&root));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(!root.has_cached_native_argument());
        assert_eq!(work, *baseline.get_or_insert(work), "size={size}");
    }
}
#[test]
fn pure_sequence_lowering_and_checking_scale_with_selected_elements() {
    let mut previous = None;
    for size in [8, 32, 128] {
        let _session = VerificationSession::enter();
        let elements = SpecSequenceExpression::Literal(vec![SpecExpression::Value(int32(7)); size]);
        let proposition = SpecProposition::SequenceComparison {
            left: SpecSequenceExpression::Concat(
                Box::new(SpecSequenceExpression::Literal(vec![])),
                Box::new(elements.clone()),
            ),
            equal: true,
            right: elements,
        };
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut fuel = ExecutionBudget::default();
            let mut paths = lower_spec_proposition_at_state_with_algebraic_bindings_in(
                SpecScope::new(&ExecutionState::new(), None, &NO_ALGEBRAIC_BINDINGS),
                &proposition,
                &PureFactContext::new(),
                &mut SpecEvaluation::logical(&mut fuel),
            )
            .unwrap();
            let proposition = paths.pop().unwrap().proposition;
            let Proposition::Equal(Term::Sequence(left), Term::Sequence(_)) = &proposition else {
                panic!("retained sequence equality")
            };
            assert!(matches!(left.node.as_ref(), SequenceTermNode::Concat(..)));
            assert_eq!(int32_sequence_equalities(&proposition).unwrap().len(), size);
        });
        if let Some(previous) = previous {
            assert!(
                work <= 5 * previous,
                "size={size}, work={work}, previous={previous}"
            );
        }
        previous = Some(work);
    }
}
#[test]
fn pure_membership_visits_only_the_selected_sequence() {
    let mut previous = None;
    for size in [8, 32, 128] {
        let _session = VerificationSession::enter();
        let sequence = SpecSequenceExpression::Literal(vec![SpecExpression::Value(int32(7)); size]);
        let proposition = SpecProposition::SequenceMembership {
            element: SpecExpression::Value(int32(8)),
            sequence,
        };
        let (proposition, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut fuel = ExecutionBudget::default();
            let mut paths = lower_spec_proposition_at_state_with_algebraic_bindings_in(
                SpecScope::new(&ExecutionState::new(), None, &NO_ALGEBRAIC_BINDINGS),
                &proposition,
                &PureFactContext::new(),
                &mut SpecEvaluation::logical(&mut fuel),
            )
            .unwrap();
            let proposition = paths.pop().unwrap().proposition;
            assert!(matches!(
                &proposition,
                Proposition::SequenceMembership { .. }
            ));
            assert!(crate::kernel::reasoning::path_facts::disprove_builtin_prop(
                &proposition
            ));
            proposition
        });
        if let Some(previous) = previous {
            assert!(
                work <= 5 * previous,
                "size={size}, work={work}, previous={previous}"
            );
        }
        previous = Some(work);
        let goal = Proposition::Not(Box::new(proposition));
        let ambient = (0..size).fold(PureFactContext::new(), |facts, n| {
            facts.assume_condition(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(1000 + n as u64)),
                    MachineTerm::constant(0),
                ),
                true,
            )
        });
        let check = |context: &PureFactContext| {
            crate::instrumentation::measure_deterministic_work(|| context.contains_known(&goal))
        };
        let (empty, empty_work) = check(&PureFactContext::new());
        let (with_ambient, ambient_work) = check(&ambient);
        assert!(empty && with_ambient);
        assert_eq!(empty_work, ambient_work);
    }
}
