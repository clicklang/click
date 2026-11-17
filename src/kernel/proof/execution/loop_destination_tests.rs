use super::*;
use crate::kernel::program_expression::{int32_literal, variable};
use crate::kernel::{
    ProgramType, int32, program_assign, program_do_while, program_seq, program_while,
};

struct NestedLoop {
    core: ExecutionProofCore,
    function: ProgramFunction,
    state: ExecutionState,
    control: ProgramStatement,
    repeat: Arc<ProgramStatement>,
    after_inner: Arc<ProgramStatement>,
    outer: Arc<ProgramStatement>,
    after_function: Arc<ProgramStatement>,
    update: Option<Arc<ProgramStatement>>,
}

fn enter_loop(
    core: &mut ExecutionProofCore,
    function: &ProgramFunction,
    state: &ExecutionState,
) -> LoopControlSources {
    let sources = core
        .enter_loop_phases(function, &[])
        .expect("the source loop enters its phases");
    if let Some((next, _)) = core.next_source_statement_and_tail(function)
        && matches!(next.as_ref(), ProgramStatement::LoopTest { .. })
    {
        let statement = next.into_owned();
        core.record_statement_transition_native(
            function,
            &[],
            Theorem::new(Proposition::ProgramStatementVerifies {
                state: Box::new(state.clone()),
                statement: Box::new(statement),
                outcome: StatementOutcome::Normal(Box::new(state.clone())),
            }),
            PureFactContext::new(),
            &ExecutionFacts::new(),
            &[],
            &crate::kernel::loans::empty_checked_loan_evidence_sequence(),
        )
        .expect("the entered test is true");
    }
    sources
}

fn nested_loop(
    continuing: bool,
    post_test: bool,
    with_update: bool,
    body_size: usize,
    tail_size: usize,
    parent_frames: usize,
    inside_try: bool,
) -> NestedLoop {
    let control = if continuing {
        ProgramStatement::Continue
    } else {
        ProgramStatement::Break
    };
    let body = if inside_try {
        ProgramStatement::TryCatchInt32 {
            try_body: Box::new(control.clone()),
            binding: "caught".into(),
            handler: Box::new(ProgramStatement::Skip),
        }
    } else {
        control.clone()
    };
    let suffix = (0..body_size).fold(ProgramStatement::Skip, |rest, _| {
        program_seq(program_assign("unreached", int32_literal(9)), rest)
    });
    let body = program_seq(body, suffix);
    let update = with_update.then(|| Arc::new(program_assign("gate", int32_literal(1))));
    let make_inner = |post| {
        let statement = if post {
            program_do_while(variable("gate"), body.clone())
        } else {
            program_while(variable("gate"), Vec::new(), body.clone())
        };
        match &update {
            Some(update) => statement.with_loop_update((**update).clone()),
            None => statement,
        }
    };
    let repeat = Arc::new(make_inner(post_test));
    let after_inner = Arc::new((0..tail_size).fold(
        program_assign("after_inner", int32_literal(7)),
        |rest, _| program_seq(program_assign("after_inner", int32_literal(7)), rest),
    ));
    let outer = Arc::new(program_while(
        variable("gate"),
        Vec::new(),
        ProgramStatement::seq(Arc::new(make_inner(post_test)), after_inner.clone()),
    ));
    let after_function = Arc::new(ProgramStatement::Return(ProgramExpression::Value(
        ProgramValue::Void,
    )));
    let source = Arc::new(ProgramStatement::seq(outer.clone(), after_function.clone()));
    let function = ProgramFunction::new(
        ProgramType::Void,
        "nested_destinations",
        Vec::new(),
        (*source).clone(),
    );
    let state = ExecutionState::new().with_local("gate", int32(1));
    let mut core = ExecutionProofCore::at_entry(
        state.clone(),
        ExecutionFrontier {
            position: FrontierPosition::StatementEntry { remaining: source },
            ..ExecutionFrontier::default()
        },
    );
    // These scopes belong outside the selected loops and must not be visited
    // or retired by an inner-loop transfer.
    for index in 0..parent_frames {
        core.frontier
            .continuations
            .push(ProofExecutionContinuation {
                loop_control: None,
                remaining: Some(after_function.clone()),
                next_statement_index: 100 + index,
                exceptional: None,
            });
    }
    let outer_sources = enter_loop(&mut core, &function, &state);
    core.frontier.continuations.push(
        ProofExecutionContinuation::loop_body(
            Arc::new(ProgramStatement::seq(outer.clone(), after_function.clone())),
            0,
            Some(after_function.clone()),
            90,
            None,
            outer_sources,
        )
        .expect("outer loop destination"),
    );
    let inner_sources = enter_loop(&mut core, &function, &state);
    let continuation = inner_sources.continuation.clone();
    core.frontier.continuations.push(
        ProofExecutionContinuation::loop_body(
            Arc::new(ProgramStatement::seq(repeat.clone(), after_inner.clone())),
            1,
            Some(after_inner.clone()),
            2,
            continuation.as_ref().map(|_| 3),
            inner_sources,
        )
        .expect("inner loop destination"),
    );
    if inside_try {
        core.frontier
            .continuations
            .push(ProofExecutionContinuation {
                loop_control: None,
                remaining: None,
                next_statement_index: 4,
                exceptional: Some(ExceptionalContinuation {
                    entry: ExceptionalEntry::Catch("caught".into()),
                    handler: Arc::new(ProgramStatement::Skip),
                    handler_first_index: 5,
                }),
            });
    }
    NestedLoop {
        core,
        function,
        state,
        control,
        repeat,
        after_inner,
        outer,
        after_function,
        update: continuation,
    }
}

fn transfer(fixture: &mut NestedLoop, continuing: bool) {
    let outcome = if continuing {
        StatementOutcome::Continue(Box::new(fixture.state.clone()))
    } else {
        StatementOutcome::Break(Box::new(fixture.state.clone()))
    };
    fixture
        .core
        .record_statement_transition_native(
            &fixture.function,
            &[],
            Theorem::new(Proposition::ProgramStatementVerifies {
                state: Box::new(fixture.state.clone()),
                statement: Box::new(fixture.control.clone()),
                outcome,
            }),
            PureFactContext::new(),
            &ExecutionFacts::new(),
            &[],
            &crate::kernel::loans::empty_checked_loan_evidence_sequence(),
        )
        .expect("the checked transfer follows its recorded destination");
}

fn source_heads(mut source: Option<Arc<ProgramStatement>>) -> Vec<ProgramStatement> {
    let mut heads = Vec::new();
    while let Some(current) = source {
        let (head, tail) = split_shared_source(&current);
        heads.push(head.into_owned());
        source = tail;
    }
    heads
}

fn assert_destination(fixture: &NestedLoop, continuing: bool, parent_frames: usize) {
    let mut expected = Vec::new();
    if continuing {
        if let Some(update) = &fixture.update {
            expected.extend(source_heads(Some(update.clone())));
        }
        expected.push((*fixture.repeat).clone());
    }
    expected.extend(source_heads(Some(fixture.after_inner.clone())));
    expected.push((*fixture.outer).clone());
    expected.push((*fixture.after_function).clone());
    assert_eq!(
        source_heads(fixture.core.evidence_source.clone()),
        expected,
        "the destination must preserve both enclosing loop and function tails"
    );
    assert_eq!(
        fixture.core.frontier.next_statement_index,
        if continuing {
            if fixture.update.is_some() { 3 } else { 1 }
        } else {
            2
        }
    );
    assert_eq!(
        fixture.core.frontier.continuations.len(),
        parent_frames + 1 + usize::from(continuing && fixture.update.is_some())
    );
    assert!(
        fixture.core.evidence_try_stack.is_empty(),
        "the transfer leaves the inner try"
    );
}

#[test]
fn loop_control_preserves_enclosing_sources_and_exits_inner_try_scopes() {
    for continuing in [false, true] {
        for post_test in [false, true] {
            for with_update in [false, true] {
                for inside_try in [false, true] {
                    let mut fixture =
                        nested_loop(continuing, post_test, with_update, 2, 2, 2, inside_try);
                    transfer(&mut fixture, continuing);
                    assert_destination(&fixture, continuing, 2);
                }
            }
        }
    }
}

#[test]
fn loop_entry_refuses_an_if_source_without_advancing_evidence() {
    let state = ExecutionState::new().with_local("gate", int32(1));
    let statement = Arc::new(crate::kernel::program_if(
        variable("gate"),
        ProgramStatement::Skip,
        ProgramStatement::Skip,
    ));
    let function = ProgramFunction::new(
        ProgramType::Void,
        "wrong_loop_source",
        Vec::new(),
        (*statement).clone(),
    );
    let mut core = ExecutionProofCore::at_entry(
        state.clone(),
        ExecutionFrontier {
            position: FrontierPosition::StatementEntry {
                remaining: statement.clone(),
            },
            ..ExecutionFrontier::default()
        },
    );
    assert!(core.enter_loop_phases(&function, &[]).is_err());
    assert!(core.evidence_state.is_none());
    assert!(core.evidence_source.is_none());
    assert_eq!(core.current_source(&function), Some(statement.as_ref()));
}

mod scaling_tests {
    use super::*;
    include!("../../../scaling_tests/kernel/proof/execution/loop_destinations.rs");
}

#[test]
fn test_false_and_written_break_keep_distinct_checked_region_exits() {
    for (control, expected) in [
        (
            ProgramStatement::LoopTest {
                condition: int32_literal(0),
                aggregate_steps: Vec::new(),
            },
            LoopControlExit::TestFalse,
        ),
        (ProgramStatement::Break, LoopControlExit::Break),
    ] {
        let state = ExecutionState::new();
        let outcome = crate::kernel::eval::execute_execution_statement(
            &state,
            &control,
            &PureFactContext::new(),
        )
        .expect("the evaluator produces the control outcome");
        let function = ProgramFunction::new(
            ProgramType::Void,
            "control_reason",
            Vec::new(),
            control.clone(),
        );
        let mut core = ExecutionProofCore::at_entry(
            state.clone(),
            ExecutionFrontier {
                region: ExecutionRegionKind::LoopBody,
                position: FrontierPosition::StatementEntry {
                    remaining: Arc::new(control.clone()),
                },
                ..ExecutionFrontier::default()
            },
        );
        core.record_statement_transition_native(
            &function,
            &[],
            Theorem::new(Proposition::ProgramStatementVerifies {
                state: Box::new(state),
                statement: Box::new(control),
                outcome,
            }),
            PureFactContext::new(),
            &ExecutionFacts::new(),
            &[],
            &crate::kernel::loans::empty_checked_loan_evidence_sequence(),
        )
        .expect("the checked boundary retains the explicit exit reason");
        assert_eq!(core.frontier.loop_control, expected);
        assert!(matches!(
            core.frontier.position,
            FrontierPosition::RegionBoundary
        ));
    }
}

#[test]
fn loop_phase_entry_retains_the_original_loop_and_records_no_skip() {
    for position in [
        crate::kernel::LoopTestPosition::BeforeBody,
        crate::kernel::LoopTestPosition::AfterBody,
    ] {
        let statement = program_while(variable("gate"), Vec::new(), ProgramStatement::Break)
            .with_loop_test(
                ProgramStatement::LoopTest {
                    condition: variable("gate"),
                    aggregate_steps: Vec::new(),
                },
                position,
            );
        let function = ProgramFunction::new(
            ProgramType::Void,
            "phase_entry",
            Vec::new(),
            statement.clone(),
        );
        let state = ExecutionState::new().with_local("gate", int32(1));
        let mut core = ExecutionProofCore::at_entry(
            state,
            ExecutionFrontier {
                position: FrontierPosition::StatementEntry {
                    remaining: Arc::new(statement.clone()),
                },
                ..ExecutionFrontier::default()
            },
        );
        let sources = core.enter_loop_phases(&function, &[]).unwrap();
        assert_eq!(
            sources.repeat.as_ref(),
            &statement,
            "entry must not rewrite a post-test loop"
        );
        let events = &core.execution_evidence[0].events;
        assert_eq!(events.len(), 1);
        assert!(matches!(
            events.last(),
            Some(CheckedExecutionEvent::LoopEntry { .. })
        ));
        assert!(
            !events
                .iter()
                .any(|event| matches!(event, CheckedExecutionEvent::Statement(_)))
        );
    }
}
