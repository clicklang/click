use super::*;
use crate::kernel::program_expression::{add, equal, int32_literal, less_than, variable};
use crate::kernel::program_loop_regions;
use std::sync::Arc;

#[test]
fn shared_update_runs_once_on_fallthrough_and_continue() {
    let state = ExecutionState::new()
        .with_local("i", int32(0))
        .with_local("visits", int32(0))
        .with_local("updates", int32(0));
    let statement = program_while(
        less_than(variable("i"), int32_literal(3)),
        Vec::new(),
        program_if(
            equal(variable("i"), int32_literal(1)),
            ProgramStatement::Continue,
            program_assign("visits", add(variable("visits"), int32_literal(1))),
        ),
    )
    .with_loop_update(program_seq(
        program_assign("i", add(variable("i"), int32_literal(1))),
        program_assign("updates", add(variable("updates"), int32_literal(1))),
    ));
    let outcome = crate::kernel::eval::execute_execution_statement(
        &state,
        &statement,
        &PureFactContext::new(),
    )
    .expect("bounded loop executes");
    let StatementOutcome::Normal(state) = outcome else {
        panic!("{outcome:?}");
    };
    for (name, expected) in [("i", 3), ("visits", 2), ("updates", 3)] {
        assert_eq!(
            state.locals.get_native(name).as_deref(),
            Some(&int32(expected)),
            "{name}"
        );
    }
}

#[test]
fn shared_update_is_skipped_by_break_and_return() {
    for body in [ProgramStatement::Break, program_return(int32_literal(7))] {
        let state = ExecutionState::new().with_local("updates", int32(0));
        let statement = program_while(int32_literal(1), Vec::new(), body)
            .with_loop_update(program_assign("updates", int32_literal(1)));
        let outcome = crate::kernel::eval::execute_execution_statement(
            &state,
            &statement,
            &PureFactContext::new(),
        )
        .expect("exiting loop executes");
        let state = match outcome {
            StatementOutcome::Normal(state) | StatementOutcome::Return { state, .. } => state,
            outcome => panic!("{outcome:?}"),
        };
        assert_eq!(
            state.locals.get_native("updates").as_deref(),
            Some(&int32(0))
        );
    }
}

#[test]
fn shared_post_test_runs_once_after_a_switch_continue() {
    let state = ExecutionState::new().with_local("tests", int32(0));
    let body = program_switch(
        int32_literal(0),
        vec![SwitchCase {
            value: Some(0),
            body: Box::new(ProgramStatement::Continue),
        }],
    );
    let test = program_seq(
        program_assign("tests", add(variable("tests"), int32_literal(1))),
        ProgramStatement::LoopTest {
            aggregate_steps: Vec::new(),
            condition: less_than(variable("tests"), int32_literal(3)),
        },
    );
    let statement = program_while(int32_literal(1), Vec::new(), body)
        .with_loop_test(test, LoopTestPosition::AfterBody);
    let outcome = crate::kernel::eval::execute_execution_statement(
        &state,
        &statement,
        &PureFactContext::new(),
    )
    .expect("post-test loop executes");
    let StatementOutcome::Normal(state) = outcome else {
        panic!("{outcome:?}");
    };
    assert_eq!(state.locals.get_native("tests").as_deref(), Some(&int32(3)));
}

mod scaling_tests {
    use super::*;
    include!("../../scaling_tests/kernel/loops/shared_update.rs");
}

#[test]
fn direct_and_prepared_tests_keep_placement_and_continue_semantics() {
    for position in [LoopTestPosition::BeforeBody, LoopTestPosition::AfterBody] {
        for prepared in [false, true] {
            for initial in [0, 3] {
                let state = ExecutionState::new()
                    .with_local("i", int32(initial))
                    .with_local("visits", int32(0))
                    .with_local("tests", int32(0));
                let condition = less_than(variable("i"), int32_literal(3));
                let body = program_switch(
                    int32_literal(0),
                    vec![SwitchCase {
                        value: Some(0),
                        body: Box::new(ProgramStatement::Continue),
                    }],
                );
                let statement = match position {
                    LoopTestPosition::BeforeBody => {
                        program_while(condition.clone(), Vec::new(), body)
                    }
                    LoopTestPosition::AfterBody => program_do_while(condition.clone(), body),
                }
                .with_loop_update(program_seq(
                    program_assign("i", add(variable("i"), int32_literal(1))),
                    program_assign("visits", add(variable("visits"), int32_literal(1))),
                ));
                let statement = if prepared {
                    statement.with_loop_test(
                        program_seq(
                            program_assign("tests", add(variable("tests"), int32_literal(1))),
                            ProgramStatement::LoopTest {
                                condition,
                                aggregate_steps: Vec::new(),
                            },
                        ),
                        position,
                    )
                } else {
                    statement
                };
                let ProgramStatement::Loop { test, .. } = &statement else {
                    unreachable!()
                };
                assert_eq!(test.position, position);
                let outcome = crate::kernel::eval::execute_execution_statement(
                    &state,
                    &statement,
                    &PureFactContext::new(),
                )
                .expect("both test forms execute the same bounded loop");
                let StatementOutcome::Normal(state) = outcome else {
                    panic!("{outcome:?}")
                };
                let visits = if initial == 0 {
                    3
                } else if position == LoopTestPosition::AfterBody {
                    1
                } else {
                    0
                };
                let tests = if !prepared {
                    0
                } else if position == LoopTestPosition::BeforeBody {
                    visits + 1
                } else {
                    visits
                };
                for (name, expected) in [
                    ("i", initial + visits),
                    ("visits", visits),
                    ("tests", tests),
                ] {
                    assert_eq!(
                        state.locals.get_native(name).as_deref(),
                        Some(&int32(expected)),
                        "{position:?}, prepared={prepared}, initial={initial}, {name}"
                    );
                }
            }
        }
    }
}

#[test]
fn loop_test_false_is_distinct_from_break_and_propagates_to_its_loop() {
    let state = ExecutionState::new().with_local("after", int32(0));
    let test = ProgramStatement::LoopTest {
        condition: int32_literal(0),
        aggregate_steps: Vec::new(),
    };
    let evaluate = |statement: &ProgramStatement| {
        crate::kernel::eval::execute_execution_statement(&state, statement, &PureFactContext::new())
            .expect("one checked successor")
    };
    assert!(matches!(
        evaluate(&test),
        StatementOutcome::LoopTestFalse(_)
    ));
    assert!(matches!(
        evaluate(&ProgramStatement::Break),
        StatementOutcome::Break(_)
    ));
    let true_test = ProgramStatement::LoopTest {
        condition: int32_literal(1),
        aggregate_steps: Vec::new(),
    };
    assert!(matches!(evaluate(&true_test), StatementOutcome::Normal(_)));

    // A switch consumes its own written break, but must preserve a test exit.
    let switch = |body| {
        program_switch(
            int32_literal(0),
            vec![SwitchCase {
                value: Some(0),
                body: Box::new(body),
            }],
        )
    };
    assert!(matches!(
        evaluate(&switch(ProgramStatement::Break)),
        StatementOutcome::Normal(_)
    ));
    let pass = program_seq(switch(test), program_assign("after", int32_literal(1)));
    let StatementOutcome::LoopTestFalse(exited) = evaluate(&pass) else {
        panic!("the switch and sequence must preserve the test's exit reason");
    };
    assert_eq!(
        exited.locals.get_native("after").as_deref(),
        Some(&int32(0))
    );
    let loop_statement = program_while(int32_literal(1), Vec::new(), pass)
        .with_loop_update(program_assign("after", int32_literal(2)));
    let StatementOutcome::Normal(exited) = evaluate(&loop_statement) else {
        panic!("the loop consumes its own test exit");
    };
    assert_eq!(
        exited.locals.get_native("after").as_deref(),
        Some(&int32(0))
    );
}

#[test]
fn every_loop_test_is_a_phase_and_post_tests_keep_their_placement() {
    for position in [LoopTestPosition::BeforeBody, LoopTestPosition::AfterBody] {
        for prepared in [false, true] {
            let decision = Arc::new(ProgramStatement::LoopTest {
                condition: int32_literal(0),
                aggregate_steps: Vec::new(),
            });
            let test = LoopTestRegion {
                position,
                statement: if prepared {
                    Arc::new(ProgramStatement::seq(
                        Arc::new(program_assign("tested", int32_literal(1))),
                        decision,
                    ))
                } else {
                    decision
                },
            };
            let body = program_assign("visited", int32_literal(1));
            let regions = program_loop_regions(&body, None, Some(&test)).collect::<Vec<_>>();
            assert_eq!(regions.len(), 2, "every pass includes its actual test");
            let test_index = usize::from(position == LoopTestPosition::AfterBody);
            assert!(std::ptr::eq(regions[test_index], test.statement.as_ref()));
            let statement = program_while(int32_literal(1), Vec::new(), body)
                .with_loop_test((*test.statement).clone(), position);
            let state = ExecutionState::new()
                .with_local("visited", int32(0))
                .with_local("tested", int32(0));
            let StatementOutcome::Normal(exit) = crate::kernel::eval::execute_execution_statement(
                &state,
                &statement,
                &PureFactContext::new(),
            )
            .unwrap() else {
                panic!("the false test exits its loop");
            };
            assert_eq!(
                exit.locals.get_native("visited").as_deref(),
                Some(&int32(u32::from(position == LoopTestPosition::AfterBody)))
            );
            assert_eq!(
                exit.locals.get_native("tested").as_deref(),
                Some(&int32(u32::from(prepared)))
            );
            let ProgramStatement::Loop { test: retained, .. } = statement else {
                unreachable!()
            };
            assert_eq!(retained.position, position);
        }
    }
}

#[test]
fn a_false_pre_test_does_not_exit_the_unentered_body_scope() {
    let state = ExecutionState::new().with_local("kept", int32(7));
    let statement = program_while(
        int32_literal(0),
        Vec::new(),
        program_declare("kept", ProgramType::Int32),
    );
    let StatementOutcome::Normal(exit) = crate::kernel::eval::execute_execution_statement(
        &state,
        &statement,
        &PureFactContext::new(),
    )
    .unwrap() else {
        panic!("the false test exits");
    };
    assert_eq!(exit.locals.get_native("kept").as_deref(), Some(&int32(7)));
}
