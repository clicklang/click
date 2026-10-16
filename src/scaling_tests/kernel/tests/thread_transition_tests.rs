// Scaling tests of `src/kernel/tests/thread_transition_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn pending_status_resolution_scales_with_explicit_intervening_work() {
    let status = Bitvector32Term::Variable(Variable(890_000));
    let zero = ConditionTerm::Bitvector32Equal(
        Box::new(status.clone()),
        Box::new(Bitvector32Term::Constant(0)),
    );
    let success_assumptions =
        PureFactContext::new().assume_proposition(Proposition::ConditionIs(zero.clone(), true));
    let failure_assumptions =
        PureFactContext::new().assume_proposition(Proposition::ConditionIs(zero, false));
    let base = parent(1);
    let mut samples = Vec::new();
    for size in [8usize, 16, 32, 64] {
        let mut pending = PendingThreadCreate::new(
            status.clone(),
            Pointer::null(),
            CValue::UInt64(Bitvector32Term::UInt64Constant(0)),
            &base,
            &base,
        );
        let mut visible = base.clone();
        for index in 0..size {
            let value = int32(index as u32);
            visible.set_memory(visible.memory().clone().store(pointer(0), value.clone()));
            pending = pending.with_delta(crate::kernel::threads::PendingThreadMemoryDelta::Store {
                pointer: pointer(0),
                value,
            });
        }
        let failed = pending.resolve(&visible, &failure_assumptions).unwrap();
        assert_eq!(failed.memory(), visible.memory());
        let (resolved, work) = crate::instrumentation::measure_deterministic_work(|| {
            pending.resolve(&visible, &success_assumptions).unwrap()
        });
        assert_eq!(
            resolved.memory().load(&pointer(0)),
            CExpressionOutcome::Value(int32((size - 1) as u32))
        );
        assert!(work >= size);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 3,
            "pending resolution grew faster than explicit work: {samples:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn thread_recovery_work_depends_on_one_child_not_the_outstanding_registry() {
    let (worker, termination) = worker();
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [8, 16, 32, 64] {
        let mut context = ThreadContext::new(parent(size)).unwrap();
        let mut budget = ExecutionBudget::new();
        let mut handles = Vec::new();
        for index in 0..size {
            let (next, handle) = spawn(&context, index, &worker, &termination, &mut budget);
            context = next;
            handles.push(handle);
        }
        let ((next, _), work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .join(
                    handles[0],
                    JoinRuntimeAssumption::ValidJoinSucceeds,
                    &assumptions,
                )
                .unwrap()
        });
        assert!(work > 0);
        samples.push((size, work));
        // The last child's loan must survive even the oldest child's join.
        assert!(
            next.parent()
                .loan_ledger()
                .unwrap()
                .memory_access_refusal(
                    &range(size - 1, 1, 2),
                    &assumptions,
                    crate::kernel::LoanRefusalOperation::MemoryAccess,
                )
                .is_some()
        );
    }
    assert!(
        samples.last().unwrap().1 <= samples[0].1 * 2,
        "joining one child must not scan the ambient ledger/frame: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn joining_one_of_many_shared_readers_touches_only_its_share_branch() {
    let function = c_function(
        CType::Int32,
        "thread_reader",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_load(c_variable("p"))),
    )
    .with_resource_summary(
        vec![CResourceSpec::viewed_memory(CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(0),
            c_int32_literal(1),
        ))],
        vec![],
    )
    .with_contract(
        vec![],
        vec![],
        vec![],
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let (reader, termination) = certify_worker(function.clone());
    let view = CResourceFact::view_memory(range(0, 0, 1));
    let state = c_state_with_borrowed_contract_inputs(
        parent(1).with_resource_context(ResourceContext::new().unchecked_with_fact(view.clone())),
        &function,
        &[c_pointer_value(pointer(0))],
        &PureFactContext::new(),
    )
    .unwrap();
    let occurrence = state.resources().occurrences_for_fact(&view)[0];
    let root_binding = state.loan_view_bindings().get(&occurrence).unwrap().clone();
    let mut samples = Vec::new();
    for size in [8, 16, 32, 64] {
        let mut context = ThreadContext::new(state.clone()).unwrap();
        let mut handles = Vec::new();
        let mut budget = ExecutionBudget::new();
        for _ in 0..size {
            let (next, handle) = spawn(&context, 0, &reader, &termination, &mut budget);
            context = next;
            handles.push(handle);
        }
        let ((next, _), work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .join(
                    handles[0],
                    JoinRuntimeAssumption::ValidJoinSucceeds,
                    &PureFactContext::new(),
                )
                .unwrap()
        });
        samples.push((size, work));
        context = next;
        for handle in handles.into_iter().skip(1) {
            context = context
                .join(
                    handle,
                    JoinRuntimeAssumption::ValidJoinSucceeds,
                    &PureFactContext::new(),
                )
                .unwrap()
                .0;
        }
        assert_eq!(
            context.parent().loan_view_bindings().get(&occurrence),
            Some(&root_binding)
        );
    }
    assert!(
        samples.last().unwrap().1 <= samples[0].1 * 3,
        "joining a fixed shared reader scanned unrelated children: {samples:?}"
    );
}
