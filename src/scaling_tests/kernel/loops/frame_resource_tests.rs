// Scaling coverage for rebuilding a loop's retained frame in kernel/loops.rs.
use super::*;

#[test]
fn a_loop_frame_normalizes_its_retained_views_once() {
    let mut samples = Vec::new();
    for count in [4u64, 8, 16, 32, 64] {
        let assumptions = PureFactContext::new();
        let state = ExecutionState::new();
        let views = (0..count)
            .map(|index| {
                CResourceFact::view_memory(CMemoryRange::new(
                    Pointer::symbolic(Variable(9_360_000 + index)),
                    MachineTerm::constant(0),
                    MachineTerm::constant(1),
                ))
            })
            .collect::<Vec<_>>();
        let withheld = views
            .iter()
            .cloned()
            .fold(ResourceContext::new(), |resources, fact| {
                resources.unchecked_with_fact(fact)
            });
        let (body, work) = crate::instrumentation::measure_deterministic_work(|| {
            with_loop_frame_resources(
                ResourceContext::new(),
                &withheld,
                true,
                &state,
                &assumptions,
                &state,
            )
        });
        assert_eq!(body.facts().len(), views.len());
        for view in &views {
            assert!(body.contains_exact_representation(view));
        }
        let hidden = with_loop_frame_resources(
            ResourceContext::new(),
            &withheld,
            false,
            &state,
            &assumptions,
            &state,
        );
        assert!(
            hidden.facts().is_empty(),
            "an explicit view interface hides undeclared frame views"
        );
        samples.push((count, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1.saturating_mul(3) + 64, "{samples:?}");
    }
}

/// Keep one declared loop view fixed. Measure the binding-copy block as well
/// as its real checking caller, without charging fixture/index construction.
#[test]
fn loop_binding_carryover_ignores_ambient_observations() {
    use crate::kernel::loans::{LoanLedger, LoanViewBinding, LoanViewBindings};

    let mut curves = Vec::new();
    for case in ["early", "late", "unbound", "retained_metadata"] {
        let mut samples = Vec::new();
        for count in [4usize, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let assumptions = PureFactContext::new();
            let pointer = PointerValue::new(
                Pointer::symbolic(Variable(9_370_001)),
                ProgramType::Int32Pointer,
            );
            let view = CResourceFact::view_memory(CMemoryRange::from_pointer_value(
                &pointer,
                0u32.into(),
                8u32.into(),
                4,
            ));
            let spec = CResourceSpec::viewed_memory(CMemorySegment::new(
                ProgramExpression::Value(ProgramValue::Pointer(pointer)),
                ProgramExpression::Value(ProgramValue::Int32(0u32.into())),
                ProgramExpression::Value(ProgramValue::Int32(8u32.into())),
            ));
            let observations = if case == "retained_metadata" {
                1
            } else {
                count + 1
            };
            let (resources, occurrences) = ResourceContext::new_with_equalities(&assumptions)
                .unchecked_with_facts_and_occurrences(std::iter::repeat_n(
                    view.clone(),
                    observations,
                ));
            let selected = occurrences[if case == "late" { count } else { 0 }].1;
            let ledger = LoanLedger::new();
            let holder = ledger.fresh_participant().unwrap();
            let opening = ledger
                .borrowed_contract_input(holder, selected, view.clone(), None)
                .unwrap();
            let ledger = ledger.apply(&opening.transition).unwrap();
            let binding = LoanViewBinding {
                loan: opening.loan,
                scope: opening.scope,
                share: opening.root_share,
                support: selected,
                viewed: view.clone(),
                hold: None,
            };
            let mut bindings = LoanViewBindings::default();
            if case != "unbound" {
                bindings = bindings.with_inserted(selected, binding.clone());
            }
            if case == "retained_metadata" {
                for _ in 0..count {
                    let (_, old) =
                        ResourceContext::new().unchecked_with_facts_and_occurrences([view.clone()]);
                    bindings = bindings.with_inserted(old[0].1, binding.clone());
                }
            }
            let entry = ExecutionState::new()
                .with_resource_context(resources)
                .with_loan_ledger(Some(ledger))
                .with_loan_participant(Some(holder))
                .with_loan_view_bindings(bindings.clone());
            entry
                .resources()
                .synchronize_memory_equalities(&assumptions);
            let (body_resources, body_occurrences) =
                ResourceContext::new_with_equalities(&assumptions)
                    .unchecked_with_facts_and_occurrences([view.clone()]);
            body_resources.synchronize_memory_equalities(&assumptions);
            let body_occurrence = body_occurrences[0].1;
            let specs = [spec];
            let mut queries = Vec::new();
            for _ in 0..3 {
                let ((carried, work), maps) = crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        let destination = bindings.attach_to_inserted_views(
                            entry.resources(),
                            body_resources.clone(),
                            &body_occurrences,
                            &assumptions,
                        );
                        LoanViewBindings::from_state(destination.loan_dependency_state())
                    })
                });
                assert_eq!(
                    carried.get(&body_occurrence),
                    (case != "unbound").then_some(&binding)
                );
                let ((result, call_work), call_maps) =
                    crate::persistent::measure_persistent_work(|| {
                        crate::instrumentation::measure_deterministic_work(|| {
                            loop_body_resource_context(
                                &entry,
                                &entry,
                                &specs,
                                &[],
                                &assumptions,
                                &mut ExecutionBudget::default(),
                            )
                        })
                    });
                let (body, failures) = result.expect("construct the loop body");
                assert!(failures.is_empty(), "{case}/{count}: {failures:?}");
                let held = body
                    .resources()
                    .view_occurrences_for_fact(&view, &assumptions);
                assert_eq!(
                    held.len(),
                    1,
                    "one declared body view, independent of frame size"
                );
                assert_eq!(
                    body.loan_view_bindings().get(&held[0]),
                    (case != "unbound").then_some(&binding)
                );
                assert_ne!(
                    held[0], selected,
                    "loop construction allocated the body occurrence"
                );
                assert_eq!(
                    entry.loan_view_bindings(),
                    &bindings,
                    "the entry branch is unchanged"
                );
                queries.push((work, maps, call_work, call_maps));
            }
            samples.push((count, queries));
        }
        eprintln!(
            "loop binding {case} (count; copy work/maps, whole constructor work/maps): {samples:?}"
        );
        curves.push((case, samples));
    }
    for (case, samples) in curves {
        assert!(
            samples[3]
                .1
                .iter()
                .zip(&samples[0].1)
                .all(|(large, small)| {
                    large.0 <= small.0 + 64
                        && large.1 <= small.1 * 3 + 128
                        && large.2 <= small.2 + 64
                        && large.3 <= small.3 * 3 + 512
                }),
            "loop binding carryover walks ambient state ({case}): {samples:?}"
        );
    }
}

#[test]
fn explicit_loop_views_keep_scalar_owners_without_visiting_observations() {
    let mut samples = Vec::new();
    for count in [4u64, 16, 64, 256] {
        let assumptions = PureFactContext::new();
        let scalar = Pointer::symbolic(Variable(9_380_001));
        let heap = Pointer::symbolic(Variable(9_380_002));
        let scalar_owner =
            CResourceFact::own_memory(CMemoryRange::new(scalar.clone(), 0u32.into(), 4u32.into()));
        let heap_owner =
            CResourceFact::own_memory(CMemoryRange::new(heap, 0u32.into(), 4u32.into()));
        let state = ExecutionState::new().with_memory(CMemory::new().with_declared_scalar_block(
            scalar.block,
            4,
            ProgramType::Int32,
        ));
        let mut withheld = ResourceContext::new_with_equalities(&assumptions)
            .unchecked_with_fact(scalar_owner.clone())
            .unchecked_with_fact(heap_owner.clone());
        for index in 0..count {
            withheld = withheld.unchecked_with_fact(CResourceFact::view_memory(CMemoryRange::new(
                Pointer::symbolic(Variable(9_381_000 + index)),
                0u32.into(),
                4u32.into(),
            )));
        }
        withheld.synchronize_memory_equalities(&assumptions);
        let ((body, work), maps) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                with_loop_frame_resources(
                    ResourceContext::new_with_equalities(&assumptions),
                    &withheld,
                    false,
                    &state,
                    &assumptions,
                    &state,
                )
            })
        });
        assert!(body.contains_exact_representation(&scalar_owner));
        assert!(!body.contains_exact_representation(&heap_owner));
        assert_eq!(body.facts().len(), 1);
        samples.push((count, work, maps));
    }
    let small = samples[0];
    let large = samples[3];
    assert!(large.1 <= small.1 + 16, "{samples:?}");
    assert!(large.2 <= small.2 * 3 + 64, "{samples:?}");
}

/// Fixed loop interface and fixed output: one retained scalar owner plus one
/// declared view. Extra heap owners are withheld and must not enter the body.
#[test]
fn explicit_loop_frame_ignores_rejected_heap_owners() {
    let mut curves = Vec::new();
    for count in [4u64, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let facts = PureFactContext::new();
        let scalar = Pointer::symbolic(Variable(9_390_001));
        let viewed = PointerValue::new(
            Pointer::symbolic(Variable(9_390_002)),
            ProgramType::Int32Pointer,
        );
        let scalar_owner =
            CResourceFact::own_memory(CMemoryRange::new(scalar.clone(), 0u32.into(), 4u32.into()));
        let view = CResourceFact::view_memory(CMemoryRange::from_pointer_value(
            &viewed,
            0u32.into(),
            1u32.into(),
            4,
        ));
        let spec = CResourceSpec::viewed_memory(CMemorySegment::new(
            ProgramExpression::Value(ProgramValue::Pointer(viewed)),
            ProgramExpression::Value(ProgramValue::Int32(0u32.into())),
            ProgramExpression::Value(ProgramValue::Int32(1u32.into())),
        ));
        let mut withheld =
            ResourceContext::new_with_equalities(&facts).unchecked_with_fact(scalar_owner.clone());
        let mut memory =
            CMemory::new().with_declared_scalar_block(scalar.block, 4, ProgramType::Int32);
        let mut heaps = Vec::new();
        for index in 0..count {
            let owner = CResourceFact::own_memory(CMemoryRange::new(
                Pointer::symbolic(Variable(9_391_000 + index)),
                0u32.into(),
                4u32.into(),
            ));
            memory = memory.with_block(owner.memory_own_range().unwrap().base().block.clone(), 4);
            withheld = withheld.unchecked_with_fact(owner.clone());
            heaps.push(owner);
        }
        withheld.synchronize_memory_equalities(&facts);
        let declared =
            ResourceContext::new_with_equalities(&facts).unchecked_with_fact(view.clone());
        declared.synchronize_memory_equalities(&facts);
        let resources = withheld.clone().unchecked_with_fact(view.clone());
        resources.synchronize_memory_equalities(&facts);
        let entry = ExecutionState::new()
            .with_memory(memory)
            .with_resource_context(resources);
        let mut samples = Vec::new();
        for _ in 0..3 {
            let ((retained, selection_work), selection_maps) =
                crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        with_loop_frame_resources(
                            declared.clone(),
                            &withheld,
                            false,
                            &entry,
                            &facts,
                            &entry,
                        )
                    })
                });
            let (((body, failures), body_work), body_maps) =
                crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        loop_body_resource_context(
                            &entry,
                            &entry,
                            std::slice::from_ref(&spec),
                            &[],
                            &facts,
                            &mut ExecutionBudget::default(),
                        )
                        .unwrap()
                    })
                });
            assert!(failures.is_empty(), "{failures:?}");
            for resources in [&retained, body.resources()] {
                assert_eq!(resources.facts().len(), 2);
                assert!(resources.contains_exact_representation(&scalar_owner));
                assert!(resources.contains_exact_representation(&view));
                for heap in &heaps {
                    assert!(!resources.contains_exact_representation(heap));
                }
            }
            assert_eq!(entry.resources().facts().len(), count as usize + 2);
            assert!(
                entry
                    .resources()
                    .contains_exact_representation(&scalar_owner)
            );
            samples.push((selection_work, selection_maps, body_work, body_maps));
        }
        curves.push((count, samples));
    }
    eprintln!("loop rejected heap owners (count; selection work/maps, body work/maps): {curves:?}");
    assert!(
        curves[3].1.iter().zip(&curves[0].1).all(|(large, small)| {
            large.0 <= small.0 + 64
                && large.1 <= small.1 * 3 + 512
                && large.2 <= small.2 + 64
                && large.3 <= small.3 * 3 + 512
        }),
        "loop frame scans rejected heap owners: {curves:?}"
    );
}
