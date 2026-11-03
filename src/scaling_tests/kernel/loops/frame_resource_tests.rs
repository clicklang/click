// Scaling coverage for rebuilding a loop's retained frame in kernel/loops.rs.
use super::*;

#[test]
fn a_loop_frame_normalizes_its_retained_views_once() {
    let mut samples = Vec::new();
    for count in [4u64, 8, 16, 32, 64] {
        let assumptions = PureFactContext::new();
        let state = CState::new();
        let views = (0..count)
            .map(|index| {
                CResourceFact::view_memory(CMemoryRange::new(
                    Pointer::symbolic(Variable(9_360_000 + index)),
                    Bitvector32Term::Constant(0),
                    Bitvector32Term::Constant(1),
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
#[ignore = "red regression: loop binding carryover scans matching observations"]
fn loop_binding_carryover_ignores_ambient_observations() {
    use crate::kernel::loans::{LoanLedger, LoanViewBinding, LoanViewBindings};

    let mut curves = Vec::new();
    for case in ["early", "late", "unbound", "retained_metadata"] {
        let mut samples = Vec::new();
        for count in [4usize, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let assumptions = PureFactContext::new();
            let pointer =
                CPointerValue::new(Pointer::symbolic(Variable(9_370_001)), CType::Int32Pointer);
            let view = CResourceFact::view_memory(CMemoryRange::from_pointer_value(
                &pointer,
                0u32.into(),
                8u32.into(),
                4,
            ));
            let spec = CResourceSpec::viewed_memory(CMemorySegment::new(
                CExpression::Value(CValue::Pointer(pointer)),
                CExpression::Value(CValue::Int32(0u32.into())),
                CExpression::Value(CValue::Int32(8u32.into())),
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
            let entry = CState::new()
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
                        // The binding-copy block in loop_body_resource_context.
                        let mut carried = entry.loan_view_bindings().clone();
                        for fact in body_resources.facts().iter().filter(|fact| fact.is_view()) {
                            let Some(binding) = entry
                                .resources()
                                .view_occurrences_for_fact(fact, &assumptions)
                                .into_iter()
                                .find_map(|occurrence| {
                                    entry.loan_view_bindings().get(&occurrence).cloned()
                                })
                            else {
                                continue;
                            };
                            if let Some(occurrence) = body_resources
                                .view_occurrences_for_fact(fact, &assumptions)
                                .into_iter()
                                .find(|occurrence| carried.get(occurrence).is_none())
                            {
                                carried = carried.with_inserted(occurrence, binding);
                            }
                        }
                        carried
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
