use super::*;

#[test]
fn constructed_state_observation_does_not_revisit_ambient_owners_or_aliases() {
    for axis in ["related", "owners", "aliases"] {
        let mut samples = Vec::new();
        for count in [4_u32, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = Address::symbolic(Variable(8_919_000));
            let mut aliases = Vec::new();
            let mut resources = ResourceContext::new().unchecked_with_fact(
                ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    pointer.clone(),
                    0u32.into(),
                    4u32.into(),
                    1,
                )),
            );
            for index in 0..count {
                if axis == "aliases" {
                    aliases.push(Proposition::condition_is(
                        ConditionTerm::address_equal(
                            pointer.clone(),
                            Address::symbolic(Variable(8_919_100 + u64::from(index))),
                        ),
                        true,
                    ));
                } else {
                    let (base, start) = if axis == "related" {
                        (pointer.clone(), (index + 1) * 8)
                    } else {
                        (Address::symbolic(Variable(8_919_200 + u64::from(index))), 0)
                    };
                    resources = resources.unchecked_with_fact(ResourceFact::own_memory(
                        MemoryRange::new_with_element_width(
                            base,
                            start.into(),
                            (start + 4).into(),
                            1,
                        ),
                    ));
                }
            }
            let store = PureFactStore::from_ordered(&aliases);
            resources.synchronize_memory_equalities(store.assumptions());
            let state = ExecutionState::new().with_resource_context(resources);
            let mut facts = ProofResourcePureFacts::new(store);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                append_state_resource_context_observable_facts_with_store(&state, &mut facts);
            });
            samples.push(work);
        }
        assert!(samples[2] <= samples[0] + 64, "{axis}: {samples:?}");
    }
}

#[test]
fn memory_load_outcome_checks_shared_current_read_dependencies_without_export() {
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelTermImport, LoadKind, MachineBinaryOp, ProgramPoint,
    };

    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let state = ExecutionState::new();
        let pointer = Address::symbolic(Variable(991_044));
        let read = MachineTerm::MemoryLoad(
            ProgramPoint::at(&crate::kernel::intern_memory_ref(state.memory())),
            Box::new(pointer.clone()),
            LoadKind::Int32,
        );
        let format = MachineIntegerType::Int32;
        let mut root = KernelTermImport::for_exact_field_inputs().machine(format, &read);
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let fact = Proposition::MemoryLoads {
            memory: state.memory().clone(),
            pointer,
            outcome: ExpressionOutcome::Value(crate::kernel::StoredProgramValue::from(
                crate::kernel::ExecutionValue::from(root.clone()),
            )),
        };
        let assumptions = PureFactContext::new();
        let views = DynamicViewDependencyIndex::new(&[], &[], &assumptions);
        let exports = KernelTermExport::machine_export_count();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            dynamic_body_fact_dependency(&fact, &state, &assumptions, &views)
        });
        assert_eq!(
            result.unwrap_err(),
            "current body fact reads memory outside every live viewed-memory dependency"
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(!root.has_cached_native_argument());
        assert!(work <= 32 * (size + 1) + 128, "size={size}, work={work}");
    }
}
