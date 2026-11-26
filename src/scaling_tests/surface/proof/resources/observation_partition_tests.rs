use super::*;

#[test]
fn constructed_state_observation_does_not_revisit_ambient_owners_or_aliases() {
    for axis in ["related", "owners", "aliases"] {
        let mut samples = Vec::new();
        for count in [4_u32, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = OldAddress::symbolic(Variable(8_919_000));
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
                        OldConditionTerm::address_equal(
                            pointer.clone(),
                            OldAddress::symbolic(Variable(8_919_100 + u64::from(index))),
                        ),
                        true,
                    ));
                } else {
                    let (base, start) = if axis == "related" {
                        (pointer.clone(), (index + 1) * 8)
                    } else {
                        (
                            OldAddress::symbolic(Variable(8_919_200 + u64::from(index))),
                            0,
                        )
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
        let pointer = OldAddress::symbolic(Variable(991_044));
        let read = OldMachineTerm::read_named(
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
            point: Default::default(),
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

#[test]
fn stored_conditions_and_counts_check_current_dependency_without_export() {
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelTermImport, KernelType, LoadKind, MachineBinaryOp,
        ProgramPoint, StoredConditionTerm, StoredMachineTerm,
    };

    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let state = ExecutionState::new();
        let pointer = OldAddress::symbolic(Variable(991_045));
        let point = ProgramPoint::at(&crate::kernel::intern_memory_ref(state.memory()));
        let word =
            OldMachineTerm::read_named(point.clone(), Box::new(pointer.clone()), LoadKind::Int32);
        let wide = OldMachineTerm::read_named(point, Box::new(pointer.clone()), LoadKind::Bits64);
        let mut import = KernelTermImport::for_exact_field_inputs();
        let word = import.machine(MachineIntegerType::Int32, &word);
        let wide = import.machine(MachineIntegerType::UInt64, &wide);
        let word_limit =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(991_046));
        let mut condition = KernelTerm::boolean_comparison(
            MachineIntegerType::Int32,
            CompareRelation::Equal,
            [word, word_limit],
        );
        let guard = KernelTerm::variable(KernelType::Bool, Variable(991_047));
        let mut count = wide.clone();
        for _ in 0..size {
            condition = KernelTerm::boolean_if_raw([guard.clone(), condition, guard.clone()]);
            count = KernelTerm::machine_binary_shared(
                MachineIntegerType::UInt64,
                MachineBinaryOp::Add,
                [count, wide.clone()],
            );
        }
        let baseline = KernelTermExport::machine_export_count();
        let condition_fact = Proposition::condition_is(
            StoredConditionTerm::from_root(condition.clone()).unwrap(),
            true,
        );
        let count_fact = Proposition::MemoryLoadable {
            point: Default::default(),
            memory: state.memory().clone(),
            base: pointer.clone(),
            bytes: StoredMachineTerm::from_value(crate::kernel::ExecutionValue::Shared(
                count.clone(),
            ))
            .unwrap(),
            wide: true,
        };
        let assumptions = PureFactContext::new();
        let views = DynamicViewDependencyIndex::new(&[], &[], &assumptions);
        for fact in [&condition_fact, &count_fact] {
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                dynamic_body_fact_dependency(fact, &state, &assumptions, &views)
            });
            assert_eq!(
                result.unwrap_err(),
                "current body fact reads memory outside every live viewed-memory dependency"
            );
            assert!(work <= 32 * (size + 1) + 128, "size={size}, work={work}");
        }
        assert_eq!(KernelTermExport::machine_export_count(), baseline);
        assert!(!condition.has_cached_native_argument());
        assert!(!count.has_cached_native_argument());

        let raw_count =
            StoredMachineTerm::from_value(crate::kernel::ExecutionValue::Shared(wide)).unwrap();
        assert_eq!(
            crate::kernel::current_memory_loads_in_count(&raw_count, state.memory()).unwrap_err(),
            "current memory load has no statically known byte width"
        );
        let opaque = StoredConditionTerm::from_root(KernelTerm::checked_call(
            KernelType::Bool,
            "opaque_test".into(),
            vec![],
        ))
        .unwrap();
        assert_eq!(
            dynamic_body_fact_dependency(
                &Proposition::condition_is(opaque, true),
                &state,
                &assumptions,
                &views,
            )
            .unwrap_err(),
            "opaque Click function may hide a current memory load"
        );
    }
}
