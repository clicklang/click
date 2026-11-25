// Scaling tests of `src/kernel/functions.rs` (module `population_creation_frame_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn function_return_lifetime_cleanup_ignores_value_only_parameters() {
    let caller = ExecutionState::new();
    let function = program_function(
        ProgramType::Int32,
        "scope",
        vec![],
        program_return(crate::kernel::program_expression::int32_literal(0)),
    );
    let mut samples = Vec::new();
    for count in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let block = AddressBase::from("local:frame:live");
        let mut state = ExecutionState::new()
            .with_local("frame:live", int32(0))
            .with_memory(SymbolicMemory::new().with_block(block.clone(), 4));
        for i in 0..count {
            let name = BindingName::from(format!("parameter_{i}"));
            let slot = SymbolicMemory::value_parameter_pointer(&name);
            state.locals.set_typed_qualified_with_all_qualifiers(
                name,
                int32(0),
                ProgramType::Int32,
                slot,
                false,
                false,
                false,
                false,
            );
        }
        let outcome = StatementOutcome::Return {
            value: int32(0).into(),
            state: Box::new(state.clone()),
        };
        let ((result, obligations), return_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                function_outcome_from_body(
                    &caller,
                    &function,
                    outcome,
                    vec![],
                    &PureFactContext::new(),
                    None,
                )
            });
        assert!(obligations.is_empty());
        let FunctionOutcome::Return { state: after, .. } = result else {
            panic!("expected successful return, got {result:?}");
        };
        assert!(after.memory().is_ended_local_block(&block));

        let (inline, inline_work) = crate::instrumentation::measure_deterministic_work(|| {
            end_inline_frame_automatic_lifetimes(&state).unwrap()
        });
        assert_eq!(inline.retired_local_blocks, vec![block]);
        samples.push((count, return_work, inline_work));
    }
    let (_, first_return, first_inline) = samples[0];
    for (count, return_work, inline_work) in samples {
        assert!(
            return_work <= first_return + 8 && inline_work <= first_inline + 8,
            "{count} value-only parameters: return {return_work}, inline {inline_work}, baseline return {first_return}, inline {first_inline}"
        );
    }
}

#[test]
fn automatic_lifetime_reuse_tracks_exact_memory_and_retired_blocks() {
    for size in [16usize, 32, 64, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let blocks = (0..size)
            .map(|i| AddressBase::from(format!("local:lifetime:memo_{i}")))
            .collect::<Vec<_>>();
        let before = blocks.iter().fold(SymbolicMemory::new(), |memory, block| {
            memory.with_block(block.clone(), 4)
        });
        let after = retire_automatic_lifetime_blocks(&before, &blocks);
        let (repeated, work) = crate::instrumentation::measure_deterministic_work(|| {
            retire_automatic_lifetime_blocks(&before, &blocks)
        });
        assert_eq!(after, repeated);
        assert!(
            work <= size + 1,
            "retiring {size} exact blocks again rebuilt memory: {work}"
        );
        for block in &blocks {
            assert!(!after.has_block(block));
            assert!(after.is_ended_local_block(block));
        }
        // A sibling input must not evict the result needed when checking
        // this branch again after execution has visited other outcomes.
        let sibling = before.clone().with_block("caller:sibling", 4);
        retire_automatic_lifetime_blocks(&sibling, &blocks);
        let (interleaved, work) = crate::instrumentation::measure_deterministic_work(|| {
            retire_automatic_lifetime_blocks(&before, &blocks)
        });
        assert_eq!(interleaved, after);
        assert!(
            work <= size + 1,
            "interleaved retirement rebuilt {size} blocks: {work}"
        );
        let partial = retire_automatic_lifetime_blocks(&before, &blocks[..size - 1]);
        assert!(partial.has_block(&blocks[size - 1]));
        let changed = before.clone().with_block("caller:preserved", 8);
        let changed_after = retire_automatic_lifetime_blocks(&changed, &blocks);
        assert!(changed_after.has_block(&AddressBase::from("caller:preserved")));
        assert!(!after.has_block(&AddressBase::from("caller:preserved")));
    }
}

#[test]
fn control_read_body_retains_its_held_frame_as_owners_and_aliases_grow() {
    use crate::kernel::program_expression::{int32_literal, variable};
    use crate::kernel::{MemorySegment, ResourceTypeSpec};

    for aliases in [false, true] {
        let mut samples = Vec::new();
        for count in [4_u64, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = Address {
                base: AddressBase::ExternalArgument,
                offset: AddressOffset::Variable(Variable(7_993_000)),
            };
            let value = ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int32Pointer);
            let member = ResourceSpec::composite(
                ResourceAccessMode::Own,
                "slot".into(),
                vec![variable("p")],
                vec![ProgramType::Int32Pointer],
            );
            let authority_spec = ResourceSpec::new(
                ResourceTerm::PopulationAuthority {
                    protected: Box::new(ResourceTypeSpec {
                        resource: Box::new(member),
                        schema: ResourceFieldSchema::new(vec![]).unwrap(),
                    }),
                    population_arity: None,
                    state_source: ResourceStateSource::Current,
                },
                ResourceAccessMode::Own,
                ResourceQuantity::One,
                ResourceTransferRole::Borrow,
                ResourceStateSource::Entry,
            )
            .unwrap();
            let definition = CompositeResourceDefinition::new(
                "control",
                vec![program_parameter("p", ProgramType::Int32Pointer)],
                None,
                false,
                vec![
                    ResourceSpec::owned_memory(MemorySegment::new(
                        variable("p"),
                        int32_literal(0),
                        int32_literal(1),
                    )),
                    authority_spec,
                ],
                vec![],
            );
            let interface = program_function(
                ProgramType::Void,
                "read_control",
                vec![],
                ProgramStatement::Skip,
            )
            .with_composite_resource_definitions(vec![definition])
            .contract_interface()
            .clone();
            let head = ResourceFact::own(Resource::Composite {
                name: "control".into(),
                arguments: vec![value.clone().into()].into(),
            });
            let authority =
                ResourceFact::own(Resource::PopulationAuthority(ResourceDescription::new(
                    "slot".into(),
                    vec![value.into()].into(),
                    ResourceFieldSchema::new(vec![]).unwrap(),
                )));
            let frontier = ResourceContext::new().unchecked_with_fact(head.clone());
            let mut facts = PureFactContext::new();
            let mut resources =
                ResourceContext::new().unchecked_with_facts([head.clone(), authority.clone()]);
            let mut retained = Vec::new();
            for index in 0..count {
                let other = Address::symbolic(Variable(7_993_100 + index));
                if aliases {
                    facts = facts.assume_condition(
                        OldConditionTerm::address_equal(pointer.clone(), other),
                        true,
                    );
                } else {
                    let owner = ResourceFact::own_memory(MemoryRange::new_with_element_width(
                        other,
                        OldMachineTerm::constant(0),
                        OldMachineTerm::constant(1),
                        4,
                    ));
                    resources = resources.unchecked_with_fact(owner.clone());
                    retained.push(owner);
                }
            }
            resources.synchronize_memory_equalities(&facts);
            let state = ExecutionState::new()
                .with_population_creation_tracking()
                .with_resource_context(resources)
                .import_opaque_population(&authority, 0)
                .unwrap();
            let resources = state
                .resources()
                .clone()
                .without_fact_incrementally(&authority, &facts)
                .unwrap();
            let retained = retained
                .into_iter()
                .map(|fact| {
                    let occurrence = resources.first_exact_occurrence(&fact).unwrap();
                    (fact, occurrence)
                })
                .collect::<Vec<_>>();
            let state = state.with_resource_context(resources);
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                let _fast =
                    crate::kernel::search::FastOperationScope::enter("held control read body");
                checked_contract_control_read_state(&state, &frontier, &interface, &facts)
            });
            let result = result.unwrap();
            assert!(!result.resources().contains_exact_representation(&head));
            assert!(result.resources().contains_exact_representation(&authority));
            assert!(
                result
                    .resources()
                    .contains_exact_representation(&ResourceFact::own_memory(
                        MemoryRange::new_with_element_width(
                            pointer,
                            OldMachineTerm::constant(0),
                            OldMachineTerm::constant(1),
                            4
                        ),
                    ))
            );
            for (fact, occurrence) in retained {
                assert_eq!(
                    result.resources().first_exact_occurrence(&fact),
                    Some(occurrence)
                );
            }
            samples.push(work);
        }
        assert!(
            samples[2] <= samples[0] * 3 + 96,
            "aliases={aliases}: {samples:?}"
        );
    }
}
