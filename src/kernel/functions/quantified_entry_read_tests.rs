use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

fn fixture(
    unrelated: usize,
    quantities: usize,
) -> (
    ExecutionState,
    Vec<ResourceSpec>,
    Vec<CompositeResourceDefinition>,
) {
    let pointer = Address {
        base: AddressBase::Concrete("quantity-pool".into()),
        offset: OldAddressOffset::Constant(0),
    };
    let state = ExecutionState::new()
        .with_local("pool", ProgramValue::pointer(pointer.clone()))
        .with_memory(
            SymbolicMemory::new()
                .with_block(pointer.base.clone(), 8)
                .store(
                    pointer.offset_by_int32_elements(OldMachineTerm::constant(1)),
                    int32(4),
                ),
        );
    let slot = ResourceSpec::composite(
        ResourceAccessMode::Own,
        "slot".into(),
        vec![crate::kernel::program_expression::variable("pool")],
        vec![ProgramType::Int32Pointer],
    );
    let authority = ResourceSpec::new(
        ResourceTerm::PopulationAuthority {
            population_arity: None,
            protected: Box::new(ResourceTypeSpec {
                resource: Box::new(slot.clone()),
                schema: ResourceFieldSchema::new(vec![]).unwrap(),
            }),
            state_source: ResourceStateSource::Current,
        },
        ResourceAccessMode::Own,
        ResourceQuantity::One,
        ResourceTransferRole::Borrow,
        ResourceStateSource::Entry,
    )
    .unwrap();
    let control = CompositeResourceDefinition::new(
        "zz_control",
        vec![program_parameter("pool", ProgramType::Int32Pointer)],
        None,
        false,
        vec![
            ResourceSpec::owned_memory(MemorySegment::new(
                crate::kernel::program_expression::variable("pool"),
                crate::kernel::program_expression::int32_literal(0),
                crate::kernel::program_expression::int32_literal(2),
            )),
            authority,
        ],
        vec![],
    );
    let mut definitions = (0..unrelated)
        .map(|index| {
            CompositeResourceDefinition::new(
                format!("unused_{index:04}"),
                vec![],
                None,
                false,
                vec![],
                vec![],
            )
        })
        .collect::<Vec<_>>();
    definitions.push(control);
    definitions.sort_by(|a, b| a.name().cmp(b.name()));
    let quantity = ResourceSpec::quantified(
        crate::kernel::program_expression::load(crate::kernel::program_expression::add(
            crate::kernel::program_expression::variable("pool"),
            crate::kernel::program_expression::int32_literal(1),
        )),
        slot,
        ResourceTransferRole::Borrow,
        ResourceStateSource::Entry,
    )
    .unwrap();
    let mut resources = vec![ResourceSpec::composite(
        ResourceAccessMode::Own,
        "zz_control".into(),
        vec![crate::kernel::program_expression::variable("pool")],
        vec![ProgramType::Int32Pointer],
    )];
    resources.extend(std::iter::repeat_n(quantity, quantities));
    (state, resources, definitions)
}

fn sample(unrelated: usize, quantities: usize) -> usize {
    let (state, resources, definitions) = fixture(unrelated, quantities);
    let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
        quantified_resource_requirement_assumptions(
            &state,
            &resources,
            &definitions,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
        )
    });
    let guards = result
        .unwrap()
        .expect("a folded control supplies the field read");
    assert_eq!(guards.len(), quantities);
    assert!(guards.iter().all(|guard| guard
        == &Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: Box::new(OldMachineTerm::constant(4)),
                right: Box::new(OldMachineTerm::constant(0))
            },
            true
        )));
    assert!(
        state.resources().facts().is_empty(),
        "the scratch projection must not change entry ownership"
    );
    work
}

#[test]
fn composite_read_projection_requires_positive_ownership() {
    let (state, _, definitions) = fixture(0, 1);
    let pointer = match state.locals.get_native("pool").as_deref().unwrap() {
        ProgramValue::Pointer(value) => value.address().clone(),
        _ => unreachable!(),
    };
    let target = ResourceFact::view_memory(MemoryRange::new(
        pointer.clone(),
        OldMachineTerm::constant(1),
        OldMachineTerm::constant(2),
    ));
    for quantity in [0, 1] {
        let supplied = ResourceFact::Own(
            Resource::Composite {
                name: "zz_control".into(),
                arguments: vec![ProgramValue::pointer(pointer.clone()).into()].into(),
            },
            Box::new(OldMachineTerm::constant(quantity).into()),
        );
        let supply = resource_clause_section_supply(
            &state,
            &[supplied],
            &definitions,
            &PureFactContext::new(),
        );
        assert_eq!(
            supply.satisfies_fact(&target, &PureFactContext::new()),
            quantity == 1,
            "zero ownership must not expose a folded body's memory"
        );
    }
}

#[test]
fn quantity_read_projection_is_built_once_per_section() {
    let samples = [1, 4, 16, 64].map(|size| (size, sample(64, size)));
    assert!(samples[0].1 > 0);
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * (pair[1].0 / pair[0].0) + 32,
            "quantity setup must scale with its clauses: {samples:?}"
        );
    }
}

#[test]
fn quantity_read_projection_ignores_unrelated_definitions() {
    let samples = [0, 16, 64, 256, 1024].map(|size| (size, sample(size, 1)));
    let baseline = samples[0].1;
    assert!(
        samples
            .iter()
            .all(|(size, work)| *work <= baseline + 4 * (size + 1).ilog2() as usize + 8),
        "quantity setup must not scan unrelated declarations: {samples:?}"
    );
}

#[test]
fn symbolic_quantity_keeps_the_entry_field_read_through_materialization() {
    let _session = crate::kernel::VerificationSession::enter();
    let pool = Address {
        base: AddressBase::ExternalArgument,
        offset: OldAddressOffset::scale_int32(OldMachineTerm::Variable(Variable(38_500)), 4),
    };
    let capacity = pool.offset_by_bytes(4);
    let view = ResourceFact::view_memory(MemoryRange::new(
        pool.clone(),
        OldMachineTerm::constant(0),
        OldMachineTerm::constant(2),
    ));
    let entry = ExecutionState::new()
        .with_local("pool", ProgramValue::pointer(pool))
        .with_resource_context(ResourceContext::new().unchecked_with_fact(view))
        .begin_function_entry_memory();
    let point = entry.program_point();
    let named = entry.clone().with_materialized_memory_at_current_point(
        entry
            .memory()
            .clone()
            .materialize_cell_at(capacity.clone(), ProgramType::Int32, &point),
    );
    let expression = crate::kernel::program_expression::load(
        crate::kernel::program_expression::pointer_offset_bytes(
            crate::kernel::program_expression::variable("pool"),
            4,
        ),
    );
    let quantity = |state| {
        evaluate_declared_quantity(
            state,
            &expression,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
        )
        .unwrap()
        .unwrap()
    };

    let before = quantity(&entry);
    assert!(matches!(
        before.old_form(),
        OldMachineTerm::MemoryLoad(read, address, LoadKind::Int32)
            if read.read_version_id() == point.id() && address.as_ref() == &capacity
    ));
    assert_eq!(before, quantity(&named));
}
