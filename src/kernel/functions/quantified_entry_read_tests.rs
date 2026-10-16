use super::*;

fn fixture(
    unrelated: usize,
    quantities: usize,
) -> (
    CState,
    Vec<CResourceSpec>,
    Vec<CCompositeResourceDefinition>,
) {
    let pointer = Pointer {
        block: PointerBlock::Concrete("quantity-pool".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("pool", CValue::pointer(pointer.clone()))
        .with_memory(CMemory::new().with_block(pointer.block.clone(), 8).store(
            pointer.offset_by_int32_elements(Bitvector32Term::Constant(1)),
            int32(4),
        ));
    let slot = CResourceSpec::composite(
        CResourceAccessMode::Own,
        "slot".into(),
        vec![c_variable("pool")],
        vec![CType::Int32Pointer],
    );
    let authority = CResourceSpec::new(
        CResourceTerm::PopulationAuthority {
            population_arity: None,
            protected: Box::new(CResourceTypeSpec {
                resource: Box::new(slot.clone()),
                schema: ResourceFieldSchema::new(vec![]).unwrap(),
            }),
            snapshot: CResourceSnapshot::Current,
        },
        CResourceAccessMode::Own,
        CResourceQuantity::One,
        CResourceTransferRole::Borrow,
        CResourceSnapshot::Entry,
    )
    .unwrap();
    let control = CCompositeResourceDefinition::new(
        "zz_control",
        vec![c_parameter("pool", CType::Int32Pointer)],
        None,
        false,
        vec![
            CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable("pool"),
                c_int32_literal(0),
                c_int32_literal(2),
            )),
            authority,
        ],
        vec![],
    );
    let mut definitions = (0..unrelated)
        .map(|index| {
            CCompositeResourceDefinition::new(
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
    let quantity = CResourceSpec::quantified(
        c_load(c_add(c_variable("pool"), c_int32_literal(1))),
        slot,
        CResourceTransferRole::Borrow,
        CResourceSnapshot::Entry,
    )
    .unwrap();
    let mut resources = vec![CResourceSpec::composite(
        CResourceAccessMode::Own,
        "zz_control".into(),
        vec![c_variable("pool")],
        vec![CType::Int32Pointer],
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
        == &Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(
                Box::new(Bitvector32Term::Constant(4)),
                Box::new(Bitvector32Term::Constant(0)),
            ),
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
    let pointer = match state.locals.get("pool").unwrap() {
        CValue::Pointer(value) => value.pointer().clone(),
        _ => unreachable!(),
    };
    let target = CResourceFact::view_memory(CMemoryRange::new(
        pointer.clone(),
        Bitvector32Term::Constant(1),
        Bitvector32Term::Constant(2),
    ));
    for quantity in [0, 1] {
        let supplied = CResourceFact::Own(
            CResource::Composite {
                name: "zz_control".into(),
                arguments: vec![CValue::pointer(pointer.clone()).into()].into(),
            },
            Box::new(Bitvector32Term::Constant(quantity)),
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
