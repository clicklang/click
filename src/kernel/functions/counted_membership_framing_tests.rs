use super::*;
use crate::kernel::*;

fn boxed_definition() -> CCompositeResourceDefinition {
    CCompositeResourceDefinition::new(
        "boxed",
        vec![c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![CResourceSpec::owned_memory(CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(0),
            c_int32_literal(1),
        ))],
        vec![],
    )
}

/// A held composite whose body is argument-direct is kept by a call
/// without being opened: the recorded kept memory answers for its cell,
/// the checker's exact-range test finds the range it answered with, and
/// memory no held resource names is not kept.
#[test]
fn a_call_keeps_an_argument_direct_composites_memory_without_opening_it() {
    let _session = VerificationSession::enter();
    let boxed = boxed_definition();
    assert!(boxed.has_argument_direct_body());
    let object = |index: u64| Pointer::symbolic(Variable(781_000 + index));
    let residual = ResourceContext::new().unchecked_with_fact(CResourceFact::own_composite(
        "boxed".into(),
        vec![CValue::pointer(object(1))],
    ));
    let memory = CMemory::new().store(object(1), int32(5));
    let assumptions = PureFactContext::new();
    let state = CState::new()
        .with_memory(memory.clone())
        .with_resource_context(residual.clone());
    let kept = call_kept_ownership(&residual, &[boxed], &state, &assumptions);
    assert!(
        kept.opened_resources_for_test().is_empty(),
        "an argument-direct composite is not opened at the call"
    );
    let written = CMemoryRange::new(
        object(2),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    );
    let after =
        memory.with_call_memory_havoc(Variable(781_100), &[written], &assumptions, Some(&kept));
    let recorded = CallKeptRanges::recorded_on(&after).expect("kept memory is recorded");
    let range = recorded
        .range_holding(&assumptions, None, &object(1), 4)
        .expect("the composite's cell is kept by the caller");
    assert!(recorded.contains_range(&range));
    assert!(!recorded.holds_access(&object(3), 4, &assumptions));
    assert_eq!(
        recorded.diagnostic_ranges().facts().len(),
        1,
        "diagnostics still list the composite's range"
    );
}

/// Original flat ownership only excludes unchanged composite owners. Newly
/// packaged composites, retained flat fragments, and overlapping views must
/// keep their ordinary positive answers.
#[test]
fn caller_flat_exclusions_keep_new_composites_fragments_and_views() {
    let _session = VerificationSession::enter();
    let object = |index| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(index)), 4),
    };
    let cell = object(783_901);
    let other = object(783_902);
    let range =
        |base: Pointer, start, end| CMemoryRange::new_with_element_width(base, start, end, 4);
    let flat = range(cell.clone(), 0u32.into(), 3u32.into());
    let boxed =
        |base: Pointer| CResourceFact::own_composite("boxed".into(), vec![CValue::pointer(base)]);
    let original = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(flat.clone()))
        .unchecked_with_fact(boxed(other));
    let assumptions = PureFactContext::new();
    let memory = CMemory::new();
    let record = |original: &ResourceContext, residual: &ResourceContext| {
        let state = CState::new()
            .with_memory(memory.clone())
            .with_resource_context(original.clone());
        let kept = call_kept_ownership(residual, &[boxed_definition()], &state, &assumptions)
            .with_caller_before_transfer(original);
        let after = memory.clone().with_call_memory_havoc(
            Variable(783_910),
            std::slice::from_ref(&flat),
            &assumptions,
            Some(&kept),
        );
        CallKeptRanges::recorded_on(&after).unwrap()
    };
    let repackaged = ResourceContext::new().unchecked_with_fact(boxed(cell.clone()));
    let kept = record(&original, &repackaged);
    assert!(
        kept.holds_access(&cell, 4, &assumptions),
        "a new residual composite can protect the original flat cell"
    );
    assert_eq!(
        kept.diagnostic_ranges().facts().len(),
        1,
        "original owners are exclusion hints, not kept ranges"
    );
    assert!(!kept.holds_access(&cell.offset_by_elements(1u32.into(), 4), 4, &assumptions));

    let right = cell.offset_by_elements(2u32.into(), 4);
    let fragments = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(range(
        cell.clone(),
        2u32.into(),
        3u32.into(),
    )));
    assert!(
        record(&original, &fragments).holds_access(&right, 4, &assumptions),
        "a retained flat fragment wins before composite exclusion"
    );

    let zero = repackaged
        .clone()
        .unchecked_with_fact(CResourceFact::own_quantity(
            CResource::Memory(flat.clone()),
            0u32.into(),
        ));
    assert!(
        record(&zero, &repackaged).holds_access(&cell, 4, &assumptions),
        "a zero quantity must not exclude a composite owner"
    );

    let viewed = repackaged
        .clone()
        .unchecked_with_fact(CResourceFact::view_memory(flat.clone()));
    assert!(
        record(&viewed, &repackaged).holds_access(&cell, 4, &assumptions),
        "a view must not exclude its composite owner"
    );
}

#[test]
fn retained_membership_does_not_preserve_the_shared_body_across_a_call() {
    let _session = VerificationSession::enter();
    for wrapper_kind in 0..3 {
        let pointer = |name: &str| Pointer {
            block: name.into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let shared = pointer("shared-counter");
        let private = pointer("private-cell");
        crate::kernel::eval::declare_load_access_width(&shared, 4);
        crate::kernel::eval::declare_load_access_width(&private, 4);
        let range = |pointer: &Pointer| {
            CMemoryRange::new(
                pointer.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )
        };
        let memory_spec = |name: &str| {
            CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable(name),
                c_int32_literal(0),
                c_int32_literal(1),
            ))
        };
        let population = CCompositeResourceDefinition::authority_control(
            "remaining",
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            vec![memory_spec("p")],
            vec![],
        );
        let schema =
            ResourceFieldSchema::new(vec![("tag".into(), ResourceFieldType::C(CType::Int32))])
                .unwrap();
        let wrapper = CCompositeResourceDefinition::new(
            "wrapper",
            vec![
                c_parameter("p", CType::Int32Pointer),
                c_parameter("q", CType::Int32Pointer),
            ],
            None,
            false,
            vec![
                CResourceSpec::composite(
                    CResourceAccessMode::Own,
                    "remaining".into(),
                    vec![c_variable("p")],
                    vec![CType::Int32Pointer],
                ),
                memory_spec("q"),
            ],
            vec![],
        )
        .with_instance_schema((wrapper_kind == 2).then_some(schema.clone()));
        let mut residual = ResourceContext::new();
        let head = match wrapper_kind {
            0 => {
                residual = residual.unchecked_with_fact(CResourceFact::own_memory(range(&private)));
                CResourceFact::own_composite(
                    "remaining".into(),
                    vec![CValue::pointer(shared.clone())],
                )
            }
            1 => CResourceFact::own_composite(
                "wrapper".into(),
                vec![
                    CValue::pointer(shared.clone()),
                    CValue::pointer(private.clone()),
                ],
            ),
            _ => CResourceFact::own(CResource::Instance(
                ResourceInstance::new(
                    Variable(780_100),
                    "wrapper".into(),
                    vec![
                        CValue::pointer(shared.clone()).into(),
                        CValue::pointer(private.clone()).into(),
                    ]
                    .into(),
                    schema,
                    vec![int32(0).into()].into(),
                )
                .unwrap(),
            )),
        };
        residual = residual.unchecked_with_fact(head);
        let base = CMemory::new()
            .with_block("shared-counter", 4)
            .with_block("private-cell", 4);
        let load_in = |memory: &CMemory| {
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory_ref(memory),
                Box::new(shared.clone()),
                crate::kernel::LoadKind::Bits32,
            )
        };
        let (old_name, _) = crate::kernel::eval::load_variable_for_term(&load_in(&base)).unwrap();
        let before = base
            .store(
                shared.clone(),
                CValue::Int32(Bitvector32Term::Variable(old_name)),
            )
            .store(private.clone(), int32(7));
        let assumptions = PureFactContext::new().assume_condition(
            ConditionTerm::equal(
                Bitvector32Term::Variable(old_name),
                Bitvector32Term::Constant(0),
            ),
            true,
        );
        let state = CState::new()
            .with_memory(before.clone())
            .with_resource_context(residual.clone());
        let kept = call_kept_ownership(&residual, &[population, wrapper], &state, &assumptions);
        let after = before.clone().with_call_memory_havoc(
            Variable(780_101 + wrapper_kind),
            &[range(&shared), range(&private)],
            &assumptions,
            Some(&kept),
        );
        assert!(
            !after.cells.contains_key(&shared),
            "membership must not preserve the shared counter (wrapper {wrapper_kind})"
        );
        let same_load = |pointer: &Pointer| {
            checked_atomic_load_equality(
                &Bitvector32Term::MemoryLoad(
                    intern_c_memory_ref(&before),
                    Box::new(pointer.clone()),
                    crate::kernel::LoadKind::Bits32,
                ),
                &Bitvector32Term::MemoryLoad(
                    intern_c_memory_ref(&after),
                    Box::new(pointer.clone()),
                    crate::kernel::LoadKind::Bits32,
                ),
                &assumptions,
            )
        };
        let recorded = CallKeptRanges::recorded_on(&after).expect("private caller custody");
        assert!(recorded.holds_access(&private, 4, &assumptions));
        assert!(!recorded.holds_access(&shared, 4, &assumptions));
        assert!(
            !same_load(&shared),
            "membership cannot certify shared-body load equality across a call (wrapper {wrapper_kind})"
        );
        let (new_name, _) = crate::kernel::eval::load_variable_for_term(&load_in(&after)).unwrap();
        assert_ne!(
            new_name, old_name,
            "a population mutation must get a fresh load identity"
        );
        let post_facts = assumptions.assume_condition(
            ConditionTerm::equal(
                Bitvector32Term::Variable(new_name),
                Bitvector32Term::Constant(1),
            ),
            true,
        );
        assert!(
            !post_facts
                .equality_graph
                .are_int32_equal(&Bitvector32Term::Constant(0), &Bitvector32Term::Constant(1),),
            "the old and new invariants must not imply zero equals one"
        );
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/counted_membership_framing_tests.rs");
}
