use super::*;

fn pointer(id: u64) -> CPointerValue {
    CPointerValue::new(Pointer::symbolic(Variable(id)), CType::Int32Pointer)
}

fn view(value: &CPointerValue, start: u32, end: u32) -> CResourceFact {
    CResourceFact::view_memory(CMemoryRange::from_pointer_value(
        value,
        start.into(),
        end.into(),
        4,
    ))
}

fn permits(
    value: &CPointerValue,
    bytes: u32,
    facts: &PureFactContext,
    resources: &ResourceContext,
) -> bool {
    permits_at(
        value,
        &value.pointer().offset_by_bytes(bytes),
        facts,
        resources,
    )
}

fn permits_at(
    value: &CPointerValue,
    position: &Pointer,
    facts: &PureFactContext,
    resources: &ResourceContext,
) -> bool {
    subobject_formation_guards(
        value,
        position,
        &ExecutionFacts::new(),
        &[],
        facts,
        resources,
    )
    .is_ok_and(|guards| {
        guards
            .iter()
            .all(|guard| facts.decide(&guard.condition) == Some(guard.value))
    })
}

#[test]
fn formation_requires_the_original_domain_and_includes_one_past() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = pointer(930_100);
    let q = pointer(930_101);
    let root = PureFactContext::new();
    let resources = ResourceContext::new().unchecked_with_fact(view(&q, 0, 2));
    assert!(permits(&p, 0, &root, &ResourceContext::new()));
    assert!(!permits(&p, 4, &root, &ResourceContext::new()));
    let numeric = root.clone().assume_condition(
        ConditionTerm::pointer_equal(p.pointer().clone(), q.pointer().clone()),
        true,
    );
    assert!(!permits(&p, 4, &numeric, &resources));
    let equality = Proposition::ConditionIs(
        ConditionTerm::PointerValueEqual(Box::new(p.clone()), Box::new(q.clone())),
        true,
    );
    let full = numeric.clone().assume_proposition(equality.clone());
    assert!(permits(&p, 4, &full, &resources));
    assert!(permits(&p, 8, &full, &resources));
    assert!(!permits(&p, 12, &full, &resources));
    assert!(!permits(
        &p,
        4,
        &full.without_exact_fact(&equality),
        &resources
    ));
    assert!(!permits(
        &p,
        4,
        &root,
        &ResourceContext::new().unchecked_with_fact(view(&p, 1, 1))
    ));
    let empty_coverage = p
        .opaque_coverage_fact(&CMemoryRange::from_pointer_value(
            &p,
            1u32.into(),
            1u32.into(),
            4,
        ))
        .unwrap();
    assert!(!permits(
        &p,
        4,
        &root.assume_proposition(empty_coverage),
        &ResourceContext::new()
    ));
}

#[test]
fn member_coverage_does_not_follow_numeric_aliases_or_survive_withdrawal() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = pointer(930_200);
    let q = pointer(930_201);
    let coverage = q
        .opaque_coverage_fact(&CMemoryRange::from_pointer_value(
            &q,
            0u32.into(),
            3u32.into(),
            4,
        ))
        .unwrap();
    let numeric = PureFactContext::new()
        .assume_condition(
            ConditionTerm::pointer_equal(p.pointer().clone(), q.pointer().clone()),
            true,
        )
        .assume_proposition(coverage.clone());
    let empty = ResourceContext::new();
    assert!(!permits(&p, 8, &numeric, &empty));
    let equality = Proposition::ConditionIs(
        ConditionTerm::PointerValueEqual(Box::new(p.clone()), Box::new(q.clone())),
        true,
    );
    let full = numeric.clone().assume_proposition(equality.clone());
    assert!(permits(&p, 12, &full, &empty));
    assert!(!permits(&p, 16, &full, &empty));
    assert!(!permits(&p, 8, &full.without_exact_fact(&coverage), &empty));
    assert!(!permits(&p, 8, &full.without_exact_fact(&equality), &empty));
    let member = p
        .clone()
        .with_member_extent(SubobjectExtent::constant(p.pointer().clone(), 4));
    assert!(!permits(&member, 8, &full, &empty));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/eval/unknown_pointer_formation_tests.rs");
}

#[test]
fn allocation_bounds_require_positive_ownership_and_grant_no_read_permission() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = pointer(930_400);
    let allocation = CResourceFact::own_designated_allocation(p.clone(), 12u32);
    let root = PureFactContext::new();
    let coverage = allocation.allocation_bounds_fact(&root).unwrap();
    let context = root.clone().assume_proposition(coverage);
    assert!(permits(&p, 12, &context, &ResourceContext::new()));
    assert!(!permits(&p, 16, &context, &ResourceContext::new()));
    let resources = ResourceContext::new().unchecked_with_fact(allocation.clone());
    assert!(!resources.permits_memory_read(p.pointer(), 4, &context));
    let empty = CResourceFact::own_quantity(allocation.resource().clone(), 0u32.into());
    assert!(empty.allocation_bounds_fact(&root).is_none());
}

#[test]
fn slice_entry_bounds_allow_formation_without_read_authority() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = pointer(930_450);
    let state = CState::new()
        .with_local("data", CValue::Pointer(p.clone()))
        .with_local("length", CValue::UInt64(Bitvector32Term::UInt64Constant(2)));
    let function = c_function(
        CType::Void,
        "slice_metadata",
        vec![
            c_parameter("p", CType::Int32Pointer).with_slice_length_parameter(1),
            c_parameter("n", CType::UInt64),
        ],
        c_skip(),
    );
    let entry = crate::kernel::c_function_contract_entry(
        &state,
        &function,
        &[
            CExpression::Value(CValue::Pointer(p.clone())),
            CExpression::Value(
                CValue::UInt64(Bitvector32Term::UInt64Constant(2))
                    .complete_word(Pointer::symbolic(Variable(930_451))),
            ),
        ],
    )
    .unwrap();
    let context = entry
        .facts()
        .iter()
        .fold(PureFactContext::new(), |facts, fact| {
            facts.assume_proposition(fact.proposition().clone())
        });
    let resources = ResourceContext::new();
    assert!(permits(&p, 8, &context, &resources));
    assert!(!permits(&p, 12, &context, &resources));
    assert!(!resources.permits_memory_read(p.pointer(), 4, &context));
}

#[test]
fn well_formed_range_terms_do_not_establish_an_opaque_domain() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = pointer(930_500);
    let range = CMemoryRange::from_pointer_value(&p, 0u32.into(), 3u32.into(), 4);
    let state = |facts: Vec<Proposition>| {
        facts
            .into_iter()
            .fold(PureFactContext::new(), |context, fact| {
                context.assume_proposition(fact)
            })
    };
    let numeric = state(crate::kernel::memory_range_extent_guard_spellings(&range));
    assert!(!permits(&p, 4, &numeric, &ResourceContext::new()));
    let admitted = state(crate::kernel::admitted_memory_range_extent_facts(&range));
    assert!(permits(&p, 12, &admitted, &ResourceContext::new()));
    assert!(!permits(&p, 16, &admitted, &ResourceContext::new()));
}

#[test]
fn native_coverage_keeps_high_bits_and_interior_bytes() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = pointer(930_600);
    let start = 1u64 << 32;
    let range = CMemoryRange::from_pointer_value_wide(
        &p,
        Bitvector32Term::UInt64Constant(start),
        Bitvector32Term::UInt64Constant(start + 2),
        4,
    );
    let coverage = p.opaque_coverage_fact(&range).unwrap();
    let context = PureFactContext::new().assume_proposition(coverage.clone());
    let position = |index| {
        p.pointer()
            .offset_by_typed_elements(Bitvector32Term::UInt64Constant(index), 4, true, true)
    };
    assert!(context.opaque_pointer_covers(&p, &position(start + 1), 4));
    assert!(context.opaque_pointer_covers(&p, &position(start + 2), 0));
    assert!(!context.opaque_pointer_covers(&p, &position(start + 2), 4));
    assert!(!context.opaque_pointer_covers(&p, &position(1), 0));
    let (allowed, used) = crate::kernel::assumptions::collect_reasoning_provenance(|| {
        context.opaque_pointer_covers(&p, &position(start + 1), 0)
    });
    assert!(allowed && used.contains(&coverage));
    assert!(
        !context
            .without_exact_fact(&coverage)
            .opaque_pointer_covers(&p, &position(start + 1), 0)
    );
    let record = CMemoryRange::from_pointer_value_wide(
        &p,
        Bitvector32Term::UInt64Constant(0),
        Bitvector32Term::UInt64Constant(2),
        16,
    );
    let context =
        PureFactContext::new().assume_proposition(p.opaque_coverage_fact(&record).unwrap());
    assert!(context.opaque_pointer_covers(&p, &p.pointer().offset_by_bytes(4), 4));
    assert!(!context.opaque_pointer_covers(&p, &p.pointer().offset_by_bytes(31), 4));
}

fn split_formation_fixture() -> (
    CPointerValue,
    Pointer,
    PureFactContext,
    ResourceContext,
    CResourceFact,
) {
    let p = CPointerValue::new(
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(930_999)), 4),
        },
        CType::Int32Pointer,
    );
    let from = Bitvector32Term::Variable(Variable(930_601));
    let to = Bitvector32Term::Variable(Variable(930_602));
    let i = Bitvector32Term::Variable(Variable(930_603));
    let facts = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_than(0u32.into(), from.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(from.clone(), i.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(i.clone(), to.clone()), true)
        .assume_condition(
            ConditionTerm::signed_less_equal(to.clone(), 8u32.into()),
            true,
        );
    let position = p.pointer().offset_by_elements(i, 4);
    let owner = CResourceFact::own_memory(CMemoryRange::from_pointer_value(
        &p,
        from.clone(),
        to.clone(),
        4,
    ));
    let resources = ResourceContext::new_with_equalities(&facts)
        .unchecked_with_fact(CResourceFact::view_memory(
            CMemoryRange::from_pointer_value(&p, 0u32.into(), from.clone(), 4),
        ))
        .unchecked_with_fact(owner.clone())
        .unchecked_with_fact(CResourceFact::view_memory(
            CMemoryRange::from_pointer_value(&p, to, 8u32.into(), 4),
        ));
    resources.synchronize_memory_equalities(&facts);
    (p, position, facts, resources, owner)
}

#[test]
fn formation_selects_the_containing_symbolic_piece_beside_prefix_and_suffix_views() {
    let _session = crate::kernel::VerificationSession::enter();
    let (p, position, facts, resources, owner) = split_formation_fixture();
    assert!(
        permits_at(&p, &position, &facts, &resources),
        "the owned middle piece contains the queried position"
    );
    let zero = resources
        .clone()
        .without_exact_representation(&owner)
        .unwrap()
        .unchecked_with_fact(CResourceFact::own_quantity(
            owner.resource().clone(),
            0u32.into(),
        ));
    zero.synchronize_memory_equalities(&facts);
    assert!(!permits_at(&p, &position, &facts, &zero));
    assert!(permits_at(&p, &position, &facts, &resources));
}
