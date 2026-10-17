use super::*;
use crate::kernel::VerificationSession;

fn pointer(id: u64) -> Pointer {
    Pointer::symbolic(Variable(990_000 + id))
}
fn range(p: &Pointer, start: u32, end: u32) -> CMemoryRange {
    CMemoryRange::new_with_element_width(p.clone(), start.into(), end.into(), 8)
}
fn separate(a: &Pointer, b: &Pointer) -> Proposition {
    Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(range(a, 0, 1))),
        right: Box::new(CResource::Memory(range(b, 0, 1))),
    }
}

fn numeric(a: &Pointer, b: &Pointer) -> ConditionTerm {
    ConditionTerm::uint64_equal(
        Bitvector32Term::pointer_address(a.clone()),
        Bitvector32Term::pointer_address(b.clone()),
    )
}
fn different(a: &Pointer, b: &Pointer) -> Proposition {
    Proposition::ConditionIs(numeric(a, b), false)
}
fn alias(a: &Pointer, b: &Pointer) -> Proposition {
    Proposition::ConditionIs(ConditionTerm::pointer_equal(a.clone(), b.clone()), true)
}

#[test]
fn address_separation_follows_checked_graph_aliases_early_and_late() {
    let _session = VerificationSession::enter();
    let (a, b, c, d) = (pointer(1), pointer(2), pointer(3), pointer(4));
    let source = separate(&a, &b);
    for early in [false, true] {
        let mut context = PureFactContext::new();
        if early {
            context = context.assume_proposition(source.clone());
        }
        context.equality_graph.add_checked_read_equality(&c, &b);
        context = context.assume_proposition(alias(&c, &d));
        if !early {
            context = context.assume_proposition(source.clone());
        }
        for (a, b) in [(&a, &d), (&d, &a)] {
            assert!(context.contains_known(&different(a, b)));
            assert_eq!(context.decide(&numeric(a, b)), Some(false));
            let deferred = context.clone().defer_non_exact_condition_reasoning();
            assert_eq!(
                crate::kernel::reasoning::decide_with_facts(
                    &deferred,
                    &ExecutionFacts::new(),
                    &numeric(a, b)
                ),
                Some(false)
            );
        }
    }
}

#[test]
fn address_separation_preserves_scope_alias_withdrawal_and_exact_sources() {
    let _session = VerificationSession::enter();
    let (a, b, c) = (pointer(10), pointer(11), pointer(12));
    let source = separate(&a, &b);
    let parent = PureFactContext::new().assume_proposition(source.clone());
    let equation = alias(&b, &c);
    let child = parent.clone().assume_proposition(equation.clone());
    assert!(child.contains_known(&different(&a, &c)));
    assert!(!parent.contains_known(&different(&a, &c)));
    assert!(
        !child
            .without_exact_fact(&source)
            .contains_known(&different(&a, &c))
    );
    assert!(
        !child
            .without_exact_fact(&equation)
            .contains_known(&different(&a, &c))
    );
    assert!(
        !child
            .restricted_to_facts(&[], &[])
            .contains_known(&different(&a, &c))
    );
    let (_, premises) = crate::kernel::assumptions::collect_reasoning_provenance(|| {
        crate::kernel::assumptions::capture_implicit_reasoning_provenance(|| {
            child.contains_known(&different(&a, &c))
        })
    });
    assert!(premises.contains(&source));
    assert!(child.contains_known(&different(&a, &c)));
}

#[test]
fn numeric_aliases_transfer_only_address_separation_not_pointer_identity() {
    let _session = VerificationSession::enter();
    let (a, b, c) = (pointer(30), pointer(31), pointer(32));
    let equation = Proposition::ConditionIs(numeric(&b, &c), true);
    let context = PureFactContext::new()
        .assume_proposition(separate(&a, &b))
        .assume_proposition(equation.clone());
    assert!(context.contains_known(&different(&a, &c)));
    assert!(!context.contains_known(&alias(&b, &c)));
    assert!(
        !context
            .without_exact_fact(&equation)
            .contains_known(&different(&a, &c))
    );
    let same = context.assume_proposition(Proposition::ConditionIs(numeric(&a, &c), true));
    assert!(!same.addresses_separated_by_class(&numeric(&a, &c)));
}

#[test]
fn empty_unknown_ranges_views_and_pointer_value_inequality_supply_no_address_separation() {
    let _session = VerificationSession::enter();
    let (a, b) = (pointer(40), pointer(41));
    let empty = Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(range(&a, 0, 0))),
        right: Box::new(CResource::Memory(range(&b, 0, 1))),
    };
    let unknown = Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(CMemoryRange::new(
            a.clone(),
            0u32.into(),
            Bitvector32Term::Variable(Variable(990_050)),
        ))),
        right: Box::new(CResource::Memory(range(&b, 0, 1))),
    };
    let views = Proposition::CResourceComposition(
        ResourceContext::new()
            .unchecked_with_fact(CResourceFact::view_memory(range(&a, 0, 1)))
            .unchecked_with_fact(CResourceFact::view_memory(range(&b, 0, 1))),
    );
    let unequal = Proposition::ConditionIs(
        ConditionTerm::PointerValueEqual(
            Box::new(CPointerValue::new(a.clone(), CType::Int32Pointer)),
            Box::new(CPointerValue::new(b.clone(), CType::Int32Pointer)),
        ),
        false,
    );
    for source in [empty, unknown, views, unequal] {
        let context = PureFactContext::new().assume_proposition(source);
        assert!(!context.contains_known(&different(&a, &b)));
    }
}

#[test]
fn separated_nonzero_range_starts_use_their_byte_addresses() {
    let _session = VerificationSession::enter();
    let (a, b) = (pointer(60), pointer(61));
    let source = Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(range(&a, 2, 3))),
        right: Box::new(CResource::Memory(range(&b, 1, 2))),
    };
    let context = PureFactContext::new().assume_proposition(source);
    assert!(context.contains_known(&different(&a.offset_by_bytes(16), &b.offset_by_bytes(8))));
    assert!(!context.contains_known(&different(&a, &b)));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/separation_tests.rs");
}

#[test]
fn constant_anchor_comparisons_do_not_require_an_application_node() {
    let _session = VerificationSession::enter();
    let p = Pointer::null();
    let context = PureFactContext::new().assume_proposition(separate(&p, &p));
    assert!(!context.addresses_separated_by_class(&numeric(&p, &p)));
}
