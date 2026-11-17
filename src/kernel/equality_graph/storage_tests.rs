use super::*;

#[test]
fn concrete_storage_coordinates_follow_transitive_aliases_and_forks() {
    let first = Address::symbolic(Variable(896_000));
    let second = Address::symbolic(Variable(896_001));
    let storage = Address {
        base: "local:mutex".into(),
        offset: AddressOffset::Constant(8),
    };
    let empty = PureFactContext::new();
    let joined = empty
        .clone()
        .assume_condition(
            ConditionTerm::pointer_equal(first.clone(), second.clone()),
            true,
        )
        .assume_condition(ConditionTerm::pointer_equal(second, storage.clone()), true);
    assert_eq!(
        joined
            .equality_graph
            .storage_address(&first.offset_by_bytes(16)),
        storage.offset_by_bytes(16)
    );
    assert_eq!(empty.equality_graph.storage_address(&first), first);
    let other = Address {
        base: "local:other".into(),
        offset: AddressOffset::Constant(0),
    };
    let ambiguous = joined
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(first.clone(), other), true);
    assert_eq!(ambiguous.equality_graph.storage_address(&first), first);
    assert_eq!(joined.equality_graph.storage_address(&first), storage);
}

#[test]
fn external_addresses_select_their_own_concrete_storage_anchor() {
    let first = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Variable(Variable(896_010)),
    };
    let second = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Variable(Variable(896_011)),
    };
    let one = Address {
        base: "global:first".into(),
        offset: AddressOffset::Constant(8),
    };
    let two = Address {
        base: "global:second".into(),
        offset: AddressOffset::Constant(16),
    };
    let facts = PureFactContext::new()
        .assume_condition(
            ConditionTerm::pointer_equal(first.clone(), one.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::pointer_equal(second.clone(), two.clone()),
            true,
        );
    assert!(facts.equality_graph.are_equal(&first, &one));
    assert!(facts.equality_graph.are_equal(&second, &two));
    assert_eq!(
        facts
            .equality_graph
            .storage_address(&first.offset_by_bytes(4)),
        one.offset_by_bytes(4)
    );
    assert_eq!(
        facts
            .equality_graph
            .storage_address(&second.offset_by_bytes(8)),
        two.offset_by_bytes(8)
    );
}

#[test]
fn alignment_uses_the_checked_storage_anchor_through_transitive_equality() {
    let first = Address::symbolic(Variable(896_900));
    let last = Address::symbolic(Variable(896_901));
    let storage = Address {
        base: AddressBase::Heap(896_990),
        offset: AddressOffset::Constant(0),
    };
    let empty = PureFactContext::new();
    let facts = empty
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(first.clone(), storage), true)
        .assume_condition(ConditionTerm::pointer_equal(last.clone(), first), true);
    assert_eq!(
        facts.decide(&ConditionTerm::pointer_aligned(last.offset_by_bytes(8), 8)),
        Some(true)
    );
    assert_eq!(
        facts.decide(&ConditionTerm::pointer_aligned(last.offset_by_bytes(8), 16)),
        Some(false)
    );
    assert_eq!(empty.decide(&ConditionTerm::pointer_aligned(last, 8)), None);
}

#[test]
fn declared_alignment_follows_late_transitive_address_equality() {
    let base = Address::symbolic(Variable(898_100));
    let middle = Address::symbolic(Variable(898_101));
    let alias = Address::symbolic(Variable(898_102));
    let original = PureFactContext::new()
        .assume_condition(ConditionTerm::pointer_aligned(base.clone(), 8), true);
    let facts = original
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(base, middle.clone()), true)
        .assume_condition(ConditionTerm::pointer_equal(middle, alias.clone()), true);
    assert_eq!(
        facts.decide(&ConditionTerm::pointer_aligned(alias.clone(), 8)),
        Some(true)
    );
    // The single-premise formation certificate must not silently omit the
    // equalities required by this stronger ambient graph decision.
    assert!(
        facts
            .pointer_alignment_certificate_decision(&alias, 8)
            .is_none()
    );
    assert_eq!(
        original.decide(&ConditionTerm::pointer_aligned(alias, 8)),
        None
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/storage_tests.rs");
}

#[test]
fn automatic_declaration_storage_is_an_anchor_and_an_indexed_local_alias() {
    let binding = crate::kernel::LocalBindingId::new(
        crate::kernel::LocalFunctionId::new(Some("objects.c".into()), "f".into()),
        false,
        0,
        Some("x".into()),
    );
    let storage = Address {
        base: AddressBase::AutomaticLocal {
            binding,
            instance: crate::kernel::LocalStorageInstance::Frame(3),
        },
        offset: AddressOffset::Constant(0),
    };
    let alias = Address::symbolic(Variable(896_999));
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(alias.clone(), storage.clone()),
        true,
    );
    assert_eq!(facts.equality_graph.storage_address(&alias), storage);
    assert!(
        facts
            .equality_graph
            .local_slot_alias_blocks(&alias)
            .contains(&storage.base)
    );
}
