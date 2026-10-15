use super::*;

fn range(block: &str) -> CMemoryRange {
    CMemoryRange::new_with_element_width(
        Pointer {
            block: PointerBlock::Concrete(block.to_string()),
            offset: PointerOffsetTerm::Constant(0),
        },
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
        4,
    )
}

fn view(block: &str) -> CResourceFact {
    CResourceFact::View(CResource::Memory(range(block)))
}

fn own(block: &str) -> CResourceFact {
    CResourceFact::own(CResource::Memory(range(block)))
}

fn token(quantity: u32) -> CResourceFact {
    CResourceFact::Own(
        CResource::Token {
            name: "ticket".to_string(),
            arguments: Vec::new().into(),
        },
        Box::new(Bitvector32Term::Constant(quantity)),
    )
}

fn context(facts: impl IntoIterator<Item = CResourceFact>) -> ResourceContext {
    ResourceContext::new().unchecked_with_facts(facts)
}

/// A view held twice is the view held once, and nothing else about two
/// exits' resources is looked through: a permission one exit lacks, a
/// view against ownership, another range, and another owned quantity
/// each keep the exits apart.
#[test]
fn exits_agree_on_resources_only_up_to_a_view_held_twice() {
    let assumptions = PureFactContext::new();
    let agree = |left: &ResourceContext, right: &ResourceContext| {
        loop_exit_resources_agree(left, right, &assumptions)
            && loop_exit_resources_agree(right, left, &assumptions)
    };
    let once = context([view("a"), own("b")]);
    let twice = context([view("a"), view("a"), own("b")]);
    assert!(once != twice);
    assert!(agree(&once, &twice));

    // A permission only one exit holds.
    assert!(!agree(&once, &context([own("b")])));
    // A view where the other exit owns.
    assert!(!agree(&once, &context([own("a"), own("b")])));
    // The same shape over another range.
    assert!(!agree(&once, &context([view("c"), own("b")])));
    // Ownership only one exit holds.
    assert!(!agree(&once, &context([view("a")])));
    // Different owned quantities of one resource.
    assert!(!agree(&context([token(1)]), &context([token(2)])));
    assert!(!agree(&context([token(1)]), &context([token(1), token(1)])));
}

#[test]
fn exits_agree_on_a_memory_owner_with_its_own_observation_cache() {
    let owner = own("a");
    let plain = context([owner.clone()]);
    let expanded = plain
        .clone()
        .with_cached_supported_expansion(&owner, vec![owner.clone()]);
    let observed = expanded
        .clone()
        .unchecked_with_supported_facts(&owner, vec![view("a")]);
    let assumptions = PureFactContext::new();
    for derived in [expanded, observed] {
        assert_ne!(derived, plain);
        assert!(loop_exit_resources_agree(&derived, &plain, &assumptions));
        assert!(loop_exit_resources_agree(&plain, &derived, &assumptions));
    }
    let nontrivial = plain
        .clone()
        .with_cached_supported_expansion(&owner, vec![own("b")]);
    assert!(!loop_exit_resources_agree(
        &nontrivial,
        &plain,
        &assumptions
    ));
    let other_view = plain
        .clone()
        .unchecked_with_supported_facts(&owner, vec![view("b")]);
    assert!(!loop_exit_resources_agree(
        &other_view,
        &plain,
        &assumptions
    ));
}
