use super::*;
use crate::kernel::{AddressBase, AddressOffset, MemoryRange, OldAddress, OldMachineTerm};

// Reading the pre-update tree is test setup, independent of how the producer
// implements its update or prepares the resulting footprint.
fn height(node: &Option<Arc<Node>>) -> usize {
    node.as_ref()
        .map_or(0, |node| 1 + height(&node.left).max(height(&node.right)))
}

fn preparation_counts() -> (usize, usize) {
    (
        FOOTPRINT_VISITS.with(|value| value.get()),
        FOOTPRINT_BUILDS.with(|value| value.get()),
    )
}

fn change(set: &CanonicalFactSet, range: &MemoryRange, insert: bool) -> CanonicalFactSet {
    let old_height = height(&set.root);
    let walks = canonical_fact_set_walks();
    let (old_visits, old_builds) = preparation_counts();
    let next = if insert {
        set.with_memory_range(range)
    } else {
        set.without_memory_range(range)
    };
    let (visits, builds) = preparation_counts();
    let (visits, builds) = (visits - old_visits, builds - old_builds);
    // Split and the boundary-spine merges rebuild at most three old-tree
    // heights plus the replacement leaf. Cached old subtrees require one
    // visit, without preparation of their descendants.
    assert!(
        builds <= 3 * (old_height + 1),
        "height={old_height}, builds={builds}"
    );
    assert!(
        visits > 0 && visits <= 6 * (old_height + 1) + 1,
        "height={old_height}, visits={visits}"
    );
    assert_eq!(
        canonical_fact_set_walks(),
        walks,
        "a delta enumerated held facts"
    );
    next
}

fn assert_footprint(set: &CanonicalFactSet, expected: &[MemoryRange]) {
    let mut pending = vec![set.footprint()];
    let mut actual = Vec::new();
    while let Some(resource) = pending.pop() {
        match resource {
            crate::kernel::Resource::Emp => {}
            crate::kernel::Resource::Memory(range) => actual.push(range),
            crate::kernel::Resource::Star(children) => {
                let (left, right) = &**children;
                pending.extend([left.clone(), right.clone()]);
            }
            resource => panic!("unexpected footprint resource: {resource:?}"),
        }
    }
    let mut expected = expected.to_vec();
    actual.sort();
    expected.sort();
    assert_eq!(actual, expected);
}

#[test]
fn partial_borrow_footprints_prepare_only_changed_tree_paths() {
    for size in [16usize, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let owners = (0..size)
            .map(|index| {
                MemoryRange::new(
                    OldAddress {
                        base: AddressBase::ExternalArgument,
                        offset: AddressOffset::scaled_int32_node(
                            OldMachineTerm::Variable(Variable(1_967_000 + index as u64)),
                            4,
                        ),
                    },
                    OldMachineTerm::constant(0),
                    OldMachineTerm::constant(4),
                )
            })
            .collect::<Vec<_>>();
        let mut original = CanonicalFactSet::default();
        for owner in &owners {
            original = original.with_memory_range(owner);
        }
        // Different selected positions exercise different actual priorities
        // and removal merge spines without pinning a preferred tree shape.
        for selected in [0, size / 2, size - 1] {
            let whole = &owners[selected];
            let left = MemoryRange::new(
                whole.base.clone(),
                OldMachineTerm::constant(0),
                OldMachineTerm::constant(2),
            );
            let right = MemoryRange::new(
                whole.base.clone(),
                OldMachineTerm::constant(2),
                OldMachineTerm::constant(4),
            );
            let mut remainder = owners.clone();
            remainder.remove(selected);
            let mut split_ranges = remainder.clone();
            split_ranges.extend([left.clone(), right.clone()]);
            let mut borrowed_ranges = remainder;
            borrowed_ranges.push(right.clone());
            let mut split = change(&original, whole, false);
            split = change(&split, &left, true);
            split = change(&split, &right, true);
            assert_footprint(&split, &split_ranges);
            let borrowed = change(&split, &left, false);
            assert_footprint(&borrowed, &borrowed_ranges);
            let returned = change(&borrowed, &left, true);
            assert!(returned.same_contents(&split));
            assert!(returned.shares_root_with(&split));
            assert_footprint(&returned, &split_ranges);
            let mut restored = change(&returned, &left, false);
            restored = change(&restored, &right, false);
            restored = change(&restored, whole, true);
            assert!(restored.same_contents(&original));
            assert!(restored.shares_root_with(&original));
            assert_eq!(restored.footprint(), original.footprint());
            assert_footprint(&restored, &owners);
        }
    }
}
