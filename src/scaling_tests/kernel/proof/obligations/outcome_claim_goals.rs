use super::*;

#[test]
fn claim_closing_updates_only_selected_entries_and_preserves_forks() {
    for count in [16_usize, 64, 256, 512] {
        let outcome = outcome();
        let original = OutcomeClaimGoals::open(
            (0..count).map(|index| (CFunctionContractClaimKey::Ensure(index), None)),
            false,
        );
        let ((closed, work), indexed_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut current = original.clone();
                // Out-of-order closing must retain the first open source position.
                for index in (0..count).rev() {
                    let key = CFunctionContractClaimKey::Ensure(index);
                    assert_eq!(current.first_open_position(), Some(0));
                    current = current.close(&key, receipt(), &outcome.identity).unwrap();
                    assert!(current.evidence(&key).is_some());
                }
                current
            })
        });
        assert!(work >= count, "entry updates must be charged");
        assert!(work <= 8 * count, "{count} claims charged {work} work");
        assert!(
            indexed_work <= 20 * count * (count.ilog2() as usize + 1),
            "{count} claims visited {indexed_work} index nodes"
        );
        assert_eq!(closed.first_open_position(), None);
        assert_eq!(original.first_open_position(), Some(0));
        assert!(
            original
                .evidence(&CFunctionContractClaimKey::Ensure(count - 1))
                .is_none()
        );
        let sibling = original
            .close(
                &CFunctionContractClaimKey::Ensure(0),
                receipt(),
                &outcome.identity,
            )
            .unwrap();
        assert_eq!(sibling.first_open_position(), Some(1));
        assert!(
            sibling
                .evidence(&CFunctionContractClaimKey::Ensure(count - 1))
                .is_none()
        );
        let (((), work), indexed_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(
                    closed
                        .evidence(&CFunctionContractClaimKey::Ensure(count - 1))
                        .is_some()
                );
                assert!(
                    closed
                        .evidence(&CFunctionContractClaimKey::Ensure(count))
                        .is_none()
                );
                assert!(
                    closed
                        .target(&CFunctionContractClaimKey::Ensure(count))
                        .is_none()
                );
            })
        });
        assert_eq!(work, 3);
        assert!(indexed_work <= 6 * (count.ilog2() as usize + 1));
    }
}
